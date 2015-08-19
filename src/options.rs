use std::ffi::{CString, CStr};
use std::cmp::Ordering;
use std::mem;
use std::slice;
use std::path::Path;
use std::marker::PhantomData;
use std::convert::From;

use libc::{c_uchar, c_char, c_int, c_uint, c_double, c_void, uint64_t, uint32_t, size_t};

use super::{Db,Result};
use super::ffi;

/// Options for constructing or accessing a RocksDB instance.
///
/// `Options` follows the builder pattern, whereby one can either construct and open a db in a
/// single line, or for more complex cases, build up options with arbitrarily complex logic before
/// opening the db.
///
/// For example, a simple one-liner:
///
/// ```no_run
/// # use myrocksdb::Options;
/// # use std::path::Path;
/// let db = Options::new()
///             .error_if_exists(true)
///             .open(Path::new("foo"));
/// ```
///
/// Or alternatively: over multiple lines:
///
/// ```no_run
/// # use myrocksdb::{Options,Compression};
/// # use myrocksdb::Db;
/// # use std::path::Path;
/// let mut opts = Options::new();
/// opts.error_if_exists(true);
/// opts.compression(Compression::LZ4);
/// let db = Db::open(&opts, Path::new("foo"));
/// ```

#[allow(raw_pointer_derive)]
#[derive(Debug)]
pub struct Options {
    options: *mut ffi::rocksdb_options_t,
}

impl Drop for Options {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_options_destroy(self.options) }
    }
}

pub struct CompactionFilter<'a, F>
    where F: Filter<'a>
{
    filter: *mut ffi::rocksdb_compactionfilter_t,
    ty: PhantomData<(F,&'a ())>
}

/// Create a compaction filter. A single filter created this way may be called from multiple
/// threads, and must therefore be thread safe.
impl<'a, F> CompactionFilter<'a, F>
    where F: Filter<'a>
{
    pub fn new(filt: F) -> CompactionFilter<'a, F>
        where F: Sync + Send
    {
        Self::make(filt)
    }

    fn make(filt: F) -> CompactionFilter<'a, F> {
        CompactionFilter {
            filter: unsafe {
                ffi::rocksdb_compactionfilter_create(Box::into_raw(Box::new(filt)) as *mut c_void,
                                                     Some(compaction_drop_cb::<F>),
                                                     Some(compaction_filter_cb::<F>),
                                                     Some(compaction_name_cb::<F>))
            },
            ty: PhantomData
        }
    }

    /// Consume self and return the raw pointer
    fn into_ptr(self) -> *mut ffi::rocksdb_compactionfilter_t {
        let ret = self.filter;
        mem::forget(self);            
        ret
    }
}

impl<'a, F> Drop for CompactionFilter<'a, F>
    where F: Filter<'a>
{
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_compactionfilter_destroy(self.filter); }
    }
}

pub enum FilterRes<V: AsRef<[u8]>> {
    Remove,
    Preserve,
    Change(V),
}

pub trait Filter<'a> {
    type Key: From<&'a [u8]>;
    type Val: From<&'a [u8]> + AsRef<[u8]>;

    /// Return the name of the filter
    fn name(&self) -> &CStr;

    /// The actual filter itself
    fn filter(&self, level: u32, key: &Self::Key, val: &Self::Val) -> FilterRes<Self::Val>;

    /// Stash the value in a per-thread storage which will be live until the next call to the filter
    /// function. Hacky consequence of the C compaction filter binding.
    fn stash(&self, val: Self::Val) -> &Self::Val;
}

extern fn compaction_filter_cb<'a, F>(ptr: *mut c_void, level: c_int,
                                      key: *const c_char, keylen: size_t,
                                      existing: *const c_char, vallen: size_t,
                                      newval: *mut *mut c_char, newlen: *mut size_t,
                                      val_changed: *mut c_uchar) -> c_uchar
    where F: Filter<'a>
{
    let ptr = ptr as *const Box<F>;

    unsafe {
        let ptr = &*ptr;
        let key = F::Key::from(slice::from_raw_parts(key as *const u8, keylen as usize));
        let val = F::Val::from(slice::from_raw_parts(existing as *const u8, vallen as usize));

        match ptr.filter(level as u32, &key, &val) {
            FilterRes::Remove => 1,
            FilterRes::Preserve => {
                *val_changed = 0;
                0
            },
            FilterRes::Change(v) => {
                let v = ptr.stash(v); // keep v alive till next call
                let s = v.as_ref();
                let p = s.as_ptr();
                let l = s.len();
                
                *val_changed = 1;
                *newval = p as *mut c_char;
                *newlen = l as size_t;
                0
            },
        }
    }
}

extern fn compaction_drop_cb<'a, F>(ptr: *mut c_void)
    where F: Filter<'a>
{
    let ptr = ptr as *mut F;
    unsafe {
        let _ = Box::from_raw(ptr); // drops
    }
}

extern fn compaction_name_cb<'a, F>(ptr: *mut c_void) -> *const c_char
    where F: Filter<'a>
{
    let ptr = ptr as *const Box<F>;

    let s = unsafe { (&*ptr).name() };
    s.as_ptr()
}

extern fn compactionfilterfactory_drop_cb<'a, FF, F>(ptr: *mut c_void)
    where FF: FilterFactory<'a, F>, F: Filter<'a>
{
    let ptr = ptr as *mut F;
    unsafe {
        let _ = Box::from_raw(ptr); // drops
    }    
}

extern fn compactionfilterfactory_name_cb<'a, FF, F>(ptr: *mut c_void) -> *const c_char
    where FF: FilterFactory<'a, F>, F: Filter<'a>
{
    let ptr = ptr as *const Box<FF>;

    let s = unsafe { (&*ptr).name() };
    s.as_ptr()
}

extern fn compactionfilterfactory_createfilter_cb<'a, FF, F>(ptr: *mut c_void, context: *mut ffi::rocksdb_compactionfiltercontext_t) -> *mut ffi::rocksdb_compactionfilter_t
    where FF: FilterFactory<'a, F>, F: Filter<'a>
{
    let ptr = ptr as *mut FF;
    let ptr = unsafe { &mut *ptr };
    let cctx = CompactionFilterContext(&context);

    let filt = ptr.createfilter(&cctx);

    CompactionFilter::make(filt).into_ptr()
}

pub struct CompactionFilterContext<'a>(&'a *mut ffi::rocksdb_compactionfiltercontext_t);

impl<'a> CompactionFilterContext<'a> {
    pub fn is_full_compaction(&self) -> bool {
        unsafe { ffi::rocksdb_compactionfiltercontext_is_full_compaction(*self.0) != 0 }
    }

    pub fn is_manual_compaction(&self) -> bool {
        unsafe { ffi::rocksdb_compactionfiltercontext_is_manual_compaction(*self.0) != 0 }
    }
}

/// A factory for compaction `Filter`s.
pub trait FilterFactory<'a, F>
    where F: Filter<'a>
{
    fn createfilter(&mut self, ctx: &CompactionFilterContext) -> F;
    fn name(&self) -> &CStr;    
}

pub trait Comparator<'a> {
    type Key: From<&'a [u8]>;
    
    fn name(&self) -> &CStr;
    fn compare(&self, a: &Self::Key, b: &Self::Key) -> Ordering;
}

extern fn comparator_drop_cb<'a, C>(ptr: *mut c_void)
    where C: Comparator<'a>
{
    let ptr = ptr as *mut C;
    unsafe {
        let _ = Box::from_raw(ptr); // drops
    }
}

extern fn comparator_name_cb<'a, C>(ptr: *mut c_void) -> *const c_char
    where C: Comparator<'a>
{
    let ptr = ptr as *const Box<C>;

    let s = unsafe { (&*ptr).name() };
    s.as_ptr()
}

extern fn comparator_compare_cb<'a, C>(ptr: *mut c_void,
                                       aptr: *const c_char, alen: size_t,
                                       bptr: *const c_char, blen: size_t) -> c_int
    where C: Comparator<'a>
{
    let ptr = ptr as *const Box<C>;

    unsafe {
        let ptr = &*ptr;
        let a = C::Key::from(slice::from_raw_parts(aptr as *const u8, alen as usize));
        let b = C::Key::from(slice::from_raw_parts(bptr as *const u8, blen as usize));

        match ptr.compare(&a, &b) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }
}

pub struct DefaultCompare<'a, K>(CString, PhantomData<(&'a K)>)
    where K: From<&'a [u8]> + Ord + 'a;

impl<'a, T> DefaultCompare<'a, T>
    where T: From<&'a [u8]> + Ord + 'a
{
    pub fn new() -> DefaultCompare<'a, T> { DefaultCompare(CString::new("default").unwrap(), PhantomData) }
}

impl<'a, T> Comparator<'a> for DefaultCompare<'a, T>
    where T: From<&'a [u8]> + Ord + 'a
{
    type Key = T;

    fn name<'b>(&'b self) -> &'b CStr { &self.0 }
    fn compare(&self, a: &T, b: &T) -> Ordering { a.cmp(b) }
}

// TBD
pub struct MergeOperator {
    mergeoperator: *mut ffi::rocksdb_mergeoperator_t,
}

impl Drop for MergeOperator {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_mergeoperator_destroy(self.mergeoperator); }        
    }
}

// TBD
pub struct SliceTransform {
    slicetransform: *mut ffi::rocksdb_slicetransform_t,
}

impl Drop for SliceTransform {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_slicetransform_destroy(self.slicetransform); }
    }
}

#[repr(u32)]
pub enum CompactionStyle {
    Level = ffi::rocksdb_level_compaction,
    Universal = ffi::rocksdb_universal_compaction,
    Fifo = ffi::rocksdb_fifo_compaction,
}

pub struct UniversalCompactionOptions {
    options: *mut ffi::rocksdb_universal_compaction_options_t,
}

pub struct FifoCompactionOptions {
    options: *mut ffi::rocksdb_fifo_compaction_options_t,
}


pub enum AccessHint {
    None = 0,
    Normal = 1,
    Sequential = 2,
    Willneed = 3,
}

#[repr(u32)]
pub enum Compression {
    None = ffi::rocksdb_no_compression,
    Snappy = ffi::rocksdb_snappy_compression,
    Zlib = ffi::rocksdb_zlib_compression,
    BZip2 = ffi::rocksdb_bz2_compression,
    LZ4 = ffi::rocksdb_lz4_compression,
    LZ4H= ffi::rocksdb_lz4hc_compression,
}

#[repr(u32)]
/// The index type that will be used for this table.
pub enum IndexType {
    /// A space efficient index block that is optimized for
    /// binary-search-based index.
    BinarySearch = ffi::rocksdb_block_based_table_index_type_binary_search,
    /// The hash index, if enabled, will do the hash lookup when
    /// `Options.prefix_extractor` is provided.
    HashSearch = ffi::rocksdb_block_based_table_index_type_hash_search,
}

impl Options {
    /// Construct a new default set of options
    pub fn new() -> Options {
        Options {
            options: unsafe { ffi::rocksdb_options_create() }
        }
    }

    /// Create a new `Db` instance with the current set of options
    pub fn open<P: AsRef<Path>>(&self, name: P) -> Result<Db> { Db::open(self, name) }

    /// Create a new read-only `Db` instance with the current set of options
    pub fn open_for_read_only<P: AsRef<Path>>(&self, name: P, error_if_log_exists: bool) -> Result<Db> {
        Db::open_for_read_only(self, name, error_if_log_exists)
    }

    /// Set the "create if missing flag". The Db will be created if missing.
    pub fn create_if_missing(&mut self, create: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_create_if_missing(self.options, create as c_uchar) };
        self
    }

    /// Set the "error if exists" flag. The open will fail if the db already exists.
    pub fn error_if_exists(&mut self, excl: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_error_if_exists(self.options, excl as c_uchar) };
        self
    }

    /// Increase the parallelism by setting the number of threads.
    ///
    /// By default, RocksDB uses only one background thread for flush and
    /// compaction. Calling this function will set it up such that total of
    /// `total_threads` is used. Good value for `total_threads` is the number of
    /// cores. You almost definitely want to call this function if your system is
    /// bottlenecked by RocksDB.
    pub fn increase_parallelism(&mut self, total_threads: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_increase_parallelism(self.options, total_threads as c_int) };
        self
    }
    
    /// Use this if you don't need to keep the data sorted, i.e. you'll never use
    /// an iterator, only Put() and Get() API calls
    pub fn optimize_for_point_lookup(&mut self, block_cache_size_mb: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_optimize_for_point_lookup(self.options, block_cache_size_mb) };
        self
    }

    /// Default values for some parameters in ColumnFamilyOptions are not optimized for heavy
    /// workloads and big datasets, which means you might observe write stalls under some
    /// conditions. As a starting point for tuning RocksDB options, use the following two functions:
    ///
    /// * OptimizeLevelStyleCompaction -- optimizes level style compaction
    /// * OptimizeUniversalStyleCompaction -- optimizes universal style compaction
    ///
    /// Universal style compaction is focused on reducing Write Amplification Factor for big data
    /// sets, but increases Space Amplification. You can learn more about the different styles
    /// [here](https:///github.com/facebook/rocksdb/wiki/Rocksdb-Architecture-Guide). Make sure to
    /// also call `increase_parallelism()`, which will provide the biggest performance gains.
    ///
    /// Note: we might use more memory than memtable_memory_budget during high write rate period
    pub fn compaction_style(&mut self, compactionstyle: CompactionStyle) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_compaction_style(self.options, compactionstyle as c_int) }
        self
    }

    pub fn optimize_level_style_compaction(&mut self, memtable_memory_budget: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_optimize_level_style_compaction(self.options, memtable_memory_budget) };
        self
    }

    pub fn optimize_universal_style_compaction(&mut self, memtable_memory_budget: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_optimize_universal_style_compaction(self.options, memtable_memory_budget) };
        self
    }

    /// A single CompactionFilter instance to call into during compaction.  Allows an application to
    /// modify/delete a key-value during background compaction.
    ///
    /// If the client requires a new compaction filter to be used for different compaction runs, it
    /// can specify `compaction_filter_factory` instead of this option.  The client should specify
    /// only one of the two.  compaction_filter takes precedence over compaction_filter_factory if
    /// client specifies both.
    ///
    /// If multithreaded compaction is being used, the supplied `Filter` instance may be
    /// used from different threads concurrently and so should be thread-safe.
    pub fn compaction_filter<'a, F>(&mut self, filter: F) -> &mut Options
        where F: Filter<'a>
    {
        unsafe {
            let cf =
                ffi::rocksdb_compactionfilter_create(Box::into_raw(Box::new(filter)) as *mut c_void,
                                                     Some(compaction_drop_cb::<F>),
                                                     Some(compaction_filter_cb::<F>),
                                                     Some(compaction_name_cb::<F>));
            // Takes ownership
            ffi::rocksdb_options_set_compaction_filter(self.options, cf);
        };
        self
    }

    /// This is a factory that provides compaction filter objects which allow an application to
    /// modify/delete a key-value during background compaction.
    ///
    /// A new filter will be created on each compaction run.  If multithreaded compaction is being
    /// used, each created CompactionFilter will only be used from a single thread and so does not
    /// need to be thread-safe.
    ///
    /// (TBD: At present `Filter` must always present a thread-safe interface. In future a MutFilter
    /// interface will exist to allow direct mutation in a single-threaded context.)
    pub fn compaction_filter_factory<'a, FF, F>(&mut self, factory: FF) -> &mut Options
        where FF: FilterFactory<'a, F>, F: Filter<'a>
    {
        unsafe {
            let ff =
                ffi::rocksdb_compactionfilterfactory_create(Box::into_raw(Box::new(factory)) as *mut c_void,
                                                            Some(compactionfilterfactory_drop_cb::<FF, F>),
                                                            Some(compactionfilterfactory_createfilter_cb::<FF, F>),
                                                            Some(compactionfilterfactory_name_cb::<FF, F>));
            // shared ptr
            ffi::rocksdb_options_set_compaction_filter_factory(self.options, ff);

            // Release local reference
            ffi::rocksdb_compactionfilterfactory_destroy(ff);
        };
        self
    }

    /// Comparator used to define the order of keys in the table.  Default: a comparator that uses
    /// lexicographic byte-wise ordering
    ///
    /// REQUIRES: The client must ensure that the comparator supplied here has the same name and
    /// orders keys *exactly* the same as the comparator provided to previous open calls on the same
    /// DB.
    pub fn comparator<'a, C>(&mut self, cmp: C) -> &mut Options
        where C: Comparator<'a>
    {
        unsafe {
            let cmp = ffi::rocksdb_comparator_create(Box::into_raw(Box::new(cmp)) as *mut c_void,
                                                     Some(comparator_drop_cb::<C>),
                                                     Some(comparator_compare_cb::<C>),
                                                     Some(comparator_name_cb::<C>));

            // takes ownership
            ffi::rocksdb_options_set_comparator(self.options, cmp);
        };
        self
    }

    pub fn merge_operator(&mut self, merge: MergeOperator) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_merge_operator(self.options, merge.mergeoperator) };
        self
    }

    pub fn paranoid_checks(&mut self, checks: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_paranoid_checks(self.options, checks as c_uchar) };
        self
    }

    // rocksdb_options_set_info_log - ues Log crate?

    pub fn info_log_level(&mut self, level: i32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_info_log_level(self.options, level as c_int) };
        self
    }

    pub fn write_buffer_size(&mut self, size: usize) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_write_buffer_size(self.options, size as size_t) };
        self
    }

    pub fn max_open_files(&mut self, nopen: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_open_files(self.options, nopen as c_int) };
        self
    }

    pub fn max_total_wal_size(&mut self, max: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_total_wal_size(self.options, max as uint64_t) };
        self
    }

    pub fn compression(&mut self, compression: Compression) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_compression(self.options, compression as c_int) };
        self
    }
    
    pub fn compression_options(&mut self, wbits: i32, level: i32, strat: i32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_compression_options(self.options, wbits, level, strat) };
        self
    }

    pub fn prefix_extractor(&mut self, slice: SliceTransform) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_prefix_extractor(self.options, slice.slicetransform) };
        self
    }

    pub fn num_levels(&mut self, levels: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_num_levels(self.options, levels as c_int) };
        self
    }

    pub fn level0_file_num_compaction_trigger(&mut self, files: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_level0_file_num_compaction_trigger(self.options, files as c_int) };
        self
    }

    pub fn level0_slowdown_writes_trigger(&mut self, files: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_level0_slowdown_writes_trigger(self.options, files as c_int) };
        self
    }

    pub fn level0_stop_writes_trigger(&mut self, files: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_level0_stop_writes_trigger(self.options, files as c_int) };
        self
    }

    pub fn target_file_size_base(&mut self, size: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_target_file_size_base(self.options, size as uint64_t) };
        self
    }

    pub fn target_file_size_multiplier(&mut self, mult: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_target_file_size_multiplier(self.options, mult as c_int) };
        self
    }

    pub fn max_bytes_for_level_base(&mut self, size: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_bytes_for_level_base(self.options, size as uint64_t) };
        self
    }

    pub fn max_bytes_for_level_multiplier(&mut self, mult: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_bytes_for_level_multiplier(self.options, mult as c_int) };
        self
    }

    pub fn expanded_compaction_factor(&mut self, mult: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_expanded_compaction_factor(self.options, mult as c_int) };
        self
    }

    pub fn max_grandparent_overlap_factor(&mut self, mult: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_grandparent_overlap_factor(self.options, mult as c_int) };
        self
    }

    pub fn max_bytes_for_level_multiplier_additional(&mut self, mult: Vec<u32>) -> &mut Options {
        let mut cmult : Vec<_> = mult.into_iter().map(|m| m as c_int).collect();
        unsafe { ffi::rocksdb_options_set_max_bytes_for_level_multiplier_additional(self.options, cmult.as_mut_ptr(), cmult.len() as size_t) };
        self
    }

    pub fn enable_statistics(&mut self) -> &mut Options {
        unsafe { ffi::rocksdb_options_enable_statistics(self.options) };
        self
    }

    // XXX statistics_get_string?

    pub fn max_write_buffer_number(&mut self, num: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_write_buffer_number(self.options, num as c_int) };
        self
    }

    pub fn min_write_buffer_number_to_merge(&mut self, num: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_min_write_buffer_number_to_merge(self.options, num as c_int) };
        self
    }

    pub fn max_write_buffer_number_to_maintain(&mut self, num: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_write_buffer_number_to_maintain(self.options, num as c_int) };
        self
    }

    pub fn max_background_compactions(&mut self, num: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_background_compactions(self.options, num as c_int) };
        self
    }

    pub fn max_background_flushed(&mut self, num: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_background_flushes(self.options, num as c_int) };
        self
    }

    pub fn max_log_file_size(&mut self, sz: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_log_file_size(self.options, sz as size_t) };
        self
    }

    pub fn log_file_time_to_roll(&mut self, sz: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_log_file_time_to_roll(self.options, sz as size_t) };
        self
    }

    pub fn keep_log_file_num(&mut self, sz: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_keep_log_file_num(self.options, sz as size_t) };
        self
    }

    pub fn soft_rate_limit(&mut self, lim: f64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_soft_rate_limit(self.options, lim as c_double) };
        self
    }

    // obsolete pub fn hard_rate_limit(&mut self, lim: f64) -> &mut Options;
    // obsolete pub fn rate_limit_delay_max_milliseconds(&mut self, max: u32) -> &mut Options;

    pub fn max_manifest_file_size(&mut self, max: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_manifest_file_size(self.options, max as size_t) };
        self
    }

    pub fn table_cache_numshardbits(&mut self, num: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_table_cache_numshardbits(self.options, num as c_int) };
        self
    }

    // obsolete pub fn table_cache_remove_scan_count_limit(&mut self, num: u32) -> &mut Options;

    pub fn arena_block_size(&mut self, sz: usize) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_arena_block_size(self.options, sz as size_t) };
        self
    }

    pub fn use_fsync(&mut self, fsync: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_use_fsync(self.options, fsync as c_int) };
        self
    }

    pub fn db_log_dir<P: AsRef<Path>>(&mut self, dir: P) -> &mut Options {
        if let Some(cdir) = dir.as_ref().as_os_str().to_cstring() {
            unsafe { ffi::rocksdb_options_set_db_log_dir(self.options, cdir.as_ptr()) }
        };
        self
    }

    pub fn wal_dir<P: AsRef<Path>>(&mut self, dir: P) -> &mut Options {
        if let Some(cdir) = dir.as_ref().as_os_str().to_cstring() {
            unsafe { ffi::rocksdb_options_set_wal_dir(self.options, cdir.as_ptr()) }
        };
        self
    }

    pub fn wal_ttl_seconds(&mut self, sec: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_WAL_ttl_seconds(self.options, sec as uint64_t) }
        self
    }

    pub fn wal_size_limit_mb(&mut self, sz: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_WAL_size_limit_MB(self.options, sz as uint64_t) }
        self
    }

    pub fn manifest_preallocation_size(&mut self, sz: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_manifest_preallocation_size(self.options, sz as uint64_t) }
        self
    }

    // obsolete pub fn purge_redundant_kvs_while_flush(&mut self, purge: bool) -> &mut Options;

    pub fn allow_os_buffer(&mut self, purge: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_allow_os_buffer(self.options, purge as c_uchar) }
        self
    }

    pub fn allow_mmap_reads(&mut self, mmap: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_allow_mmap_reads(self.options, mmap as c_uchar) }
        self
    }

    pub fn allow_mmap_writes(&mut self, mmap: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_allow_mmap_writes(self.options, mmap as c_uchar) }
        self
    }

    pub fn is_fd_close_on_exec(&mut self, clx: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_is_fd_close_on_exec(self.options, clx as c_uchar) }
        self
    }

    // obsolete pub fn skip_log_error_on_recovery(&mut self, skip: bool) -> &mut Options;

    pub fn stats_dump_period_sec(&mut self, sec: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_stats_dump_period_sec(self.options, sec as c_uint) }
        self
    }

    // obsolete pub fn block_size_deviation(&mut self, dev: u32) -> &mut Options;

    pub fn advise_random_on_open(&mut self, random: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_advise_random_on_open(self.options, random as c_uchar) }
        self
    }

    pub fn access_hint_on_compaction_start(&mut self, hint: AccessHint) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_access_hint_on_compaction_start(self.options, hint as c_int) }
        self
    }

    pub fn use_adaptive_mutex(&mut self, yes: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_use_adaptive_mutex(self.options, yes as c_uchar) }
        self
    }

    pub fn bytes_per_sync(&mut self, num: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_bytes_per_sync(self.options, num as uint64_t) }
        self
    }

    pub fn verify_checksums_in_compaction(&mut self, yes: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_verify_checksums_in_compaction(self.options, yes as c_uchar) }
        self
    }

    pub fn filter_deletes(&mut self, yes: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_filter_deletes(self.options, yes as c_uchar) }
        self
    }

    pub fn max_sequential_skip_in_iterations(&mut self, num: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_sequential_skip_in_iterations(self.options, num as uint64_t) };
        self
    }

    pub fn disable_data_sync(&mut self, yes: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_disable_data_sync(self.options, yes as c_int) }
        self
    }

    pub fn disable_auto_compactions(&mut self, yes: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_disable_auto_compactions(self.options, yes as c_int) }
        self
    }

    pub fn delete_obsolete_files_period_micros(&mut self, us: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_delete_obsolete_files_period_micros(self.options, us as uint64_t) }
        self
    }

    pub fn source_compaction_factor(&mut self, n: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_source_compaction_factor(self.options, n as c_int) }
        self
    }

    pub fn prepare_for_bulk_load(&mut self) -> &mut Options {
        unsafe { ffi::rocksdb_options_prepare_for_bulk_load(self.options) }
        self
    }

    pub fn memtable_vector_rep(&mut self) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_memtable_vector_rep(self.options) }
        self
    }

    pub fn hash_skip_list_rep(&mut self, bucket_count: usize, skiplist_height: u32, skiplist_branching_factor: u32) -> &mut Options {
        unsafe {
            ffi::rocksdb_options_set_hash_skip_list_rep(self.options,
                                                        bucket_count as size_t,
                                                        skiplist_height as c_int,
                                                        skiplist_branching_factor as c_int)
        }
        self
    }

    pub fn hash_link_list_rep(&mut self, bucket_count: usize) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_hash_link_list_rep(self.options, bucket_count as size_t) }
        self
    }

    pub fn plain_table_factory(&mut self, user_key_len: u32, bloom_bits_per_key: u32,
                               hash_table_ratio: f64, index_sparseness: usize) -> &mut Options {
        unsafe {
            ffi::rocksdb_options_set_plain_table_factory(self.options, user_key_len as uint32_t,
                                                         bloom_bits_per_key as c_int,
                                                         hash_table_ratio as c_double,
                                                         index_sparseness as size_t)
        }
        self
    }

    pub fn min_level_to_compress(&mut self, lvl: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_min_level_to_compress(self.options, lvl as c_int) }
        self
    }

    pub fn memtable_prefix_bloom_bits(&mut self, bits: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_memtable_prefix_bloom_bits(self.options, bits as uint32_t) }
        self
    }

    pub fn memtable_prefix_bloom_probes(&mut self, probes: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_memtable_prefix_bloom_probes(self.options, probes as uint32_t) }
        self
    }

    pub fn max_successive_merges(&mut self, merges: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_max_successive_merges(self.options, merges as size_t) }
        self
    }

    pub fn min_partial_merge_operands(&mut self, merges: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_min_partial_merge_operands(self.options, merges as uint32_t) }
        self
    }

    pub fn bloom_localty(&mut self, loc: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_bloom_locality(self.options, loc as uint32_t) }
        self
    }

    pub fn inplace_update_support(&mut self, yes: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_inplace_update_support(self.options, yes as c_uchar) }
        self
    }

    pub fn inplace_update_num_locks(&mut self, num: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_inplace_update_num_locks(self.options, num as size_t) }
        self
    }

    pub fn block_based_table_factory(&mut self, bboptions: &BlockBasedTableOptions) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_block_based_table_factory(self.options, bboptions.options) }
        self
    }

    pub fn universal_compaction_options(&mut self, options: &UniversalCompactionOptions) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_universal_compaction_options(self.options, options.options) }
        self
    }

    pub fn fifo_compaction_options(&mut self, options: &FifoCompactionOptions) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_fifo_compaction_options(self.options, options.options) }
        self
    }
}

// Function public to modules within the crate, not exported
pub fn get_options_ptr(opts: &Options) -> *mut ffi::rocksdb_options_t {
    opts.options
}

struct FilterPolicy {
    filter: *mut ffi::rocksdb_filterpolicy_t,
}

impl FilterPolicy {
    pub fn bloom(bits_per_key: u32) -> FilterPolicy {
        FilterPolicy {
            filter: unsafe { ffi::rocksdb_filterpolicy_create_bloom(bits_per_key as c_int) },
        }
    }
}

impl Drop for FilterPolicy {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_filterpolicy_destroy(self.filter) };
    }
}

pub struct Cache {
    cache: *mut ffi::rocksdb_cache_t,
}

impl Cache {
    /// Construct an LRU cache with `capacity` bytes.
    pub fn lru(capacity: usize) -> Cache {
        Cache {
            cache: unsafe { ffi::rocksdb_cache_create_lru(capacity as size_t) }
        }
    }
}

impl Drop for Cache {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_cache_destroy(self.cache) }
    }
}

/// Version used for new tables.
/// This option only affects newly written tables. When reading exising tables,
/// the information about version is read from the footer.
#[allow(non_camel_case_types)]
pub enum TableVersion {
    /// This version is currently written out by all RocksDB's versions by
    /// default.  Can be read by really old RocksDB's. Doesn't support changing
    /// checksum (default is CRC32).
    Ver0 = 0,
    /// Can be read by RocksDB's versions since 3.0. Supports non-default
    /// checksum, like xxHash. It is written by RocksDB when
    /// BlockBasedTableOptions::checksum is something other than kCRC32c. (version
    /// 0 is silently upconverted)
    Ver3_0 = 1,
    ///Can be read by RocksDB's versions since 3.10. Changes the way we
    /// encode compressed blocks with LZ4, BZip2 and Zlib compression. If you
    /// don't plan to run RocksDB before version 3.10, you should probably use
    // this.
    Ver3_10 = 2,
}

#[allow(non_camel_case_types)]
pub enum ChecksumType {
    NoChecksum = 0,
    CRC32c = 1,
    xxHash = 2,
}

/// Configuration options for block-based tables.
///
/// Example:
///
/// ```no_run
/// # use myrocksdb::{Options,BlockBasedTableOptions};
/// # use std::path::Path;
/// let mut opts = Options::new();
///
/// BlockBasedTableOptions::new()
///               .block_size(4096)
///               .bloom_filter(12)
///               .set(&mut opts);
///
/// let db = opts.open(Path::new("foo"));
/// # let _ = db;
pub struct BlockBasedTableOptions {
    options: *mut ffi::rocksdb_block_based_table_options_t,
}

impl BlockBasedTableOptions {
    /// Construct a new default set of table options.
    pub fn new() -> BlockBasedTableOptions {
        BlockBasedTableOptions {
            options: unsafe { ffi::rocksdb_block_based_options_create() }
        }
    }

    /// Initialize a block-based table factory in `Options`.
    pub fn set<'a>(&self, opts: &'a mut Options) -> &'a mut Options {
        opts.block_based_table_factory(self);
        opts
    }
    
    /// Approximate size of user data packed per block.
    ///
    /// Note that the block size specified here corresponds to uncompressed data.  The actual size
    /// of the unit read from disk may be smaller if compression is enabled.  This parameter can be
    /// changed dynamically.
    pub fn block_size(&mut self, sz: u64) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_size(self.options, sz as size_t) }
        self
    }

    // This is used to close a block before it reaches the configured `block_size`. If the
    // percentage of free space in the current block is less than this specified number and adding a
    // new record to the block will exceed the configured block size, then this block will be closed
    // and the new record will be written to the next block.
    pub fn block_size_deviation(&mut self, sz: u32) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_size_deviation(self.options, sz as c_int) }
        self
    }

    /// Number of keys between restart points for delta encoding of keys.  This parameter can be
    /// changed dynamically.  Most clients should leave this parameter alone.
    pub fn block_restart_interval(&mut self, interval: u32) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_restart_interval(self.options, interval as c_int) }
        self
    }

    /// Set a new filter policy that uses a bloom filter with approximately the specified number of
    /// bits per key.
    ///
    /// `bits_per_key`: bits per key in bloom filter. A good value for bits_per_key is 10, which
    /// yields a filter with ~1% false positive rate.  use_block_based_builder: use block based
    /// filter rather than full fiter.  If you want to builder full filter, it needs to be set to
    /// false.
    ///
    // XXX work out lifetime issues
    // Callers must delete the result after any database that is using the result has been closed.
    //
    // Note (TBD): if you are using a custom comparator that ignores some parts of the keys being
    // compared, you must not use `bloom_filter()` and must provide your own `FilterPolicy` that
    // also ignores the corresponding parts of the keys.  For example, if the comparator ignores
    // trailing spaces, it would be incorrect to use a FilterPolicy (like NewBloomFilterPolicy)
    // that does not ignore trailing spaces in keys.
    pub fn bloom_filter(&mut self, bits_per_key: u32) -> &mut BlockBasedTableOptions {
        let filter = FilterPolicy::bloom(bits_per_key);
        self.filter_policy(filter);
        self
    }

    fn filter_policy(&mut self, filter: FilterPolicy) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_filter_policy(self.options, filter.filter) };
        self
    }

    /// Disable block cache. If this is set to true, then no block cache should be used.
    pub fn no_block_cache(&mut self, nocache: bool) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_no_block_cache(self.options, nocache as c_uchar) }
        self
    }

    /// Use the specified cache for blocks. If not set, rocksdb will automatically create and use
    /// an 8MB internal cache.
    pub fn block_cache(&mut self, cache: &Cache) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_cache(self.options, cache.cache) }
        self
    }

    /// Use the specified cache for compressed blocks. If not set, rocksdb will not use a
    /// compressed block cache.
    pub fn block_cache_compressed(&mut self, cache: &Cache) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_cache_compressed(self.options, cache.cache) }
        self
    }

    /// If true (the detault), place whole keys in the filter (not just prefixes).
    /// This must generally be true for gets to be efficient.
    pub fn whole_key_filtering(&mut self, yes: bool) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_whole_key_filtering(self.options, yes as c_uchar) }
        self
    }

    /// Version used for new tables.
    /// This option only affects newly written tables. When reading exising tables,
    /// the information about version is read from the footer.
    pub fn format_version(&mut self, version: TableVersion) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_format_version(self.options, version as c_int) }
        self
    }
    
    pub fn index_type(&mut self, idx: IndexType) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_index_type(self.options, idx as c_int) }
        self
    }
    
    /// Influence the behavior when kHashSearch is used.  If false, stores a precise prefix to block
    /// range mapping if true, does not store prefix and allows prefix hash collision (less memory
    /// consumption).
    pub fn hash_index_allow_collision(&mut self, yes: bool) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_hash_index_allow_collision(self.options, yes as c_uchar) }
        self
    }

    pub fn cache_index_and_filter_blocks(&mut self, yes: bool) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_cache_index_and_filter_blocks(self.options, yes as c_uchar) }
        self
    }
}

impl Drop for BlockBasedTableOptions {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_block_based_options_destroy(self.options) }
    }
}

#[allow(unused_imports)]
#[cfg(test)]
mod test {
    use super::{Options, DefaultCompare, CompactionFilter, Filter, FilterRes};
    use std::ffi::{CString, CStr};
    use std::str;
    use std::ops::Deref;
    use std::cmp::{Ord,Ordering};

    struct Wrap<T>(T);
    impl<T> Wrap<T> {
        fn wrap(v: T) -> Wrap<T> { Wrap(v) }
        //fn unwrap(self) -> T { self.0 }
    }
    impl<T> From<T> for Wrap<T> {
        fn from(v: T) -> Wrap<T> { Wrap::wrap(v) }
    }
    impl<T,Rhs> PartialEq<Wrap<Rhs>> for Wrap<T> where T: PartialEq<Rhs> {
        fn eq(&self, other: &Wrap<Rhs>) -> bool { self.0.eq(&other.0) }
    }
    impl<T> Eq for Wrap<T> where T: Eq {}
    impl<T,Rhs> PartialOrd<Wrap<Rhs>> for Wrap<T> where T: PartialOrd<Rhs> {
        fn partial_cmp(&self, other: &Wrap<Rhs>) -> Option<Ordering> { self.0.partial_cmp(&other.0) }
    }
    impl<T> Ord for Wrap<T> where T: Ord {
        fn cmp(&self, other: &Self) -> Ordering { self.0.cmp(&other.0) }
    }
    impl<T> Deref for Wrap<T> {
        type Target = T;
        fn deref(&self) -> &T { &self.0 }
    }
    
    /*
    struct Compact(Option<String>);
    impl Compact {
        fn new() -> Compact { Compact(None) }
    }

    const name: CString = CString::new("foo").unwrap();
    impl Filter for Compact {
        type Key = String;
        type Val = String;
        fn name(&self) -> &CStr { &name }
        fn filter(&self, _: u32, _: &Self::Key, _: &Self::Val) -> FilterRes<Self::Val> { FilterRes::Preserve }
        fn stash(&mut self, v: String) -> &String { self.0 = Some(v); self.0.as_ref().unwrap() }
    }
     */

    type MyString = Wrap<String>;
    impl<'a> From<&'a [u8]> for MyString {
        fn from(bytes: &'a [u8]) -> MyString {
            Wrap::wrap(From::from(str::from_utf8(bytes).unwrap()))
        }
    }
    
    #[test]
    fn options() {
        let dir = ::testdir();
        let _ = Options::new()
//            .compaction_filter(CompactionFilter::new(Compact::new()))
            .comparator(DefaultCompare::<MyString>::new())
            .open(dir.path());
    }
}
