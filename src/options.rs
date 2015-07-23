use std::ffi::CString;
use std::ptr;
use libc::{c_uchar, c_int, c_uint, c_double, uint64_t, uint32_t, size_t};

use super::ffi;

pub struct Options {
    options: *mut ffi::rocksdb_options_t,
}

// TBD
pub struct CompactionFilter {
    filter: *mut ffi::rocksdb_compactionfilter_t,
}

// TBD
pub struct CompactionFilterFactory {
    filterfactory: *mut ffi::rocksdb_compactionfilterfactory_t,
}

// TBD
pub struct Comparator {
    comparator: *mut ffi::rocksdb_comparator_t,
}

// TBD
pub struct MergeOperator {
    mergeoperator: *mut ffi::rocksdb_mergeoperator_t,
}

// TBD
pub struct SliceTransform {
    slicetransform: *mut ffi::rocksdb_slicetransform_t,
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
pub enum IndexType {
    BinarySearch = ffi::rocksdb_block_based_table_index_type_binary_search,
    HashSearch = ffi::rocksdb_block_based_table_index_type_hash_search,
}

impl Options {
    pub fn new() -> Options {
        Options {
            options: unsafe { ffi::rocksdb_options_create() }
        }
    }

    pub fn create_if_missing(&mut self, create: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_create_if_missing(self.options, create as c_uchar) };
        self
    }

    pub fn error_if_exists(&mut self, excl: bool) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_error_if_exists(self.options, excl as c_uchar) };
        self
    }

    pub fn increase_parallelism(&mut self, total_threads: u32) -> &mut Options {
        unsafe { ffi::rocksdb_options_increase_parallelism(self.options, total_threads as c_int) };
        self
    }

    pub fn optimize_for_point_lookup(&mut self, block_cache_size_mb: u64) -> &mut Options {
        unsafe { ffi::rocksdb_options_optimize_for_point_lookup(self.options, block_cache_size_mb) };
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

    pub fn compaction_filter(&mut self, filter: CompactionFilter) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_compaction_filter(self.options, filter.filter) };
        self
    }

    pub fn compaction_filter_factory(&mut self, filter: CompactionFilterFactory) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_compaction_filter_factory(self.options, filter.filterfactory) };
        self
    }

    pub fn comparator(&mut self, cmp: Comparator) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_comparator(self.options, cmp.comparator) };
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

    // XXX use Path?
    pub fn db_log_dir(&mut self, dir: &str) -> &mut Options {
        if let Ok(cdir) = CString::new(dir) {
            unsafe { ffi::rocksdb_options_set_db_log_dir(self.options, cdir.as_ptr()) }
        };
        self
    }

    // XXX use Path?
    pub fn wal_dir(&mut self, dir: &str) -> &mut Options {
        if let Ok(cdir) = CString::new(dir) {
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
        unsafe { ffi::rocksdb_options_set_memtable_prefix_bloom_bits(self.options, probes as uint32_t) }
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

    pub fn compaction_style(&mut self, compactionstyle: CompactionStyle) -> &mut Options {
        unsafe { ffi::rocksdb_options_set_compaction_style(self.options, compactionstyle as c_int) }
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

impl Drop for Options {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_options_destroy(self.options) }
    }
}

// Function public to modules within the crate, not exported
pub fn get_options_ptr(opts: &Options) -> *mut ffi::rocksdb_options_t {
    opts.options
}

pub struct FilterPolicy {
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
        if !self.filter.is_null() {
            unsafe { ffi::rocksdb_filterpolicy_destroy(self.filter) };
            self.filter = ptr::null_mut();
        }
    }
}

pub struct Cache {
    cache: *mut ffi::rocksdb_cache_t,
}

impl Cache {
    pub fn lru(capacity: usize) -> Cache {
        Cache {
            cache: unsafe { ffi::rocksdb_cache_create_lru(capacity as size_t) }
        }
    }
}

impl Drop for Cache {
    fn drop(&mut self) {
        if !self.cache.is_null() {
            unsafe { ffi::rocksdb_cache_destroy(self.cache) }
            self.cache = ptr::null_mut();
        }
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

pub struct BlockBasedTableOptions {
    options: *mut ffi::rocksdb_block_based_table_options_t,
}

impl BlockBasedTableOptions {
    pub fn new() -> BlockBasedTableOptions {
        BlockBasedTableOptions {
            options: unsafe { ffi::rocksdb_block_based_options_create() }
        }
    }

    pub fn block_size(&mut self, sz: u64) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_size(self.options, sz as size_t) }
        self
    }

    pub fn block_size_deviation(&mut self, sz: u32) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_size_deviation(self.options, sz as c_int) }
        self
    }

    pub fn block_restart_interval(&mut self, interval: u32) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_restart_interval(self.options, interval as c_int) }
        self
    }

    pub fn filter_policy(&mut self, filter: FilterPolicy) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_filter_policy(self.options, filter.filter) };
        self
    }

    pub fn no_block_cache(&mut self, nocache: bool) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_no_block_cache(self.options, nocache as c_uchar) }
        self
    }

    pub fn block_cache(&mut self, cache: &Cache) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_cache(self.options, cache.cache) }
        self
    }

    pub fn block_cache_compressed(&mut self, cache: &Cache) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_block_cache_compressed(self.options, cache.cache) }
        self
    }

    pub fn whole_key_filtering(&mut self, yes: bool) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_whole_key_filtering(self.options, yes as c_uchar) }
        self
    }

    pub fn format_version(&mut self, version: TableVersion) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_format_version(self.options, version as c_int) }
        self
    }
    
    pub fn index_type(&mut self, idx: IndexType) -> &mut BlockBasedTableOptions {
        unsafe { ffi::rocksdb_block_based_options_set_index_type(self.options, idx as c_int) }
        self
    }

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
