use std::ptr;
use std::mem;
use std::slice;
use std::ffi::CString;
use std::marker::PhantomData;
use std::iter;
use std::vec;

use libc;
use libc::{c_uchar, c_char, c_int, size_t, c_void};

use super::{Error, Result, ffi};
use super::ffi::rocksdb_t;
use super::options::{Options, get_options_ptr};

#[cfg(cf)]
pub struct ColumnFamily<'a> {
    name: &'a str,
    options: &'a Options,
}

#[cfg(cf)]
impl<'a> ColumnFamily<'a> {
    pub fn new(name: &'a str, options: &'a Options) -> ColumnFamily<'a> {
        ColumnFamily { name: name, options: options }
    }
}

#[cfg(cf)]
pub struct ColumnFamilyHandle<'a> {
    db: PhantomData<&'a Db>,
    handle: *mut rocksdb_column_family_handle_t,
}

#[cfg(cf)]
impl<'a> ColumnFamilyHandle<'a> {
    fn new(_: &'a Db, handle: *mut rocksdb_column_family_handle_t) -> ColumnFamilyHandle<'a> {
        ColumnFamilyHandle { db: PhantomData, handle: handle }
    }
}

#[cfg(cf)]
impl<'a> Drop for ColumnFamilyHandle<'a> {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_column_family_handle_destroy(self.handle) }
    }
}

pub struct Db {
    db: *mut rocksdb_t,
}

impl Db {
    // XXX name -> Path
    pub fn open(options: &Options, name: &str) -> Result<Db> {
        let cname = CString::new(name).unwrap();
        
        unsafe {
            let mut err = ptr::null_mut();
            let ret = ffi::rocksdb_open(get_options_ptr(options), cname.as_ptr(), &mut err);

            if ret.is_null() {
                Err(Error::new(err))
            } else {
                Ok(Db { db: ret })
            }
        }
    }

    pub fn open_for_read_only(options: &Options, name: &str, error_if_log_file_exists: bool) -> Result<Db> {
        let cname = CString::new(name).unwrap();

        unsafe {
            let mut err = ptr::null_mut();
            let ret = ffi::rocksdb_open_for_read_only(get_options_ptr(options), cname.as_ptr(),
                                                      error_if_log_file_exists as c_uchar, &mut err);

            if ret.is_null() {
                Err(Error::new(err))
            } else {
                Ok(Db { db: ret })
            }
        }
    }

    // how to express the lifetime of the handles is <= the db? Maybe needs Rc<>?
    #[cfg(cf)]
    pub fn open_column_families<'a>(options: &Options, name: &str, families: Vec<ColumnFamily>) -> Result<(Db, Vec<ColumnFamilyHandle<'a>>)> {
        let cname = CString::new(name).unwrap();
        
        unsafe {
            let mut err = ptr::null_mut();
            let fnames : Vec<_> = families.iter().map(|f| CString::new(f.name).unwrap()).collect();
            let foptions : Vec<_> = families.iter().map(|f| f.options.options).collect();
            let mut handles : Vec<_> = (0..families.len()).map(|_| ptr::null_mut()).collect();
            let ret = ffi::rocksdb_open_column_families(options.options, cname.as_ptr(),
                                                        families.len() as c_int,
                                                        fnames.as_ptr(),
                                                        foptions.as_ptr(),
                                                        handles.as_mut_ptr(), &mut err);

            if ret.is_null() {
                Err(Error::new(err))
            } else {
                let db = Db { db: ret };
                let hnd = handles.into_iter().map(|h| ColumnFamilyHandle::new(&db, h)).collect();
                
                Ok((db, hnd))
            }
        }
    }

    pub fn put<K, V>(&self, options: &WriteOptions, key: K, val: V) -> Result<()>
        where K : IntoSlice, V : IntoSlice
    {
        let ks = key.into_slice();
        let vs = val.into_slice();
        
        unsafe {
            let mut err = ptr::null_mut();
            
            ffi::rocksdb_put(self.db, options.options,
                             ks.as_ptr() as *const c_char, ks.len() as size_t,
                             vs.as_ptr() as *const c_char, vs.len() as size_t,
                             &mut err);
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::new(err))
            }
        }
    }

    pub fn get<K, V>(&self, options: &ReadOptions, key: K) -> Result<V>
        where K : IntoSlice, V : FromSlice
    {
        let ks = key.into_slice();
        
        unsafe {
            let mut err = ptr::null_mut();
            let mut vallen = 0;
            let res = ffi::rocksdb_get(self.db, options.options,
                                       ks.as_ptr() as *const c_char, ks.len() as size_t,
                                       &mut vallen, &mut err);
            if !err.is_null() {
                Err(Error::new(err))
            } else if res.is_null() {
                Err(Error::notfound())
            } else {
                let s = slice::from_raw_parts(res as *const u8, vallen as usize);
                let v = FromSlice::from_slice(s);

                libc::free(res as *mut c_void);
                Ok(v)
            }
        }
    }

    pub fn delete<K: IntoSlice>(&self, options: &WriteOptions, key: K) -> Result<()> {
        let ks = key.into_slice();

        unsafe {
            let mut err = ptr::null_mut();

            ffi::rocksdb_delete(self.db, options.options,
                                ks.as_ptr() as *const c_char, ks.len() as size_t,
                                &mut err);
            
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::new(err))
            }
        }
    }

    pub fn write(&self, options: &WriteOptions, batch: WriteBatch) -> Result<()> {
        unsafe {
            let mut err = ptr::null_mut();

            ffi::rocksdb_write(self.db, options.options, batch.batch, &mut err);
            
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::new(err))
            }
        }
        
    }

    pub fn multi_get<K,V,KI>(&self, options: &ReadOptions, keys: KI) -> Vec<Result<V>>
        where K: IntoSlice, V: FromSlice, KI: iter::IntoIterator<Item=K>
    {
        let kss: (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.into_slice(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            let mut vals : Vec<_> = iter::repeat(ptr::null_mut()).take(kss.0.len()).collect();
            let mut lens : Vec<_> = iter::repeat(0).take(kss.0.len()).collect();
            let mut errs : Vec<_> = iter::repeat(ptr::null_mut()).take(kss.0.len()).collect();

            ffi::rocksdb_multi_get(self.db, options.options,
                                   kss.0.len() as size_t, kss.0.as_ptr(), kss.1.as_ptr(),
                                   vals.as_mut_ptr(), lens.as_mut_ptr(), errs.as_mut_ptr());

            vals.into_iter()
                .zip(lens)                      // zip value pointers with lens
                .map(|(v, l)| {                 // convert (ptr,len) -> [u8]
                    if v.is_null() {
                        None
                    } else {
                        let s = slice::from_raw_parts(v as *mut u8, l as usize);
                        let r = FromSlice::from_slice(s);
                        libc::free(v as *mut c_void);
                        Some(r)
                    }
                })
                .zip(errs)                      // zip slices and errors
                .map(|(v, e)| match v {         // set error on missing values
                    Some(v) => Ok(v),
                    None => if e.is_null() { Err(Error::notfound()) } else { Err(Error::new(e)) }
                })
                .collect()
        }        
    }

    pub fn iterator_key<'a,K>(&'a self, options: &'a ReadOptions) -> DbIterator<'a,DbIterKey<K>>
        where K: FromSlice
    {
        DbIterator::new(self, options)
    }

    pub fn iterator_value<'a,V>(&'a self, options: &'a ReadOptions) -> DbIterator<'a,DbIterVal<V>>
        where V: FromSlice
    {
        DbIterator::new(self, options)
    }

    pub fn iterator_key_value<'a,K,V>(&'a self, options: &'a ReadOptions) -> DbIterator<'a,DbIterKeyVal<K,V>>
        where K: FromSlice, V: FromSlice
    {
        DbIterator::new(self, options)
    }
}

pub struct DbIterKey<K>(PhantomData<K>);
pub struct DbIterVal<V>(PhantomData<V>);
pub struct DbIterKeyVal<K,V>(PhantomData<(K,V)>);

impl Drop for Db {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_close(self.db) }
    }
}

pub struct DbIterator<'a,Item>
{
    iter: *mut ffi::rocksdb_iterator_t,
    db: PhantomData<&'a Db>,
    item: PhantomData<Item>,
}

impl<'a,Item> DbIterator<'a,Item>
{
    fn new(db: &'a Db, options: &'a ReadOptions) -> DbIterator<'a,Item> {
        DbIterator {
            iter: unsafe { ffi::rocksdb_create_iterator(db.db, options.options) },
            db: PhantomData,
            item: PhantomData,
        }
    }

    #[inline]
    pub fn valid(&self) -> bool {
        unsafe { ffi::rocksdb_iter_valid(self.iter) != 0 }
    }

    pub fn seek_first(&mut self) -> &mut DbIterator<'a,Item> {
        unsafe { ffi::rocksdb_iter_seek_to_first(self.iter) }
        self
    }

    pub fn seek_last(&mut self) -> &mut DbIterator<'a,Item> {
        unsafe { ffi::rocksdb_iter_seek_to_last(self.iter) }
        self
    }    

    pub fn seek_next(&mut self) -> &mut DbIterator<'a,Item> {
        if self.valid() {
            unsafe { ffi::rocksdb_iter_next(self.iter) }
        }
        self
    }    

    pub fn seek_prev(&mut self) -> &mut DbIterator<'a,Item> {
        if self.valid() {
            unsafe { ffi::rocksdb_iter_prev(self.iter) }
        }
        self
    }    
    
    pub fn seek<K>(&mut self, key: K) -> &mut DbIterator<'a,Item>
        where K: IntoSlice
    {
        let s = key.into_slice();
        
        unsafe { ffi::rocksdb_iter_seek(self.iter, s.as_ptr() as *const c_char, s.len() as size_t) }
        self
    }

    pub fn key<K>(&self) -> Option<K>
        where K: FromSlice
    {
        if !self.valid() { return None }
        
        unsafe {
            let mut klen = 0;
            let kptr = ffi::rocksdb_iter_key(self.iter, &mut klen);
            let s = slice::from_raw_parts(kptr as *const u8, klen as usize);

            Some(FromSlice::from_slice(s))
        }
    }

    pub fn value<V>(&self) -> Option<V>
        where V: FromSlice
    {
        if !self.valid() { return None }
        
        unsafe {
            let mut klen = 0;
            let kptr = ffi::rocksdb_iter_value(self.iter, &mut klen);
            let s = slice::from_raw_parts(kptr as *const u8, klen as usize);

            Some(FromSlice::from_slice(s))
        }
    }
}

impl<'a,Item> Drop for DbIterator<'a,Item>
{
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_iter_destroy(self.iter) }
    }
}

impl<'a,K> Iterator for DbIterator<'a,DbIterKey<K>>
    where K: FromSlice
{
    type Item=K;
    
    fn next(&mut self) -> Option<K> {
        let ret = self.key();
        self.seek_next();

        ret
    }

    fn last(mut self) -> Option<K> {
        self.seek_last();
        self.key()
    }
}

impl<'a,V> Iterator for DbIterator<'a,DbIterVal<V>>
    where V: FromSlice
{
    type Item=V;
    
    fn next(&mut self) -> Option<V> {
        let ret = self.value();
        self.seek_next();

        ret
    }

    fn last(mut self) -> Option<V> {
        self.seek_last();
        self.value()
    }
}

impl<'a,K,V> Iterator for DbIterator<'a,DbIterKeyVal<K,V>>
    where K: FromSlice, V: FromSlice
{
    type Item=(K,V);
    
    fn next(&mut self) -> Option<(K,V)> {
        if self.valid() {
            let ret = (self.key().unwrap(), self.value().unwrap());
            self.seek_next();

            Some(ret)
        } else {
            None
        }
    }

    fn last(mut self) -> Option<(K,V)> {
        self.seek_last();

        if self.valid() {
            Some((self.key().unwrap(), self.value().unwrap()))
        } else {
            None
        }
    }
}

pub struct WriteBatch {
    batch: *mut ffi::rocksdb_writebatch_t,
}

pub enum BatchIterItem<K, V>
{
    Put(K, V),
    Delete(K),
}

extern fn batch_iter_put_cb<K, V>(ptr: *mut c_void, key: *const c_char, klen: size_t, val: *const c_char, vallen: size_t)
    where K: FromSlice, V: FromSlice
{
    unsafe { 
        let mut vec : &mut Vec<BatchIterItem<K,V>> = mem::transmute(ptr);
        let ks = slice::from_raw_parts(key as *const u8, klen as usize);
        let vs = slice::from_raw_parts(val as *const u8, vallen as usize);
    
        vec.push(BatchIterItem::Put(FromSlice::from_slice(ks), FromSlice::from_slice(vs)));
    }
}

extern fn batch_iter_delete_cb<K, V>(ptr: *mut c_void, key: *const c_char, klen: size_t)
    where K: FromSlice
{
    unsafe {
        let mut vec : &mut Vec<BatchIterItem<K,V>> = mem::transmute(ptr);
        let ks = slice::from_raw_parts(key as *const u8, klen as usize);
        
        vec.push(BatchIterItem::Delete(FromSlice::from_slice(ks)));
    }
}

impl WriteBatch {
    pub fn new() -> WriteBatch {
        WriteBatch {
            batch: unsafe { ffi::rocksdb_writebatch_create() }
        }
    }

    pub fn new_from_data(data: &Vec<u8>) -> WriteBatch {
        WriteBatch {
            batch: unsafe { ffi::rocksdb_writebatch_create_from(data.as_ptr() as *const c_char, data.len() as size_t) }
        }
    }

    pub fn clear(&mut self) {
        unsafe { ffi::rocksdb_writebatch_clear(self.batch) }
    }

    pub fn count(&self) -> usize {
        unsafe { ffi::rocksdb_writebatch_count(self.batch) as usize }
    }

    pub fn put<K, V>(&mut self, key: K, val: V)
        where K: IntoSlice, V: IntoSlice
    {
        let ks = key.into_slice();
        let vs = val.into_slice();

        unsafe {
            ffi::rocksdb_writebatch_put(self.batch,
                                        ks.as_ptr() as *const c_char, ks.len() as size_t,
                                        vs.as_ptr() as *const c_char, vs.len() as size_t)
        }        
    }

    pub fn putv<K, V, KI, VI>(&mut self, keys: KI, vals: VI)
        where K: IntoSlice, V: IntoSlice, KI: iter::IntoIterator<Item=K>, VI: iter::IntoIterator<Item=V>
    {
        let kss : (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.into_slice(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();
        let vss : (Vec<_>, Vec<_>) = vals.into_iter()
            .map(|v| { let s = v.into_slice(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            ffi::rocksdb_writebatch_putv(self.batch,
                                         kss.0.len() as c_int, kss.0.as_ptr(), kss.1.as_ptr(),
                                         vss.0.len() as c_int, vss.0.as_ptr(), vss.1.as_ptr())
        }
    }

    pub fn merge<K, V>(&mut self, key: K, val: V)
        where K: IntoSlice, V: IntoSlice
    {
        let ks = key.into_slice();
        let vs = val.into_slice();

        unsafe {
            ffi::rocksdb_writebatch_merge(self.batch,
                                          ks.as_ptr() as *const c_char, ks.len() as size_t,
                                          vs.as_ptr() as *const c_char, vs.len() as size_t)
        }        
    }

    pub fn mergev<K, V, KI, VI>(&mut self, keys: KI, vals: VI)
        where K: IntoSlice, V: IntoSlice, KI: iter::IntoIterator<Item=K>, VI: iter::IntoIterator<Item=V>
    {
        let kss : (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.into_slice(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();
        let vss : (Vec<_>, Vec<_>) = vals.into_iter()
            .map(|v| { let s = v.into_slice(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            ffi::rocksdb_writebatch_mergev(self.batch,
                                           kss.0.len() as c_int, kss.0.as_ptr(), kss.1.as_ptr(),
                                           vss.0.len() as c_int, vss.0.as_ptr(), vss.1.as_ptr())
        }
    }

    pub fn delete<K>(&mut self, key: K)
        where K: IntoSlice
    {
        let ks = key.into_slice();

        unsafe {
            ffi::rocksdb_writebatch_delete(self.batch,
                                           ks.as_ptr() as *const c_char, ks.len() as size_t)
        }        
    }

    pub fn deletev<K, KI>(&mut self, keys: KI)
        where K: IntoSlice, KI: iter::IntoIterator<Item=K>
    {
        let kss : (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.into_slice(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            ffi::rocksdb_writebatch_deletev(self.batch,
                                            kss.0.len() as c_int, kss.0.as_ptr(), kss.1.as_ptr())
        }
    }

    pub fn put_log_data<V>(&mut self, blob: &V)
        where V: IntoSlice
    {
        let bs = blob.into_slice();

        unsafe {
            ffi::rocksdb_writebatch_put_log_data(self.batch, bs.as_ptr() as *const c_char, bs.len() as size_t)
        }
    }

    pub fn data(&self) -> Vec<u8> {
        unsafe {
            let mut len : size_t = 0;
            let ret = ffi::rocksdb_writebatch_data(self.batch, &mut len);

            let vec = slice::from_raw_parts(ret as *const u8, len as usize).to_vec();

            libc::free(ret as *mut c_void);

            vec
        }
    }

    pub fn iter<K, V>(&self) -> vec::IntoIter<BatchIterItem<K,V>>
        where K: FromSlice, V: FromSlice
    {
        let mut vec : Vec<_> = Vec::new();
        
        unsafe {
            ffi::rocksdb_writebatch_iterate(self.batch, mem::transmute(&mut vec),
                                            Some(batch_iter_put_cb::<K,V>), Some(batch_iter_delete_cb::<K,V>))
        }

        vec.into_iter()
    }
}

impl<K,V> iter::FromIterator<BatchIterItem<K,V>> for WriteBatch
    where K: FromSlice + IntoSlice, V: FromSlice + IntoSlice
{
    fn from_iter<T>(iter: T) -> Self
        where T: iter::IntoIterator<Item=BatchIterItem<K,V>>
    {
        let mut ret = WriteBatch::new();
            
        for i in iter {
            match i {
                BatchIterItem::Put(k, v) => ret.put(k, v),
                BatchIterItem::Delete(k) => ret.delete(k),
            }
        }

        ret
    }
}

impl Drop for WriteBatch {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_writebatch_destroy(self.batch) }
    }
}

pub struct Snapshot<'a> {
    snap: *const ffi::rocksdb_snapshot_t,
    db: &'a Db,
}

impl<'a> Snapshot<'a> {
    pub fn new(db: &'a Db) -> Snapshot<'a> {
        Snapshot {
            snap: unsafe { ffi::rocksdb_create_snapshot(db.db) },
            db: db,
        }
    }
}

impl<'a> Drop for Snapshot<'a> {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_release_snapshot(self.db.db, self.snap) }
    }
}

pub enum ReadTier {
    /// data in memtable, block cache, OS cache or storage
    ReadAllTier = 0,
    /// data in memtable or block cache
    BlockCacheTier = 1,
}

pub struct ReadOptions {
    options: *mut ffi::rocksdb_readoptions_t,
}

impl ReadOptions {
    pub fn new() -> ReadOptions {
        ReadOptions {
            options: unsafe { ffi::rocksdb_readoptions_create() },
        }
    }

    pub fn verify_checksums(&mut self, yes: bool) -> &mut ReadOptions {
        unsafe { ffi::rocksdb_readoptions_set_verify_checksums(self.options, yes as c_uchar) }
        self
    }

    pub fn fill_cache(&mut self, yes: bool) -> &mut ReadOptions {
        unsafe { ffi::rocksdb_readoptions_set_fill_cache(self.options, yes as c_uchar) }
        self
    }

    pub fn snapshot<'a>(&'a mut self, snap: &'a Snapshot) -> &'a mut ReadOptions {
        unsafe { ffi::rocksdb_readoptions_set_snapshot(self.options, snap.snap) }
        self
    }

    pub fn iterate_upper_bound<'a, K>(&'a mut self, key: K) -> &'a mut ReadOptions
        where K: IntoSlice
    {
        let ks = key.into_slice();
        
        unsafe {
            ffi::rocksdb_readoptions_set_iterate_upper_bound(self.options, ks.as_ptr() as *const c_char, ks.len() as size_t)
        }
        self
    }

    pub fn read_tier(&mut self, tier: ReadTier) -> &mut ReadOptions {
        unsafe { ffi::rocksdb_readoptions_set_read_tier(self.options, tier as c_int) }
        self
    }

    pub fn tailing(&mut self, yes: bool) -> &mut ReadOptions {
        unsafe { ffi::rocksdb_readoptions_set_tailing(self.options, yes as c_uchar) }
        self
    }
}

impl Drop for ReadOptions {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_readoptions_destroy(self.options) }
    }
}

pub struct WriteOptions {
    options: *mut ffi::rocksdb_writeoptions_t
}

impl WriteOptions {
    pub fn new() -> WriteOptions {
        WriteOptions {
            options: unsafe { ffi::rocksdb_writeoptions_create() }
        }
    }

    pub fn sync(&mut self, yes: bool) -> &mut WriteOptions {
        unsafe { ffi::rocksdb_writeoptions_set_sync(self.options, yes as c_uchar) }
        self
    }

    pub fn disable_wal(&mut self, yes: bool) -> &mut WriteOptions {
        unsafe { ffi::rocksdb_writeoptions_disable_WAL(self.options, yes as c_int) }
        self
    }
}

impl Drop for WriteOptions {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_writeoptions_destroy(self.options) }
    }
}

pub trait IntoSlice {
    fn into_slice(&self) -> &[u8];
}

impl IntoSlice for [u8] {
    fn into_slice(&self) -> &[u8] { self }
}

impl<'a> IntoSlice for &'a str {
    fn into_slice<'b>(&'b self) -> &'b [u8] { self.as_bytes() }
}

pub trait FromSlice {
    fn from_slice(slice: &[u8]) -> Self;
}

impl FromSlice for Vec<u8> {
    fn from_slice(slice: &[u8]) -> Vec<u8> { slice.to_vec() }
}

#[cfg(test)]
mod test {
    use ::Options;
    use ::Db;
    use super::WriteOptions;
    
    #[test]
    fn readopts() {
        let mut options = Options::new();
        options.error_if_exists(true).paranoid_checks(true);
        let mut wropt = WriteOptions::new();
        wropt.sync(false);
        let db = Db::open(&options, "foo").unwrap();
        db.put(&wropt, "foo", "bar").unwrap();
    }
}
