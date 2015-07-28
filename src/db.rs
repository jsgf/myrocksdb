use std::ptr;
use std::mem;
use std::str;
use std::vec;
use std::ops::{Deref,DerefMut};
use std::iter;
use std::slice;
use std::sync::Arc;
use std::path::Path;
use std::ffi::CString;
use std::borrow::Borrow;
use std::marker::PhantomData;

use libc;
use libc::{c_uchar, c_char, c_int, size_t, c_void};

use super::{Error, Result, ffi};
use super::ffi::rocksdb_t;
use super::options::{Options, get_options_ptr};

pub struct RawBuf {
    ptr: *mut u8,
    sz: usize
}

/// Raw buffer returned from the database. Users implement `From<RawBuf>` to convert it into some
/// useful type.
impl RawBuf {
    unsafe fn new(ptr: *mut c_char, sz: size_t) -> RawBuf {
        RawBuf { ptr: ptr as *mut u8, sz: sz as usize }
    }

    fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr, self.sz) }
    }

    fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.ptr, self.sz) }
    }
}

impl AsRef<[u8]> for RawBuf {
    fn as_ref(&self) -> &[u8] { self.as_slice() }
}

impl AsMut<[u8]> for RawBuf {
    fn as_mut(&mut self) -> &mut [u8] { self.as_mut_slice() }
}

impl Deref for RawBuf {
    type Target = [u8];

    fn deref(&self) -> &[u8] { self.as_slice() }
}

impl DerefMut for RawBuf {
    fn deref_mut(&mut self) -> &mut [u8] { self.as_mut_slice() }
}

impl Drop for RawBuf {
    fn drop(&mut self) {
        unsafe { libc::free(self.ptr as *mut c_void) }
    }
}

impl From<RawBuf> for Vec<u8> {
    fn from(bytes: RawBuf) -> Vec<u8> { Vec::from(bytes.as_ref()) }
}

impl From<RawBuf> for String {
    fn from(bytes: RawBuf) -> String { String::from(str::from_utf8(bytes.as_ref()).unwrap()) }
}

/// Represents a reference to a transient C buffer. The lifetime and
/// the type parameter represent what the buffer is owned by and
/// therefore borrowed from.
pub struct RawRef<'a, T: 'a> {
    ptr: *mut u8,
    sz: usize,
    owner: PhantomData<&'a mut T>,
}

impl<'a, T> RawRef<'a, T>
    where T: 'a
{
    unsafe fn new(ptr: *mut c_char, sz: size_t, _owner: &mut T) -> RawRef<'a, T> {
        RawRef { ptr: ptr as *mut u8, sz: sz as usize, owner: PhantomData }
    }

    fn as_slice(&'a self) -> &'a [u8] {
        unsafe { slice::from_raw_parts(self.ptr, self.sz) }
    }

    fn as_mut_slice(&'a mut self) -> &'a mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.ptr, self.sz) }
    }
}

/*
impl<'a, T> Deref for RawRef<'a, T>
    where T: 'a
{
    type Target = [u8];

    fn deref(&self) -> &[u8] { self.as_slice() }
}

impl<'a, T> DerefMut for RawRef<'a, T>
    where T: 'a
{
    fn deref_mut(&mut self) -> &mut [u8] { self.as_mut_slice() }
}
*/

impl<'a, T> From<RawRef<'a, T>> for Vec<u8>
    where T: 'a
{
    fn from(bytes: RawRef<'a, T>) -> Vec<u8> { Vec::from(bytes.as_slice()) }
}

impl<'a, T> From<RawRef<'a, T>> for String
    where T: 'a
{
    fn from(bytes: RawRef<'a, T>) -> String { String::from(str::from_utf8(bytes.as_slice()).unwrap()) }
}

pub struct ColumnFamily<'a> {
    name: &'a str,
    options: &'a Options,
}

impl<'a> ColumnFamily<'a> {
    pub fn new(name: &'a str, options: &'a Options) -> ColumnFamily<'a> {
        ColumnFamily { name: name, options: options }
    }
}

pub struct ColumnFamilyHandle(*mut ffi::rocksdb_column_family_handle_t);

impl ColumnFamilyHandle {
    // Caller must have corresponding db
    fn new(_: &Db, handle: *mut ffi::rocksdb_column_family_handle_t) -> ColumnFamilyHandle {
        ColumnFamilyHandle(handle)
    }
}

impl Drop for ColumnFamilyHandle {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_column_family_handle_destroy(self.0) }
    }
}

#[allow(raw_pointer_derive)]
#[derive(Debug)]
struct DbInner(*mut rocksdb_t);

impl DbInner {
    fn as_ptr(&self) -> *mut rocksdb_t { self.0 }
}

impl Drop for DbInner {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_close(self.0) }
    }
}

#[derive(Clone, Debug)]
pub struct Db {
    db: Arc<DbInner>,
}

unsafe impl Sync for DbInner {}
unsafe impl Send for DbInner {}

impl Db {
    fn db(&self) -> &DbInner { self.db.borrow() }
    
    pub fn open<P: AsRef<Path>>(options: &Options, name: P) -> Result<Db> {
        let cname = name.as_ref().as_os_str().to_cstring().unwrap();
        
        unsafe {
            let mut err = ptr::null_mut();
            let ret = ffi::rocksdb_open(get_options_ptr(options), cname.as_ptr(), &mut err);

            if ret.is_null() {
                Err(Error::from_cptr(err))
            } else {
                Ok(Db { db: Arc::new(DbInner(ret)) })
            }
        }
    }

    pub fn open_for_read_only<P: AsRef<Path>>(options: &Options, name: P, error_if_log_file_exists: bool) -> Result<Db> {
        let cname = name.as_ref().as_os_str().to_cstring().unwrap();

        unsafe {
            let mut err = ptr::null_mut();
            let ret = ffi::rocksdb_open_for_read_only(get_options_ptr(options), cname.as_ptr(),
                                                      error_if_log_file_exists as c_uchar, &mut err);

            if ret.is_null() {
                Err(Error::from_cptr(err))
            } else {
                Ok(Db { db: Arc::new(DbInner(ret)) })
            }
        }
    }

    pub fn open_column_families<'a, CFI>(options: &Options, name: &str, families: CFI) -> Result<(Db, Vec<ColumnFamilyHandle>)>
        where CFI: iter::IntoIterator<Item=ColumnFamily<'a>>
    {
        let cname = CString::new(name).unwrap();
        
        unsafe {
            let mut err = ptr::null_mut();
            let (fnames, foptions): (Vec<_>, Vec<_>) = families.into_iter()
                .map(|f| (CString::new(f.name).unwrap().as_bytes().as_ptr() as *const c_char,
                          get_options_ptr(f.options)))
                .unzip();
            let mut handles: Vec<_> = (0..fnames.len()).map(|_| ptr::null_mut()).collect();
            let ret = ffi::rocksdb_open_column_families(get_options_ptr(options), cname.as_ptr(),
                                                        fnames.len() as c_int,
                                                        fnames.as_ptr(),
                                                        foptions.as_ptr(),
                                                        handles.as_mut_ptr(), &mut err);

            if ret.is_null() {
                Err(Error::from_cptr(err))
            } else {
                let db = Db { db: Arc::new(DbInner(ret)) };
                let hnd = handles.into_iter().map(|h| ColumnFamilyHandle::new(&db, h)).collect();
                
                Ok((db, hnd))
            }
        }
    }

    pub fn put<K, V>(&self, options: &WriteOptions, key: K, val: V) -> Result<()>
        where K: AsRef<[u8]>, V: AsRef<[u8]>
    {
        let ks = key.as_ref();
        let vs = val.as_ref();
        
        unsafe {
            let mut err = ptr::null_mut();
            let db = self.db();
            
            ffi::rocksdb_put(db.as_ptr(), options.options,
                             ks.as_ptr() as *const c_char, ks.len() as size_t,
                             vs.as_ptr() as *const c_char, vs.len() as size_t,
                             &mut err);
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::from_cptr(err))
            }
        }
    }

    pub fn put_cf<K, V>(&self, options: &WriteOptions, cf: &ColumnFamilyHandle, key: K, val: V) -> Result<()>
        where K: AsRef<[u8]>, V: AsRef<[u8]>
    {
        let ks = key.as_ref();
        let vs = val.as_ref();
        
        unsafe {
            let mut err = ptr::null_mut();
            let db = self.db();
            
            ffi::rocksdb_put_cf(db.as_ptr(), options.options, cf.0,
                                ks.as_ptr() as *const c_char, ks.len() as size_t,
                                vs.as_ptr() as *const c_char, vs.len() as size_t,
                                &mut err);
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::from_cptr(err))
            }
        }
    }

    pub fn merge<K, V>(&self, options: &WriteOptions, key: K, val: V) -> Result<()>
        where K: AsRef<[u8]>, V: AsRef<[u8]>
    {
        let ks = key.as_ref();
        let vs = val.as_ref();
        
        unsafe {
            let mut err = ptr::null_mut();
            let db = self.db();
            
            ffi::rocksdb_merge(db.as_ptr(), options.options,
                               ks.as_ptr() as *const c_char, ks.len() as size_t,
                               vs.as_ptr() as *const c_char, vs.len() as size_t,
                               &mut err);
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::from_cptr(err))
            }
        }
    }

    pub fn merge_cf<K, V>(&self, options: &WriteOptions, cf: &ColumnFamilyHandle, key: K, val: V) -> Result<()>
        where K: AsRef<[u8]>, V: AsRef<[u8]>
    {
        let ks = key.as_ref();
        let vs = val.as_ref();
        
        unsafe {
            let mut err = ptr::null_mut();
            let db = self.db();
            
            ffi::rocksdb_merge_cf(db.as_ptr(), options.options, cf.0,
                                  ks.as_ptr() as *const c_char, ks.len() as size_t,
                                  vs.as_ptr() as *const c_char, vs.len() as size_t,
                                  &mut err);
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::from_cptr(err))
            }
        }
    }

    pub fn get<K, V>(&self, options: &ReadOptions, key: K) -> Result<V>
        where K: AsRef<[u8]>, V: From<RawBuf>
    {
        let ks = key.as_ref();
        
        unsafe {
            let mut err = ptr::null_mut();
            let mut vallen = 0;
            let db = self.db();
            let res = ffi::rocksdb_get(db.as_ptr(), options.options,
                                       ks.as_ptr() as *const c_char, ks.len() as size_t,
                                       &mut vallen, &mut err);
            if !err.is_null() {
                Err(Error::from_cptr(err))
            } else if res.is_null() {
                Err(Error::NotFound)
            } else {
                Ok(V::from(RawBuf::new(res, vallen)))
            }
        }
    }

    pub fn get_cf<K, V>(&self, options: &ReadOptions, cf: &ColumnFamilyHandle, key: K) -> Result<V>
        where K: AsRef<[u8]>, V: From<RawBuf>
    {
        let ks = key.as_ref();
        
        unsafe {
            let mut err = ptr::null_mut();
            let mut vallen = 0;
            let db = self.db();
            let res = ffi::rocksdb_get_cf(db.as_ptr(), options.options, cf.0,
                                          ks.as_ptr() as *const c_char, ks.len() as size_t,
                                          &mut vallen, &mut err);
            if !err.is_null() {
                Err(Error::from_cptr(err))
            } else if res.is_null() {
                Err(Error::NotFound)
            } else {
                Ok(V::from(RawBuf::new(res, vallen)))
            }
        }
    }

    pub fn delete<K: AsRef<[u8]>>(&self, options: &WriteOptions, key: K) -> Result<()> {
        let ks = key.as_ref();

        unsafe {
            let mut err = ptr::null_mut();
            let db = self.db();

            ffi::rocksdb_delete(db.as_ptr(), options.options,
                                ks.as_ptr() as *const c_char, ks.len() as size_t,
                                &mut err);
            
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::from_cptr(err))
            }
        }
    }

    pub fn delete_cf<K: AsRef<[u8]>>(&self, options: &WriteOptions, cf: &ColumnFamilyHandle, key: K) -> Result<()> {
        let ks = key.as_ref();

        unsafe {
            let mut err = ptr::null_mut();
            let db = self.db();

            ffi::rocksdb_delete_cf(db.as_ptr(), options.options, cf.0,
                                   ks.as_ptr() as *const c_char, ks.len() as size_t,
                                   &mut err);
            
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::from_cptr(err))
            }
        }
    }

    pub fn write(&self, options: &WriteOptions, batch: WriteBatch) -> Result<()> {
        unsafe {
            let mut err = ptr::null_mut();
            let db = self.db();

            ffi::rocksdb_write(db.as_ptr(), options.options, batch.batch, &mut err);
            
            if err.is_null() {
                Ok(())
            } else {
                Err(Error::from_cptr(err))
            }
        }
        
    }

    pub fn multi_get<K, V, KI>(&self, options: &ReadOptions, keys: KI) -> Vec<Result<V>>
        where K: AsRef<[u8]>, V: From<RawBuf>, KI: iter::IntoIterator<Item=K>
    {
        let kss: (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            let mut vals: Vec<_> = iter::repeat(ptr::null_mut()).take(kss.0.len()).collect();
            let mut lens: Vec<_> = iter::repeat(0).take(kss.0.len()).collect();
            let mut errs: Vec<_> = iter::repeat(ptr::null_mut()).take(kss.0.len()).collect();
            let db = self.db();

            ffi::rocksdb_multi_get(db.as_ptr(), options.options,
                                   kss.0.len() as size_t, kss.0.as_ptr(), kss.1.as_ptr(),
                                   vals.as_mut_ptr(), lens.as_mut_ptr(), errs.as_mut_ptr());

            vals.into_iter()
                .zip(lens)                      // zip value pointers with lengths
                .map(|(v, l)| {                 // convert (ptr,len) -> [u8]
                    if v.is_null() {
                        None
                    } else {
                        Some(V::from(RawBuf::new(v, l)))
                    }
                })
                .zip(errs)                      // zip slices and errors
                .map(|(v, e)| match v {         // set error on missing values
                    Some(v) => Ok(v),
                    None => if e.is_null() { Err(Error::NotFound) } else { Err(Error::from_cptr(e)) }
                })
                .collect()
        }        
    }

    // 'db => the iterator can't outlive the db itself
    // 'k => the key can't outlive an iteration
    pub fn iterator_key<'db, K>(&'db self, options: &'db ReadOptions) -> DbIterator<'db, DbIterKey<K>>
        where for <'k> K: From<RawRef<'k, DbIterator<'db, DbIterKey<K>>>> + 'k
    {
        DbIterator::new(self, options)
    }

    // 'db => the iterator can't outlive the db itself
    // 'v => the value can't outlive an iteration
    pub fn iterator_value<'db, V>(&'db self, options: &'db ReadOptions) -> DbIterator<'db, DbIterVal<V>>
        where for <'v> V: From<RawRef<'v, DbIterator<'db, DbIterVal<V>>>> + 'v
    {
        DbIterator::new(self, options)
    }

    pub fn iterator_key_value<'db, K, V>(&'db self, options: &'db ReadOptions) -> DbIterator<'db, DbIterKeyVal<K, V>>
        where for <'k> K: From<RawRef<'k, DbIterator<'db, DbIterKey<K>>>> + 'k,
              for <'v> V: From<RawRef<'v, DbIterator<'db, DbIterVal<V>>>> + 'v
    {
        DbIterator::new(self, options)
    }
}

pub struct DbIterKey<K>(PhantomData<K>);
pub struct DbIterVal<V>(PhantomData<V>);
pub struct DbIterKeyVal<K,V>(PhantomData<(K,V)>);

pub struct DbIterator<'db, Item>
{
    iter: *mut ffi::rocksdb_iterator_t,

    first: bool,                // don't need advance

    db: PhantomData<&'db Db>,
    item: PhantomData<Item>,
}

impl<'db, Item> DbIterator<'db, Item>
{
    fn new(db: &'db Db, options: &'db ReadOptions) -> Self {
        let db = db.db();

        DbIterator {
            iter: unsafe { ffi::rocksdb_create_iterator(db.as_ptr(), options.options) },
            db: PhantomData,
            item: PhantomData,
            first: true,
        }
    }

    #[inline]
    pub fn valid(&self) -> bool {
        unsafe { ffi::rocksdb_iter_valid(self.iter) != 0 }
    }

    pub fn seek_first(&mut self) -> &mut Self {
        unsafe { ffi::rocksdb_iter_seek_to_first(self.iter) };
        self.first = true;
        self
    }

    pub fn seek_last(&mut self) -> &mut Self {
        unsafe { ffi::rocksdb_iter_seek_to_last(self.iter) }
        self
    }    

    pub fn seek_next(&mut self) -> &mut Self {
        if self.valid() {
            unsafe { ffi::rocksdb_iter_next(self.iter) }
        }
        self
    }    

    pub fn seek_prev(&mut self) -> &mut Self {
        if self.valid() {
            unsafe { ffi::rocksdb_iter_prev(self.iter) }
        }
        self
    }    
    
    pub fn seek<SK>(&mut self, key: &SK) -> &mut Self
        where SK: AsRef<[u8]>
    {
        let s = key.as_ref();
        
        unsafe { ffi::rocksdb_iter_seek(self.iter, s.as_ptr() as *const c_char, s.len() as size_t) }
        self.first = true;
        self
    }

    pub fn key<'it>(&'it mut self) -> Option<RawRef<'it, Self>> {
        if !self.valid() { return None }

        unsafe {
            let mut klen = 0;
            let kptr = ffi::rocksdb_iter_key(self.iter, &mut klen);
            
            Some(RawRef::new(kptr as *mut c_char, klen, self))
        }
    }

    pub fn value<'it>(&'it mut self) -> Option<RawRef<'it, Self>> {
        if !self.valid() { return None }

        unsafe {
            let mut klen = 0;
            let kptr = ffi::rocksdb_iter_value(self.iter, &mut klen);
            Some(RawRef::new(kptr as *mut c_char, klen, self))
        }
    }
}

impl<'db, Item> Drop for DbIterator<'db, Item>
{
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_iter_destroy(self.iter) }
    }
}

impl<'db, 'it, K> Iterator for DbIterator<'db, DbIterKey<K>>
    where K: From<RawRef<'it, DbIterator<'db, DbIterKey<K>>>> + 'it + 'db
{
    type Item=K;
    
    fn next(&'it mut self) -> Option<Self::Item> {
        if !self.first {
            self.seek_next();
        }

        self.first = false;
        self.key().map(Self::Item::from)
    }

    fn last(mut self) -> Option<Self::Item> {
        self.seek_last();
        self.first = false;
        self.key().map(Self::Item::from)
    }
}

/*
impl<'a,K> DoubleEndedIterator for DbIterator<'a,DbIterKey<K>>
    where K: From<RawRef<'a, DbIterator<'a,DbIterKey<K>>>> + 'a
{
    fn next_back<'b>(&'b mut self) -> Option<Self::Item> {
        self.seek_prev();
        self.first = false;
        self.key().map(Self::Item::from)
    }
}

impl<'a,V> Iterator for DbIterator<'a,DbIterVal<V>>
    where V: From<RawRef<'a, DbIterator<'a,DbIterVal<V>>>> + 'a
{
    type Item=V;
    
    fn next(&mut self) -> Option<V> {
        if !self.first {
            self.seek_next();
        }

        self.first = false;
        self.value().map(Self::Item::from)
    }

    fn last(mut self) -> Option<V> {
        self.seek_last();
        self.first = false;
        self.key().map(Self::Item::from)
    }
}

impl<'a,V> DoubleEndedIterator for DbIterator<'a,DbIterVal<V>>
    where V: From<RawBuf>
{
    fn next_back(&mut self) -> Option<V> {
        let ret = self.value();
        self.seek_prev();

        ret
    }
}

impl<'a> Iterator for DbIterator<'a,DbIterKeyVal<K,V>>
    where K: From<RawBuf>, V: From<RawBuf>
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

impl<'a, K, V> DoubleEndedIterator for DbIterator<'a,DbIterKeyVal<K,V>>
    where K: From<RawBuf>, V: From<RawBuf>
{
    fn next_back(&mut self) -> Option<(K,V)> {
        if self.valid() {
            let ret = (self.key().unwrap(), self.value().unwrap());
            self.seek_prev();

            Some(ret)
        } else {
            None
        }
    }
}
 */

pub struct WriteBatch {
    batch: *mut ffi::rocksdb_writebatch_t,
}

pub enum BatchIterItem<K, V>
{
    Put(K, V),
    Delete(K),
}

extern fn batch_iter_put_cb<K, V>(ptr: *mut c_void, key: *const c_char, klen: size_t, val: *const c_char, vallen: size_t)
    where K: From<RawBuf>, V: From<RawBuf>
{
    let ptr = ptr as *mut Vec<BatchIterItem<K,V>>;
    
    unsafe { 
        let mut vec = &mut *ptr;
        let ks = RawBuf::new(key as *mut c_char, klen);
        let vs = RawBuf::new(val as *mut c_char, vallen);
    
        vec.push(BatchIterItem::Put(K::from(ks), V::from(vs)));
    }
}

extern fn batch_iter_delete_cb<K, V>(ptr: *mut c_void, key: *const c_char, klen: size_t)
    where K: From<RawBuf>
{
    let ptr = ptr as *mut Vec<BatchIterItem<K,V>>;

    unsafe {
        let mut vec = &mut *ptr;
        let ks = RawBuf::new(key as *mut c_char, klen);
        
        vec.push(BatchIterItem::Delete(K::from(ks)));
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
        where K: AsRef<[u8]>, V: AsRef<[u8]>
    {
        let ks = key.as_ref();
        let vs = val.as_ref();

        unsafe {
            ffi::rocksdb_writebatch_put(self.batch,
                                        ks.as_ptr() as *const c_char, ks.len() as size_t,
                                        vs.as_ptr() as *const c_char, vs.len() as size_t)
        }        
    }

    pub fn put_cf<K, V>(&mut self, cf: &ColumnFamilyHandle, key: K, val: V)
        where K: AsRef<[u8]>, V: AsRef<[u8]>
    {
        let ks = key.as_ref();
        let vs = val.as_ref();

        unsafe {
            ffi::rocksdb_writebatch_put_cf(self.batch, cf.0,
                                           ks.as_ptr() as *const c_char, ks.len() as size_t,
                                           vs.as_ptr() as *const c_char, vs.len() as size_t)
        }        
    }

    pub fn putv<K, V, KI, VI>(&mut self, keys: KI, vals: VI)
        where K: AsRef<[u8]>, V: AsRef<[u8]>, KI: iter::IntoIterator<Item=K>, VI: iter::IntoIterator<Item=V>
    {
        let kss: (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();
        let vss: (Vec<_>, Vec<_>) = vals.into_iter()
            .map(|v| { let s = v.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            ffi::rocksdb_writebatch_putv(self.batch,
                                         kss.0.len() as c_int, kss.0.as_ptr(), kss.1.as_ptr(),
                                         vss.0.len() as c_int, vss.0.as_ptr(), vss.1.as_ptr())
        }
    }

    pub fn putv_cf<K, V, KI, VI>(&mut self, cf: &ColumnFamilyHandle, keys: KI, vals: VI)
        where K: AsRef<[u8]>, V: AsRef<[u8]>, KI: iter::IntoIterator<Item=K>, VI: iter::IntoIterator<Item=V>
    {
        let kss: (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();
        let vss: (Vec<_>, Vec<_>) = vals.into_iter()
            .map(|v| { let s = v.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            ffi::rocksdb_writebatch_putv_cf(self.batch, cf.0,
                                            kss.0.len() as c_int, kss.0.as_ptr(), kss.1.as_ptr(),
                                            vss.0.len() as c_int, vss.0.as_ptr(), vss.1.as_ptr())
        }
    }

    pub fn merge<K, V>(&mut self, key: K, val: V)
        where K: AsRef<[u8]>, V: AsRef<[u8]>
    {
        let ks = key.as_ref();
        let vs = val.as_ref();

        unsafe {
            ffi::rocksdb_writebatch_merge(self.batch,
                                          ks.as_ptr() as *const c_char, ks.len() as size_t,
                                          vs.as_ptr() as *const c_char, vs.len() as size_t)
        }        
    }

    pub fn merge_cf<K, V>(&mut self, cf: &ColumnFamilyHandle, key: K, val: V)
        where K: AsRef<[u8]>, V: AsRef<[u8]>
    {
        let ks = key.as_ref();
        let vs = val.as_ref();

        unsafe {
            ffi::rocksdb_writebatch_merge_cf(self.batch, cf.0,
                                             ks.as_ptr() as *const c_char, ks.len() as size_t,
                                             vs.as_ptr() as *const c_char, vs.len() as size_t)
        }        
    }

    pub fn mergev<K, V, KI, VI>(&mut self, keys: KI, vals: VI)
        where K: AsRef<[u8]>, V: AsRef<[u8]>, KI: iter::IntoIterator<Item=K>, VI: iter::IntoIterator<Item=V>
    {
        let kss: (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();
        let vss: (Vec<_>, Vec<_>) = vals.into_iter()
            .map(|v| { let s = v.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            ffi::rocksdb_writebatch_mergev(self.batch,
                                           kss.0.len() as c_int, kss.0.as_ptr(), kss.1.as_ptr(),
                                           vss.0.len() as c_int, vss.0.as_ptr(), vss.1.as_ptr())
        }
    }

    pub fn mergev_cf<K, V, KI, VI>(&mut self, cf: &ColumnFamilyHandle, keys: KI, vals: VI)
        where K: AsRef<[u8]>, V: AsRef<[u8]>, KI: iter::IntoIterator<Item=K>, VI: iter::IntoIterator<Item=V>
    {
        let kss: (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();
        let vss: (Vec<_>, Vec<_>) = vals.into_iter()
            .map(|v| { let s = v.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            ffi::rocksdb_writebatch_mergev_cf(self.batch, cf.0,
                                              kss.0.len() as c_int, kss.0.as_ptr(), kss.1.as_ptr(),
                                              vss.0.len() as c_int, vss.0.as_ptr(), vss.1.as_ptr())
        }
    }

    pub fn delete<K>(&mut self, key: K)
        where K: AsRef<[u8]>
    {
        let ks = key.as_ref();

        unsafe {
            ffi::rocksdb_writebatch_delete(self.batch,
                                           ks.as_ptr() as *const c_char, ks.len() as size_t)
        }        
    }

    pub fn delete_cf<K>(&mut self, cf: &ColumnFamilyHandle, key: K)
        where K: AsRef<[u8]>
    {
        let ks = key.as_ref();

        unsafe {
            ffi::rocksdb_writebatch_delete_cf(self.batch, cf.0,
                                              ks.as_ptr() as *const c_char, ks.len() as size_t)
        }        
    }

    pub fn deletev<K, KI>(&mut self, keys: KI)
        where K: AsRef<[u8]>, KI: iter::IntoIterator<Item=K>
    {
        let kss: (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            ffi::rocksdb_writebatch_deletev(self.batch,
                                            kss.0.len() as c_int, kss.0.as_ptr(), kss.1.as_ptr())
        }
    }

    pub fn deletev_cf<K, KI>(&mut self, cf: &ColumnFamilyHandle, keys: KI)
        where K: AsRef<[u8]>, KI: iter::IntoIterator<Item=K>
    {
        let kss: (Vec<_>, Vec<_>) = keys.into_iter()
            .map(|k| { let s = k.as_ref(); (s.as_ptr() as *const c_char, s.len() as size_t) }).unzip();

        unsafe {
            ffi::rocksdb_writebatch_deletev_cf(self.batch, cf.0,
                                               kss.0.len() as c_int, kss.0.as_ptr(), kss.1.as_ptr())
        }
    }

    pub fn put_log_data<V>(&mut self, blob: &V)
        where V: AsRef<[u8]>
    {
        let bs = blob.as_ref();

        unsafe {
            ffi::rocksdb_writebatch_put_log_data(self.batch, bs.as_ptr() as *const c_char, bs.len() as size_t)
        }
    }

    pub fn data(&self) -> Vec<u8> {
        unsafe {
            let mut len: size_t = 0;
            let ret = ffi::rocksdb_writebatch_data(self.batch, &mut len);

            let vec = slice::from_raw_parts(ret as *const u8, len as usize).to_vec();

            libc::free(ret as *mut c_void);

            vec
        }
    }

    pub fn iter<K, V>(&self) -> vec::IntoIter<BatchIterItem<K,V>>
        where K: From<RawBuf>, V: From<RawBuf>
    {
        let mut vec: Vec<_> = Vec::new();
        
        unsafe {
            ffi::rocksdb_writebatch_iterate(self.batch, mem::transmute(&mut vec),
                                            Some(batch_iter_put_cb::<K,V>), Some(batch_iter_delete_cb::<K,V>))
        }

        vec.into_iter()
    }
}

impl<K, V> iter::FromIterator<BatchIterItem<K,V>> for WriteBatch
    where K: From<RawBuf> + AsRef<[u8]>, V: From<RawBuf> + AsRef<[u8]>
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
    db: &'a DbInner,
}

impl<'a> Snapshot<'a> {
    pub fn new(db: &'a Db) -> Snapshot<'a> {
        let db = db.db();
        Snapshot {
            snap: unsafe { ffi::rocksdb_create_snapshot(db.as_ptr()) },
            db: db,
        }
    }
}

impl<'a> Drop for Snapshot<'a> {
    fn drop(&mut self) {
        unsafe { ffi::rocksdb_release_snapshot(self.db.as_ptr(), self.snap) }
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
        where K: AsRef<[u8]>
    {
        let ks = key.as_ref();
        
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

#[cfg(test)]
mod test {
    use ::Options;
    use ::{ReadOptions,WriteOptions};
    use std::collections::btree_set::BTreeSet;
    
    #[test]
    fn simple() {
        let dir = ::testdir();
        let db = Options::new()
            .error_if_exists(true)
            .create_if_missing(true)
            .open(dir.path()).unwrap();
        let wropt = WriteOptions::new();
        let rdopt = ReadOptions::new();
        
        db.put(&wropt, "foo", "bar").unwrap();
        assert_eq!(db.get(&rdopt, "foo"), Ok(Vec::from("bar")));
        assert_eq!(db.get(&rdopt, "foo"), Ok(String::from("bar")));
    }

    #[test]
    fn iter() {
        let dir = ::testdir();
        let db = Options::new()
            .error_if_exists(true)
            .create_if_missing(true)
            .open(dir.path()).unwrap();
        let wropt = WriteOptions::new();
        let rdopt = ReadOptions::new();

        let kset: BTreeSet<_> = vec!["foo","bar","blat"].into_iter().map(Vec::from).collect();
        for k in kset.iter() {
            db.put(&wropt, k, k).unwrap()
        }

        for k in kset.iter() {
            let v : Vec<_> = db.get(&rdopt, k).unwrap();
            assert_eq!(&v, k);
        }
        
        let kset2: BTreeSet<_> = db.iterator_key(&rdopt).seek_first().collect();
        assert_eq!(kset, kset2);

        let kset3: BTreeSet<_> = db.iterator_value(&rdopt).seek_first().collect();
        assert_eq!(kset, kset3);
    }
}
