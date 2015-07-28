//! Binding for rocksdb
//!
//! This crate is intended to be a complete binding for [RocksDB](http://rocksdb.org). It provides
//! access to the basic API, as well as:
//!
//! * Column Families
//! * Comparisons
//! * Compaction filter callbacks
//! * Compaction filter factories
//! * Complete set of Options
//! * Block based table options
//! * Compression
//!
//! Currently does not include Cuckoo Hash tables, merge operators or slice
//! transforms.
//!
//! It binds to RocksDB's C binding, so it is limited to what the C binding can do; there are some
//! limitations compared to the full C++ binding.
#![feature(box_raw)]            // for callbacks
#![feature(convert)]            // path to cstring
//#![warn(missing_docs)]

extern crate libc;

use libc::{c_char, c_void};
use std::ffi::CStr;
use std::error;
use std::fmt;
use std::str;
use std::result;

mod ffi;
pub mod db;
mod options;                    // not every pub thing in options should be exported

pub use db::{Db, ReadOptions, WriteOptions, RawBuf};
pub use options::{Options, CompactionFilter, Comparator, DefaultCompare, MergeOperator, SliceTransform, AccessHint,
                  CompactionStyle, UniversalCompactionOptions, FifoCompactionOptions, FilterFactory, Filter, FilterRes, CompactionFilterContext,
                  BlockBasedTableOptions, Compression, Cache, TableVersion, ChecksumType, IndexType};

#[derive(Debug,PartialEq,Eq,PartialOrd,Ord)]
/// All errors returned from RocksDB.
pub enum Error {
    /// An error returned from RocksDB as a descriptive string.
    Msg(&'static str),
    /// Key not found.
    NotFound,
}

impl Error {
    /// Take ownership of malloc-allocated string
    fn from_cptr(str: *const c_char) -> Error {
        let slice = unsafe { CStr::from_ptr(str) };
        Error::Msg(str::from_utf8(slice.to_bytes()).unwrap())
    }
}

impl Drop for Error {
    fn drop(&mut self) {
        match *self {
            Error::Msg(msg) => unsafe { libc::free(msg.as_ptr() as *mut c_void) },
            Error::NotFound => (),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match self {
            &Error::Msg(msg) => write!(fmt, "{}", msg),
            &Error::NotFound => write!(fmt, "key not found")
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            &Error::Msg(msg) => msg,
            &Error::NotFound => "key not found",
        }
    }
}

/// Results of RocksDB operations.
pub type Result<T> = result::Result<T, Error>;

#[cfg(test)]
extern crate tempdir;

#[cfg(test)]
fn testdir() -> tempdir::TempDir {
    tempdir::TempDir::new("test").unwrap()
}
