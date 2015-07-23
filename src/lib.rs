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

pub use db::Db;
pub use options::{Options, CompactionFilter, CompactionFilterFactory, Comparator, MergeOperator, SliceTransform, AccessHint,
                  CompactionStyle, UniversalCompactionOptions, FifoCompactionOptions,
                  BlockBasedTableOptions, Compression, FilterPolicy, Cache, TableVersion, ChecksumType, IndexType};

#[derive(Debug)]
pub enum Error {
    Msg(&'static str),
    NotFound,
}

impl Error {
    /// Take ownership of malloc-allocated string
    fn new(str: *const c_char) -> Error {
        let slice = unsafe { CStr::from_ptr(str) };
        Error::Msg(str::from_utf8(slice.to_bytes()).unwrap())
    }

    fn notfound() -> Error { Error::NotFound }
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

pub type Result<T> = result::Result<T, Error>;
