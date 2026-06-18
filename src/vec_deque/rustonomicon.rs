use std::alloc::{self, Layout};
use std::marker::PhantomData;
use std::mem;
use std::ops::{Deref, DerefMut};
use std::ptr::{self, NonNull};

use crate::vec_deque::flux_specs::{flux_nonnull_new, flux_unsafe_expect};

#[flux_rs::refined_by(ptr:ptr, cap: int)]
#[flux_rs::invariant(ptr.size == cap && cap <= isize::MAX)]
struct RawVec<T> {
    #[flux_rs::field(NonNull<T>[ptr])]
    ptr: NonNull<T>,
    #[flux_rs::field(usize[cap])]
    cap: usize,
}

unsafe impl<T: Send> Send for RawVec<T> {}
unsafe impl<T: Sync> Sync for RawVec<T> {}

impl<T> RawVec<T> {
    #[flux_rs::spec(fn () -> RawVec<T>{v: v.cap == 0})]
    fn new() -> Self {
        // !0 is usize::MAX. This branch should be stripped at compile time.
        assert!(mem::size_of::<T>() != 0, "TODO:zst");
        // let cap = if mem::size_of::<T>() == 0 { !0 } else { 0 };
        let cap = 0;

        // `NonNull::dangling()` doubles as "unallocated" and "zero-sized allocation"
        RawVec {
            ptr: NonNull::dangling(),
            cap,
        }
    }

    #[flux_rs::opts(solver = "cvc5")] // bitvector specs in Layout seem to kill z3
    #[flux_rs::spec(fn (self: &mut RawVec<T>[@me]) ensures self: RawVec<T>{v: v.cap > me.cap})]
    fn grow(&mut self) {
        // since we set the capacity to usize::MAX when T has size 0,
        // getting to here necessarily means the Vec is overfull.
        assert!(mem::size_of::<T>() != 0, "capacity overflow");

        let (new_cap, new_layout) = if self.cap == 0 {
            (1, Layout::array::<T>(1))
        } else {
            // This can't overflow since self.cap <= isize::MAX.
            let new_cap = 2 * self.cap;
            (new_cap, Layout::array::<T>(new_cap))
        };

        // `Layout::array` checks that the number of bytes allocated is
        // in 1..=isize::MAX and will error otherwise.  An allocation of
        // 0 bytes isn't possible thanks to the above condition.
        let new_layout = flux_unsafe_expect(new_layout, "Allocation too large");

        let new_ptr = if self.cap == 0 {
            unsafe { alloc::alloc(new_layout) }
        } else {
            let old_layout = Layout::array::<T>(self.cap).unwrap();
            let old_ptr = self.ptr.as_ptr() as *mut u8;
            unsafe { alloc::realloc(old_ptr, old_layout, new_layout.size()) }
        };

        // If allocation fails, `new_ptr` will be null, in which case we abort.
        self.ptr = match flux_nonnull_new(new_ptr) {
            Some(p) => p,
            None => alloc::handle_alloc_error(new_layout),
        };
        self.cap = new_cap;
    }
}

impl<T> Drop for RawVec<T> {
    #[flux_rs::trusted]
    fn drop(&mut self) {
        let elem_size = mem::size_of::<T>();

        if self.cap != 0 && elem_size != 0 {
            unsafe {
                alloc::dealloc(
                    self.ptr.as_ptr() as *mut u8,
                    Layout::array::<T>(self.cap).unwrap(),
                );
            }
        }
    }
}

#[flux_rs::refined_by(raw:RawVec, len: int)]
#[flux_rs::invariant(len <= raw.cap)]
pub struct Vec<T> {
    #[flux_rs::field(RawVec<T>[raw])]
    buf: RawVec<T>,
    #[flux_rs::field(usize[len])]
    len: usize,
}

impl<T> Vec<T> {
    #[flux_rs::sig(fn (self: &Vec<T>[@me]) -> *mut{p: p.addr == p.base && p.size >= me.raw.cap} T)]
    fn ptr(&self) -> *mut T {
        self.buf.ptr.as_ptr()
    }

    #[flux_rs::sig(fn (self: &Vec<T>[@me]) -> usize[me.raw.cap])]
    fn cap(&self) -> usize {
        self.buf.cap
    }

    #[flux_rs::spec(fn () -> Vec<T>{v: v.len == 0 && v.raw.cap == 0})]
    pub fn new() -> Self {
        Vec {
            buf: RawVec::new(),
            len: 0,
        }
    }
    #[flux_rs::sig(fn (self: &strg Vec<T>[@me], elem: T) ensures self: Vec<T>)]
    pub fn push(&mut self, elem: T) {
        if self.len == self.cap() {
            self.buf.grow();
        }

        unsafe {
            ptr::write(self.ptr().add(self.len), elem);
        }

        // Can't overflow, we'll OOM first.
        self.len += 1;
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (self: &strg Vec<T>[@me]) -> Option<T> ensures self: Vec<T>)]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe { Some(ptr::read(self.ptr().add(self.len))) }
        }
    }

    #[flux_rs::sig(fn (self: &strg Vec<T>[@me], index: usize{index <= me.len}, elem: T) ensures self: Vec<T>)]
    pub fn insert(&mut self, index: usize, elem: T) {
        assert!(index <= self.len, "index out of bounds");
        if self.len == self.cap() {
            self.buf.grow();
        }

        unsafe {
            ptr::copy(
                self.ptr().add(index),
                self.ptr().add(index + 1),
                self.len - index,
            );
            ptr::write(self.ptr().add(index), elem);
        }

        self.len += 1;
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (self: &strg Vec<T>[@me], index: usize{index < me.len}) -> T ensures self: Vec<T>)]
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len, "index out of bounds");

        self.len -= 1;

        unsafe {
            let result = ptr::read(self.ptr().add(index));
            ptr::copy(
                self.ptr().add(index + 1),
                self.ptr().add(index),
                self.len - index,
            );
            result
        }
    }

    #[flux_rs::trusted]
    pub fn drain(&mut self) -> Drain<'_, T> {
        let iter = unsafe { RawValIter::new(&self) };

        // this is a mem::forget safety thing. If Drain is forgotten, we just
        // leak the whole Vec's contents. Also we need to do this *eventually*
        // anyway, so why not do it now?
        self.len = 0;

        Drain {
            iter,
            vec: PhantomData,
        }
    }
}

impl<T> Drop for Vec<T> {
    #[flux_rs::trusted]
    fn drop(&mut self) {
        while let Some(_) = self.pop() {}
        // deallocation is handled by RawVec
    }
}

impl<T> Deref for Vec<T> {
    type Target = [T];
    #[flux_rs::trusted]
    fn deref(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.ptr(), self.len) }
    }
}

#[flux_rs::ignore]
impl<T> DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr(), self.len) }
    }
}

impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    #[flux_rs::trusted]
    fn into_iter(self) -> IntoIter<T> {
        let (iter, buf) = unsafe { (RawValIter::new(&self), ptr::read(&self.buf)) };

        mem::forget(self);

        IntoIter { iter, _buf: buf }
    }
}

struct RawValIter<T> {
    start: *const T,
    end: *const T,
}

impl<T> RawValIter<T> {
    #[flux_rs::trusted]
    unsafe fn new(slice: &[T]) -> Self {
        RawValIter {
            start: slice.as_ptr(),
            end: if mem::size_of::<T>() == 0 {
                ((slice.as_ptr() as usize) + slice.len()) as *const _
            } else if slice.len() == 0 {
                slice.as_ptr()
            } else {
                unsafe { slice.as_ptr().add(slice.len()) }
            },
        }
    }
}

#[flux_rs::ignore]
impl<T> Iterator for RawValIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                if mem::size_of::<T>() == 0 {
                    self.start = (self.start as usize + 1) as *const _;
                    Some(ptr::read(NonNull::<T>::dangling().as_ptr()))
                } else {
                    let old_ptr = self.start;
                    self.start = self.start.offset(1);
                    Some(ptr::read(old_ptr))
                }
            }
        }
    }

    #[flux_rs::trusted]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let elem_size = mem::size_of::<T>();
        let len =
            (self.end as usize - self.start as usize) / if elem_size == 0 { 1 } else { elem_size };
        (len, Some(len))
    }
}

#[flux_rs::ignore]
impl<T> DoubleEndedIterator for RawValIter<T> {
    fn next_back(&mut self) -> Option<T> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                if mem::size_of::<T>() == 0 {
                    self.end = (self.end as usize - 1) as *const _;
                    Some(ptr::read(NonNull::<T>::dangling().as_ptr()))
                } else {
                    self.end = self.end.offset(-1);
                    Some(ptr::read(self.end))
                }
            }
        }
    }
}

pub struct IntoIter<T> {
    _buf: RawVec<T>, // we don't actually care about this. Just need it to live.
    iter: RawValIter<T>,
}

#[flux_rs::ignore]
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.iter.next()
    }
    #[flux_rs::trusted]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[flux_rs::ignore]
impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back()
    }
}

impl<T> Drop for IntoIter<T> {
    #[flux_rs::trusted]
    fn drop(&mut self) {
        for _ in &mut *self {}
    }
}

pub struct Drain<'a, T: 'a> {
    vec: PhantomData<&'a mut Vec<T>>,
    iter: RawValIter<T>,
}

#[flux_rs::ignore]
impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.iter.next()
    }
    #[flux_rs::trusted]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[flux_rs::ignore]
impl<'a, T> DoubleEndedIterator for Drain<'a, T> {
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back()
    }
}

impl<'a, T> Drop for Drain<'a, T> {
    #[flux_rs::trusted]
    fn drop(&mut self) {
        // pre-drain the iter
        for _ in &mut *self {}
    }
}
