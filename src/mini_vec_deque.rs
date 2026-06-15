//! Minimal extraction of VecDeque: push_front, push_back, pop_front, pop_back,
//! is_empty, len, get, get_mut, make_contiguous, clear — plus all helpers they need.

use core::mem::SizedTypeProperties;
use core::ops::{Range, RangeBounds};
use core::{ptr, slice};

use crate::alloc::{Allocator, Global};
use crate::raw_vec::RawVec;

#[cfg_attr(flux, flux::defs {

    fn wrping_add(a: int, b: int) -> int {
        (a + b) % (usize::MAX + 1)
    }

    fn wrping_sub(a: int, b: int) -> int {
        (a - b) % (usize::MAX + 1)
    }

    fn wrp_idx(idx: int, cap: int) -> int {
        if idx >= cap { idx - cap } else { idx }
    }

    fn wrp_sub(idx: int, sub: int, cap: int) -> int {
        wrp_idx(wrping_add(wrping_sub(idx, sub), cap), cap)
    }
})]
const _: () = ();

#[cfg_attr(flux, flux::refined_by(head: int, len: int, cap: int))]
#[cfg_attr(flux, flux::invariant(len <= isize::MAX ))]
#[cfg_attr(flux, flux::invariant(len <= cap))]
#[cfg_attr(flux, flux::invariant(head <= cap && (cap == 0 || head < cap)))]
pub struct VecDeque<
    T,
    A: Allocator = Global,
> {
    #[cfg_attr(flux, flux::field(usize[head]))]
    head: usize,
    #[cfg_attr(flux, flux::field(usize[len]))]
    len: usize,
    #[cfg_attr(flux, flux::field(RawVec<T, A>[cap]))]
    buf: RawVec<T, A>,
}

// ---------------------------------------------------------------------------
// Free function
// ---------------------------------------------------------------------------

#[inline]
#[cfg_attr(flux, flux::spec(fn(lidx: usize, cap: usize) -> usize[wrp_idx(lidx, cap)]
    requires (lidx == 0 && cap == 0) || lidx < cap || (lidx - cap) < cap
))]
fn wrap_index(logical_index: usize, capacity: usize) -> usize {
    debug_assert!(
        (logical_index == 0 && capacity == 0)
            || logical_index < capacity
            || (logical_index - capacity) < capacity
    );
    if logical_index >= capacity {
        logical_index - capacity
    } else {
        logical_index
    }
}

// ---------------------------------------------------------------------------
// Inherent helpers (on VecDeque<T, A>)
// ---------------------------------------------------------------------------

impl<T, A: Allocator> VecDeque<T, A> {
    #[inline]
    fn ptr(&self) -> *mut T {
        self.buf.ptr()
    }

    /// # Safety
    ///
    /// May only be called if `off < self.capacity()`.
    #[inline]
    #[cfg_attr(flux, flux::spec(fn(s : &mut Self[@slf], off: usize, value: T) -> &mut T requires off < slf.cap ensures s : Self[slf]))]
    unsafe fn buffer_write(&mut self, off: usize, value: T) -> &mut T {
        unsafe {
            let ptr = self.ptr().add(off);
            ptr::write(ptr, value);
            &mut *ptr
        }
    }

    #[inline]
    unsafe fn buffer_read(&mut self, off: usize) -> T {
        unsafe { ptr::read(self.ptr().add(off)) }
    }

    /// Returns a slice pointer into the buffer.
    /// `range` must lie inside `0..self.capacity()`.
    #[inline]
    unsafe fn buffer_range(&self, range: Range<usize>) -> *mut [T] {
        unsafe {
            ptr::slice_from_raw_parts_mut(self.ptr().add(range.start), range.end - range.start)
        }
    }

    #[inline]
    fn is_full(&self) -> bool {
        self.len == self.capacity()
    }

    #[inline]
    #[cfg_attr(flux, flux::spec(fn(&Self[@slf], idx: usize, addend: usize) -> usize{ v : v < slf.cap }
        requires idx + addend < slf.cap || idx + addend - slf.cap < slf.cap
    ))]
    fn wrap_add(&self, idx: usize, addend: usize) -> usize {
        wrap_index(idx.wrapping_add(addend), self.capacity())
    }

    #[inline]
    #[cfg_attr(flux, flux::spec(fn(&Self[@slf], idx: usize) -> usize{ v : v < slf.cap }
        requires slf.head + idx < slf.cap || slf.head + idx - slf.cap < slf.cap
    ))]
    fn to_physical_idx(&self, idx: usize) -> usize {
        self.wrap_add(self.head, idx)
    }

    #[inline]
    #[cfg_attr(flux, flux::spec(fn(&Self[@slf], idx: usize, sub: usize) -> usize[wrp_sub(idx, sub, slf.cap)]
        requires wrping_add(wrping_sub(idx, sub), slf.cap) < slf.cap || wrping_sub(idx, sub) < slf.cap
    ))]
    fn wrap_sub(&self, idx: usize, subtrahend: usize) -> usize {
        wrap_index(
            idx.wrapping_sub(subtrahend).wrapping_add(self.capacity()),
            self.capacity(),
        )
    }

    #[inline]
    unsafe fn copy(&mut self, src: usize, dst: usize, len: usize) {
        debug_assert!(
            dst + len <= self.capacity(),
            "cpy dst={} src={} len={} cap={}",
            dst, src, len, self.capacity()
        );
        debug_assert!(
            src + len <= self.capacity(),
            "cpy dst={} src={} len={} cap={}",
            dst, src, len, self.capacity()
        );
        unsafe {
            ptr::copy(self.ptr().add(src), self.ptr().add(dst), len);
        }
    }

    #[inline]
    unsafe fn copy_nonoverlapping(&mut self, src: usize, dst: usize, len: usize) {
        debug_assert!(
            dst + len <= self.capacity(),
            "cno dst={} src={} len={} cap={}",
            dst, src, len, self.capacity()
        );
        debug_assert!(
            src + len <= self.capacity(),
            "cno dst={} src={} len={} cap={}",
            dst, src, len, self.capacity()
        );
        unsafe {
            ptr::copy_nonoverlapping(self.ptr().add(src), self.ptr().add(dst), len);
        }
    }

    #[inline]
    #[cfg_attr(flux, flux::trusted(reason = "foo"))]
    #[cfg_attr(flux, flux::spec(fn(s: &mut Self[@slf], old_capacity: usize) ensures s : Self[slf]))]
    unsafe fn handle_capacity_increase(&mut self, old_capacity: usize) {
        let new_capacity = self.capacity();
        debug_assert!(new_capacity >= old_capacity);

        if self.head <= old_capacity - self.len {
            // Nop
        } else {
            let head_len = old_capacity - self.head;
            let tail_len = self.len - head_len;
            if head_len > tail_len && new_capacity - old_capacity >= tail_len {
                unsafe {
                    self.copy_nonoverlapping(0, old_capacity, tail_len);
                }
            } else {
                let new_head = new_capacity - head_len;
                unsafe {
                    let h = self.head;
                    self.copy(h, new_head, head_len);
                }
                self.head = new_head;
            }
        }
        debug_assert!(self.head < self.capacity() || self.capacity() == 0);
    }

    #[inline(never)]
    #[cfg_attr(flux, flux::trusted(reason = "capacity growth relies on allocator behavior"))]
    fn grow(&mut self) {
        debug_assert!(self.is_full());
        let old_cap = self.capacity();
        self.buf.grow_one();
        unsafe {
            self.handle_capacity_increase(old_cap);
        }
        debug_assert!(!self.is_full());
    }

    #[inline]
    fn is_contiguous(&self) -> bool {
        self.head <= self.capacity() - self.len
    }

    #[cfg_attr(flux, flux::trusted(reason = "wrap-around index arithmetic"))]
    fn slice_ranges<R>(&self, range: R, len: usize) -> (Range<usize>, Range<usize>)
    where
        R: RangeBounds<usize>,
    {
        let Range { start, end } = slice::range(range, ..len);
        let len = end - start;

        if len == 0 {
            (0..0, 0..0)
        } else {
            let wrapped_start = self.to_physical_idx(start);
            let head_len = self.capacity() - wrapped_start;

            if head_len >= len {
                (wrapped_start..wrapped_start + len, 0..0)
            } else {
                let tail_len = len - head_len;
                (wrapped_start..self.capacity(), 0..tail_len)
            }
        }
    }

    // -----------------------------------------------------------------------
    // Public: capacity
    // -----------------------------------------------------------------------

    #[inline]
    #[cfg_attr(flux, flux::trusted(reason = "not dealing with zero width types yet"))]
    #[cfg_attr(flux, flux::spec(fn(&Self[@slf]) -> usize[slf.cap]))]
    pub fn capacity(&self) -> usize {
        if T::IS_ZST {
            usize::MAX
        } else {
            self.buf.capacity()
        }
    }

    // -----------------------------------------------------------------------
    // Public: as_slices / as_mut_slices (needed by truncate / make_contiguous)
    // -----------------------------------------------------------------------

    #[inline]
    pub fn as_slices(&self) -> (&[T], &[T]) {
        let (a_range, b_range) = self.slice_ranges(.., self.len);
        unsafe { (&*self.buffer_range(a_range), &*self.buffer_range(b_range)) }
    }

    #[inline]
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        let (a_range, b_range) = self.slice_ranges(.., self.len);
        unsafe {
            (
                &mut *self.buffer_range(a_range),
                &mut *self.buffer_range(b_range),
            )
        }
    }

    // -----------------------------------------------------------------------
    // Public: the 10 target methods
    // -----------------------------------------------------------------------

    /// Returns the number of elements in the deque.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the deque is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Provides a reference to the element at the given index.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            let idx = self.to_physical_idx(index);
            unsafe { Some(&*self.ptr().add(idx)) }
        } else {
            None
        }
    }

    /// Provides a mutable reference to the element at the given index.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len {
            let idx = self.to_physical_idx(index);
            unsafe { Some(&mut *self.ptr().add(idx)) }
        } else {
            None
        }
    }

    /// Shortens the deque, keeping the first `len` elements and dropping the rest.
    #[cfg_attr(flux, flux::trusted(reason = "drop/copy logic relies on pointer reasoning ICE"))]
    pub fn truncate(&mut self, len: usize) {
        struct Dropper<'a, T>(&'a mut [T]);

        impl<'a, T> Drop for Dropper<'a, T> {
            fn drop(&mut self) {
                unsafe {
                    ptr::drop_in_place(self.0);
                }
            }
        }

        unsafe {
            if len >= self.len {
                return;
            }

            let (front, back) = self.as_mut_slices();
            if len > front.len() {
                let begin = len - front.len();
                let drop_back = back.get_unchecked_mut(begin..) as *mut _;
                self.len = len;
                ptr::drop_in_place(drop_back);
            } else {
                let drop_back = back as *mut _;
                let drop_front = front.get_unchecked_mut(len..) as *mut _;
                self.len = len;

                let _back_dropper = Dropper(&mut *drop_back);
                ptr::drop_in_place(drop_front);
            }
        }
    }

    /// Clears the deque, removing all values.
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
        self.head = 0;
    }

    /// Removes the first element and returns it, or `None` if the deque is empty.
    #[cfg_attr(flux, flux::trusted(reason = "updates to head/len rely on pointer invariants"))]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            let old_head = self.head;
            self.head = self.to_physical_idx(1);
            self.len -= 1;
            unsafe {
                core::hint::assert_unchecked(self.len < self.capacity());
                Some(self.buffer_read(old_head))
            }
        }
    }

    /// Removes the last element from the deque and returns it, or `None` if it is empty.
    #[cfg_attr(flux, flux::trusted(reason = "updates to head/len rely on pointer invariants"))]
    pub fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            self.len -= 1;
            unsafe {
                core::hint::assert_unchecked(self.len < self.capacity());
                Some(self.buffer_read(self.to_physical_idx(self.len)))
            }
        }
    }

    /// Prepends an element to the deque.
    pub fn push_front(&mut self, value: T) {
        let _ = self.push_front_mut(value);
    }

    /// Prepends an element to the deque, returning a reference to it.
    #[cfg_attr(flux, flux::trusted(reason = "capacity and index reasoning relies on pointer invariants"))]
    pub fn push_front_mut(&mut self, value: T) -> &mut T {
        if self.is_full() {
            self.grow();
        }

        self.head = self.wrap_sub(self.head, 1);
        self.len += 1;
        unsafe { self.buffer_write(self.head, value) }
    }

    /// Appends an element to the back of the deque.
    pub fn push_back(&mut self, value: T) {
        let _ = self.push_back_mut(value);
    }

    /// Appends an element to the back of the deque, returning a reference to it.
    #[cfg_attr(flux, flux::trusted(reason = "capacity and index reasoning relies on pointer invariants"))]
    pub fn push_back_mut(&mut self, value: T) -> &mut T {
        if self.is_full() {
            self.grow();
        }

        let len = self.len;
        self.len += 1;
        unsafe { self.buffer_write(self.to_physical_idx(len), value) }
    }

    /// Rearranges the internal storage so it is one contiguous slice, which is then returned.
    #[cfg_attr(flux, flux::trusted(reason = "buffer re-layout relies on raw pointer reasoning"))]
    pub fn make_contiguous(&mut self) -> &mut [T] {
        if T::IS_ZST {
            self.head = 0;
        }

        if self.is_contiguous() {
            unsafe { return slice::from_raw_parts_mut(self.ptr().add(self.head), self.len) }
        }

        let &mut Self { head, len, .. } = self;
        let ptr = self.ptr();
        let cap = self.capacity();

        let free = cap - len;
        let head_len = cap - head;
        let tail = len - head_len;
        let tail_len = tail;

        if free >= head_len {
            unsafe {
                self.copy(0, head_len, tail_len);
                self.copy_nonoverlapping(head, 0, head_len);
            }
            self.head = 0;
        } else if free >= tail_len {
            unsafe {
                self.copy(head, tail, head_len);
                self.copy_nonoverlapping(0, tail + head_len, tail_len);
            }
            self.head = tail;
        } else {
            if head_len > tail_len {
                unsafe {
                    if free != 0 {
                        self.copy(0, free, tail_len);
                    }
                    let slice = &mut *self.buffer_range(free..self.capacity());
                    slice.rotate_left(tail_len);
                    self.head = free;
                }
            } else {
                unsafe {
                    if free != 0 {
                        self.copy(self.head, tail_len, head_len);
                    }
                    let slice = &mut *self.buffer_range(0..self.len);
                    slice.rotate_right(head_len);
                    self.head = 0;
                }
            }
        }

        unsafe { slice::from_raw_parts_mut(ptr.add(self.head), self.len) }
    }
}

// ---------------------------------------------------------------------------
// Constructors for VecDeque<T> (Global allocator)
// ---------------------------------------------------------------------------

impl<T> VecDeque<T> {
    /// Creates an empty deque.
    #[inline]
    pub const fn new() -> VecDeque<T> {
        VecDeque {
            head: 0,
            len: 0,
            buf: RawVec::new(),
        }
    }

    /// Creates an empty deque with space for at least `capacity` elements.
    #[inline]
    pub fn with_capacity(capacity: usize) -> VecDeque<T> {
        Self::with_capacity_in(capacity, Global)
    }
}

// ---------------------------------------------------------------------------
// Constructors for VecDeque<T, A> (custom allocator)
// ---------------------------------------------------------------------------

impl<T, A: Allocator> VecDeque<T, A> {
    /// Creates an empty deque.
    #[inline]
    pub const fn new_in(alloc: A) -> VecDeque<T, A> {
        VecDeque {
            head: 0,
            len: 0,
            buf: RawVec::new_in(alloc),
        }
    }

    /// Creates an empty deque with space for at least `capacity` elements.
    #[cfg_attr(flux, flux::spec(fn(capacity: usize, alloc: A) -> Self[0, 0, capacity]))]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> VecDeque<T, A> {
        VecDeque {
            head: 0,
            len: 0,
            buf: RawVec::with_capacity_in(capacity, alloc),
        }
    }
}
