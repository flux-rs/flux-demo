use std::{
    alloc::{AllocError, Allocator, Layout, alloc, realloc},
    marker::PointeeSized,
    ptr::{NonNull, Unique},
};

flux_rs::defs! {
    fn aligned_to(addr: int, align: int) -> bool {
        addr % align == 0
    }
}

#[flux_rs::extern_spec(core::ptr)]
#[flux_rs::refined_by(ptr:ptr)]
struct Unique<T>;

#[flux_rs::extern_spec(core::ptr)]
impl<T> Unique<T> {
    #[flux_rs::spec(fn (self: Unique<T>[@ptr]) -> *mut[ptr] T)]
    fn as_ptr(self) -> *mut T;
}

#[flux_rs::extern_spec(core::ptr)]
impl<T: Sized> Unique<T> {
    #[flux_rs::spec(fn () -> Unique<T>{v: v.ptr.addr == v.ptr.base && v.ptr.size == 0 && aligned_to(v.ptr.addr, T::align_of()) && aligned_to(T::size_of(), T::align_of()) && v.ptr.addr > 0})]
    fn dangling() -> Self;
}

// #[flux_rs::extern_spec(core::ptr)]
// impl<T: PointeeSized> Unique<T> {
//     #[flux_rs::spec(fn (ptr: *mut[@base, @addr, @size] T) -> Unique<T>[base, addr, size])]
//     unsafe fn new_unchecked(ptr: *mut T) -> Self;
// }

// #[flux_rs::extern_spec(core::ptr)]
// #[flux_rs::refined_by(ptr: ptr)]
// #[flux_rs::invariant(ptr.addr == ptr.base)]
// struct NonNull<T>;

#[flux_rs::extern_spec(core::ptr)]
impl<T> NonNull<T> {
    // #[flux_rs::spec(fn (self: NonNull<T>[@ptr]) -> *mut[ptr] T)]
    // fn as_ptr(self) -> *mut T;

    #[flux_rs::spec(fn (self: NonNull<T>[@ptr]) -> NonNull<U>[ptr])]
    fn cast<U>(self) -> NonNull<U>;
}

#[flux_rs::extern_spec(core::ptr)]
impl<T: Sized> NonNull<T> {
    #[flux_rs::spec(fn () -> NonNull<T>{v: v.addr == v.base && v.size == 0 && v.addr > 0 && aligned_to(v.addr, T::align_of()) && aligned_to(T::size_of(), T::align_of()) })]
    fn dangling() -> NonNull<T>;
}

#[flux_rs::extern_spec(core::alloc)]
#[flux_rs::spec(fn (layout: Layout) -> *mut{p: p.addr == p.base && p.size == layout.size} u8)]
unsafe fn alloc(layout: Layout) -> *mut u8;

#[flux_rs::extern_spec(core::alloc)]
#[flux_rs::spec(fn (ptr: *mut u8, layout: Layout, new_size: usize) -> *mut{p: p.addr == p.base && p.size == new_size} u8)]
unsafe fn realloc(ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8;

#[flux_rs::extern_spec(core::alloc)]
trait Allocator {
    #[flux_rs::spec(fn (&Self, layout: Layout) -> Result<NonNull<[u8]>{v: v.addr == v.base}, AllocError>)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    #[flux_rs::spec(fn (&Self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> Result<NonNull<[u8]>, AllocError>)]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>;

    #[flux_rs::spec(fn (&Self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout)
      -> Result<NonNull<[u8]>{v: v.addr == v.base}, AllocError>)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>;
}

#[flux_rs::trusted(reason = "extern spec")]
#[flux_rs::spec(fn (*mut[@ptr] T) -> Unique<T>[ptr] requires ptr.addr == ptr.base)]
pub fn flux_todo_unique_new_unchecked<T>(ptr: *mut T) -> Unique<T> {
    unsafe { Unique::new_unchecked(ptr) }
}

// A version of `expect` for `Result` types, that does not check the Ok precondition!
pub fn flux_unsafe_expect<T, E>(result: Result<T, E>, msg: &str) -> T {
    match result {
        Ok(value) => value,
        Err(_) => panic!("Expected Ok, but got Err: {}", msg),
    }
}

#[flux_rs::trusted(reason = "extern spec for NonNull::new, todo: cast")]
#[flux_rs::spec(fn (*mut[@ptr] u8) -> Option<NonNull<T>{v: v.addr == ptr.addr && v.base == ptr.base && v.size == ptr.size && v.addr > 0 && v.addr % T::align_of() == 0}>)]
pub fn flux_nonnull_new<T>(ptr: *mut u8) -> Option<NonNull<T>> {
    NonNull::new(ptr as *mut T)
}

#[flux_rs::extern_spec(core::slice)]
#[flux_rs::spec(fn (*const [@ptr] T, len: usize) -> &[T] requires len <= ptr.size)] // TODO: alignment, init, overflow: len * T::size_of() <= isize::MAX
unsafe fn from_raw_parts<'a, T>(data: *const T, len: usize) -> &'a [T];

#[flux_rs::extern_spec(core::ptr)]
#[flux_rs::spec(fn (*const [@src] T, *mut[@dst] T, count: usize) requires count <= src.size && count <= dst.size)] // TODO: alignment, init, overflow: len * T::size_of() <= isize::MAX
unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize);
