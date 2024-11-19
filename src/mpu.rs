// #![flux_rs::ignore] // comment this out to see a bunch of errors

#[allow(dead_code)]
use core::cell::UnsafeCell;
use core::fmt::Debug;
use core::marker::PhantomData;
use core::ops::Add;
use core::ops::{BitAnd, BitOr, BitOrAssign, Not, Shl, Shr};

#[flux_rs::sig(fn(x: bool[true]))]
pub fn assert(_x: bool) {}

// assoc reft bitval(v:Self) -> BitVec<32>
pub trait UIntLike:
    BitAnd<Output = Self>
    + BitOr<Output = Self>
    + BitOrAssign
    + Not<Output = Self>
    + Eq
    + Shr<usize, Output = Self>
    + Shl<usize, Output = Self>
    + Copy
    + Clone
    + Debug
{
    fn zero() -> Self;
}

// Helper macro for implementing the UIntLike trait on differrent
// types.
macro_rules! UIntLike_impl_for {
    ($type:ty) => {
        impl UIntLike for $type {
            fn zero() -> Self {
                0
            }
        }
    };
}

// UIntLike_impl_for!(u8);
// UIntLike_impl_for!(u16);
UIntLike_impl_for!(u32);
// UIntLike_impl_for!(u64);
// UIntLike_impl_for!(u128);
// UIntLike_impl_for!(usize);

/// Descriptive name for each register.
pub trait RegisterLongName {}

// Useful implementation for when no RegisterLongName is required
// (e.g. no fields need to be accessed, just the raw register values)
impl RegisterLongName for () {}

// ---------------- Field/FieldValue definitions -------------------

pub struct Field<T: UIntLike, R: RegisterLongName> {
    pub mask: T,
    pub shift: usize,
    associated_register: PhantomData<R>,
}

impl<T: UIntLike, R: RegisterLongName> Field<T, R> {
    pub const fn new(mask: T, shift: usize) -> Field<T, R> {
        Field {
            mask: mask,
            shift: shift,
            associated_register: PhantomData,
        }
    }

    #[inline]
    #[flux_rs::trusted]
    pub fn read(self, val: T) -> T {
        (val & (self.mask << self.shift)) >> self.shift
    }
}

impl<T: UIntLike, R: RegisterLongName> Clone for Field<T, R> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: UIntLike, R: RegisterLongName> Copy for Field<T, R> {}

macro_rules! Field_impl_for {
    ($type:ty) => {
        impl<R: RegisterLongName> Field<$type, R> {
            pub const fn val(&self, value: $type) -> FieldValue<$type, R> {
                FieldValue::<$type, R>::new(self.mask, self.shift, value)
            }
        }
    };
}

// Field_impl_for!(u8);
// Field_impl_for!(u16);
Field_impl_for!(u32);
// Field_impl_for!(u64);
// Field_impl_for!(u128);
// Field_impl_for!(usize);

#[derive(Copy, Clone)]
pub struct FieldValue<T: UIntLike, R: RegisterLongName> {
    mask: T,
    pub value: T,
    associated_register: PhantomData<R>,
}

macro_rules! FieldValue_impl_for {
    ($type:ty) => {
        // Necessary to split the implementation of new() out because the bitwise
        // math isn't treated as const when the type is generic.
        // Tracking issue: https://github.com/rust-lang/rfcs/pull/2632
        impl<R: RegisterLongName> FieldValue<$type, R> {
            pub const fn new(mask: $type, shift: usize, value: $type) -> Self {
                FieldValue {
                    mask: mask << shift,
                    value: (value & mask) << shift,
                    associated_register: PhantomData,
                }
            }
        }

        // Necessary to split the implementation of From<> out because of the orphan rule
        // for foreign trait implementation (see [E0210](https://doc.rust-lang.org/error-index.html#E0210)).
        impl<R: RegisterLongName> From<FieldValue<$type, R>> for $type {
            fn from(val: FieldValue<$type, R>) -> $type {
                val.value
            }
        }
    };
}

// FieldValue_impl_for!(u8);
// FieldValue_impl_for!(u16);
FieldValue_impl_for!(u32);
// FieldValue_impl_for!(u64);
// FieldValue_impl_for!(u128);
// FieldValue_impl_for!(usize);

impl<T: UIntLike, R: RegisterLongName> FieldValue<T, R> {
    #[inline]
    pub fn none() -> Self {
        Self {
            mask: T::zero(),
            value: T::zero(),
            associated_register: PhantomData,
        }
    }

    #[inline]
    pub fn read(&self, field: Field<T, R>) -> T {
        field.read(self.value)
    }
}

#[flux_rs::trusted]
impl<T: UIntLike, R: RegisterLongName> Add for FieldValue<T, R> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        FieldValue {
            mask: self.mask | rhs.mask,
            value: self.value | rhs.value,
            associated_register: PhantomData,
        }
    }
}

// -------------------- ReadWrite register definitions ----------------

#[repr(transparent)]
pub struct ReadWrite<T: UIntLike, R: RegisterLongName = ()> {
    value: UnsafeCell<T>,
    associated_register: PhantomData<R>,
}
impl<T: UIntLike, R: RegisterLongName> Readable for ReadWrite<T, R> {
    type T = T;
    type R = R;

    #[inline]
    fn get(&self) -> Self::T {
        unsafe { ::core::ptr::read_volatile(self.value.get()) }
    }
}
impl<T: UIntLike, R: RegisterLongName> Writeable for ReadWrite<T, R> {
    type T = T;
    type R = R;

    #[inline]
    fn set(&mut self, value: T) {
        unsafe { ::core::ptr::write_volatile(self.value.get(), value) }
    }
}

pub trait Readable {
    type T: UIntLike;
    type R: RegisterLongName;

    /// Get the raw register value
    fn get(&self) -> Self::T;

    #[inline]
    /// Read the value of the given field
    fn read(&self, field: Field<Self::T, Self::R>) -> Self::T {
        field.read(self.get())
    }
}

pub trait Writeable {
    type T: UIntLike;
    type R: RegisterLongName;

    /// Set the raw register value
    fn set(&mut self, value: Self::T);

    #[inline]
    /// Write the value of one or more fields, overwriting the other fields with zero
    fn write(&mut self, field: FieldValue<Self::T, Self::R>) {
        self.set(field.value);
    }
}

// ----------- Testing Harness ---------------

pub struct MpuRegisters {
    pub r1: ReadWrite<u32, ()>,
    pub r2: ReadWrite<u32, ()>,
}

impl MpuRegisters {
    fn new() -> Self {
        todo!()
    }
}

pub struct MPU {
    // regs: &'static mut MpuRegisters,
    regs: MpuRegisters,
}

impl MPU {
    #[flux_rs::trusted]
    pub fn new() -> Self {
        /* unsafe */
        {
            Self {
                regs: MpuRegisters::new(), // todo!(), &mut *(0x41414141 as *mut MpuRegisters),
            }
        }
    }
}

fn test_get_set() {
    let mut mpu = MPU::new();
    mpu.regs.r1.set(1);
    mpu.regs.r2.set(1);
    assert(mpu.regs.r1.get() == mpu.regs.r2.get());
    mpu.regs.r2.set(2);
    assert(mpu.regs.r1.get() != mpu.regs.r2.get());
}

fn test_read_write() {
    let mut mpu = MPU::new();
    mpu.regs.r1.set(1);
    let bit0_field = Field::new(0x00000001_u32, 0);
    let bit1_field = Field::new(0x00000001_u32, 1);
    let bit0 = mpu.regs.r1.read(bit0_field);
    let bit1 = mpu.regs.r1.read(bit1_field);
    assert(bit0 == 1);
    assert(bit1 == 0);

    mpu.regs.r1.write(bit0_field.val(1) + bit1_field.val(1));
    assert(mpu.regs.r1.get() == 3);
    assert(mpu.regs.r1.read(bit0_field) == 1);
    assert(mpu.regs.r1.read(bit1_field) == 1);

    /*
        mpu.regs.r1.get()               ==> mpu.regs_get_r1()                       // regs_get_rx(&self)
        mpu.regs.r1.set(val)            ==> mpu.regs_set_r2(val)                    // regs_set_rx(&mut self, val: u32)
        mpu.regs.r1.read(field)         ==> mpu.regs_read_r1_field(field)           // regs_read_rx_field(&self, field: Field<u32, R>)
        mpu.regs.r1.write(field_val)    ==> mpu.regs_write_r1_field_val(field_val)  // regs_write_rx_field_val(&mut self, field_val: FieldValue<u32, R>)
    */
}

fn main() {}
