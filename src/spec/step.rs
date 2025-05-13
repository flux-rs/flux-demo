use flux_rs::attrs::*;
use std::iter::Step;

#[extern_spec(core::ops)]
#[reft(
    fn can_step_forward(start: Self, count: int) -> bool;
    fn step_forward(start: Self, count: int) -> Self;
    fn size(lo: Self, hi: Self) -> int;
)]
trait Step {}

#[extern_spec(std::iter)]
#[reft(
    fn can_step_forward(start: int, count: int) -> bool  { true }
    fn step_forward(start: int, count: int) -> int { start + count }
    fn size(lo: int, hi: int) -> int { hi - lo }
)]
impl Step for usize {}

#[extern_spec(std::iter)]
#[reft(
    fn can_step_forward(start: int, count: int) -> bool  { true }
    fn step_forward(start: int, count: int) -> int { start + count }
    fn size(lo: int, hi: int) -> int { hi - lo }
)]
impl Step for i32 {}
