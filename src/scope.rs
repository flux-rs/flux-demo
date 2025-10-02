use std::alloc::Allocator;
use std::alloc::Global;
use std::ops::Deref;
use std::rc::Rc;

use crate::rvec::RVec;
use crate::rvec::rvec;
use flux_rs::assert;
use flux_rs::attrs::*;

fn test(){
    let x = 1;
    let y = 2;
    assert(x + x == x);
}

type Id = String;

#[derive(Clone, Copy)]
enum Op {
    Add,
    Sub,
    Mul,
}

/*
// #[refined_by(imm: bool, anf: bool)]
// #[invariant(imm => anf)]
// enum Exp0 {
//     // variables: x, y, z, ...
//     #[variant((String) -> Exp0[{imm: true, anf: true}])]
//     Var(String),

//     // numbers: 0, 1, 2, ...
//     #[variant((i32) -> Exp0[{imm: true, anf: true}])]
//     Num(i32),

//     // numbers: 0, 1, 2, ...
//     #[variant((Op, Box<Exp0[@e1]>, Box<Exp0[@e2]>) -> Exp0[{imm: false, anf: e1.imm && e2.imm}])]
//     Bin(Op, Box<Exp0>, Box<Exp0>),

//     #[variant((Id, Box<Exp0[@e1]>, Box<Exp0[@e2]>) -> Exp0[{imm: false, anf: e1.anf && e2.anf}])]
//     Let(Id, Box<Exp0>, Box<Exp0>),
// }

// // subset of Exp that are in ANF
// #[alias(type Anf = Exp0{e: e.anf})]
// type Anf = Exp0;

// // subset of Exp that are IMM
// #[alias(type Imm = Exp0{e: e.imm})]
// type Imm = Exp0;

// //---------------------------------------------------------------------------------------

// fn var(s: &str) -> Imm {
//     Exp0::Var(s.to_string())
// }

// fn num(n: i32) -> Imm {
//     Exp0::Num(n)
// }

// #[spec(fn(_, e1: Exp0, e2: Exp0) -> Exp0[{imm: false, anf: e1.anf && e2.anf}])]
// fn let_(id: &str, e1: Exp0, e2: Exp0) -> Exp0 {
//     Exp0::Let(id.to_string(), Box::new(e1), Box::new(e2))
// }

// #[spec(fn(Op, e1:Exp0, e2: Exp0) -> Exp0[{imm: false, anf: e1.imm && e2.imm}])]
// fn bin(op: Op, e1: Exp0, e2: Exp0) -> Exp0 {
//     Exp0::Bin(op, Box::new(e1), Box::new(e2))
// }

// //---------------------------------------------------------------------------------------

// // ((2 + 3) * (12 - 4)) * (7 + 8)
// fn exp0() -> Exp0 {
//     bin(
//         Op::Mul,
//         bin(
//             Op::Mul,
//             bin(Op::Add, num(2), num(3)),
//             bin(Op::Sub, num(12), num(4)),
//         ),
//         bin(Op::Add, num(7), num(8)),
//     )
// }

// // let x = 2 + 3 in (x + 4)
// fn exp1() -> Anf {
//     let_(
//         "x",
//         bin(Op::Add, num(2), num(3)),
//         bin(Op::Add, var("x"), num(4)),
//     )
// }

// //---------------------------------------------------------------------------------------

// fn fresh_id(count: &mut usize) -> Id {
//     let name = format!("?tmp{}", count);
//     *count += 1;
//     name.to_string()
// }

// impl Exp0 {
//     #[spec(fn(&Exp0[@e]) -> bool[e.imm])]
//     fn is_imm(&self) -> bool {
//         match self {
//             Exp0::Var(_) => true,
//             Exp0::Num(_) => true,
//             Exp0::Bin(_, e1, e2) => false,
//             Exp0::Let(_, e1, e2) => false,
//         }
//     }

//     #[spec(fn(&Exp0[@e]) -> bool[e.anf])]
//     fn is_anf(&self) -> bool {
//         match self {
//             Exp0::Var(_) => true,
//             Exp0::Num(_) => true,
//             Exp0::Bin(_, e1, e2) => e1.is_imm() && e2.is_imm(),
//             Exp0::Let(_, e1, e2) => e1.is_anf() && e2.is_anf(),
//         }
//     }

//     fn to_imm(&self, count: &mut usize, binds: &mut RVec<(Id, Anf)>) -> Imm {
//         match self {
//             Exp0::Var(x) => var(x),
//             Exp0::Num(n) => num(*n),
//             Exp0::Bin(op, e1, e2) => {
//                 let v1 = e1.to_imm(count, binds);
//                 let v2 = e2.to_imm(count, binds);
//                 let tmp = fresh_id(count);
//                 binds.push((tmp.clone(), bin(*op, v1, v2)));
//                 Exp0::Var(tmp)
//             }
//             Exp0::Let(x, e1, e2) => {
//                 let a = self.to_anf(count);
//                 let tmp = fresh_id(count);
//                 binds.push((tmp.clone(), a));
//                 Exp0::Var(tmp)
//             }
//         }
//     }

//     fn to_anf(&self, count: &mut usize) -> Anf {
//         match self {
//             Exp0::Var(x) => var(x),
//             Exp0::Num(n) => num(*n),
//             Exp0::Let(x, e1, e2) => {
//                 let e1 = e1.to_anf(count);
//                 let e2 = e2.to_anf(count);
//                 let_(x, e1, e2)
//             }
//             Exp0::Bin(op, e1, e2) => {
//                 let mut binds = rvec![];
//                 let v1 = e1.to_imm(count, &mut binds);
//                 let v2 = e2.to_imm(count, &mut binds);
//                 let mut res = bin(*op, v1, v2);
//                 while !binds.is_empty() {
//                     let (x, a) = binds.pop();
//                     res = let_(&x, a, res);
//                 }
//                 res
//             }
//         }
//     }
// }

// fn test_anf(e: &Exp0) {
//     let res = e.to_anf(&mut 0);
//     assert(res.is_anf());
// }

*/

//---------------------------------------------------------------------------------------

// RECAP: impossible

#[spec(fn() -> _ requires false)]
fn impossible() -> ! {
    panic!("impossible case")
}

fn test_impossible() {
    if 1 == 3 {
        impossible();
    }
}

// Environments

// A type for values
type Val = i32;


#[extern_spec]
#[refined_by(inner: T)]
struct Rc<T, A: Allocator = Global>;

#[extern_spec]
impl<T, A: Allocator> Deref for Rc<T, A> {
    #[spec(fn (&Self[@me]) -> &T[me.inner])]
    fn deref(&self) -> &T;
}

#[extern_spec]
impl<T, A: Allocator + Clone> Clone for Rc<T, A> {
    #[spec(fn (&Self[@me]) -> Self[me.inner])]
    fn clone(&self) -> Self;
}



#[extern_spec]
impl<T> Rc<T> {
    #[spec(fn(T[@a]) -> Self[a])]
    fn new(value: T) -> Self;
}

#[extern_spec]
#[flux::refined_by(val: str)]
struct String;

#[extern_spec]
impl Clone for String {
    #[spec(fn (&String[@s]) -> String[s])]
    fn clone(&self) -> Self;
}

#[extern_spec]
impl PartialEq for String {
    #[spec(fn(&String[@x], &String[@y]) -> bool[x == y])]
    fn eq(&self, other: &String) -> bool;
}

#[refined_by(binds: Set<String>)]
enum Env {
    #[variant(Env[set_emp()])]
    Empty,

    #[variant((Id[@x], Val, Rc<Env>[@env]) -> Env[set_add(x, env.inner)])]
    Bind(Id, Val, Rc<Env>),
}


/// Look up the value of a variable in an environment

#[spec(fn(&Env[@env], &String[@x]) -> Val requires set_is_in(x, env))]
fn lookup(env: &Env, x: &String) -> Val {
    match env {
        Env::Bind(y, v, env1) => {
            if *x == *y {
                *v
            } else {
                lookup(env1, x)
            }
        }
        Env::Empty => impossible(),
    }
}


#[refined_by(free: Set<String>)]
enum Exp1 {
    /// variables: x, y, z, ...
    #[variant((String[@x]) -> Exp1[set_singleton(x)])]
    Var(String),

    /// numbers: 0, 1, 2, ...
    #[variant((i32) -> Exp1[set_emp()])]
    Num(i32),

    /// numbers: 0, 1, 2, ...
    #[variant((Op, Box<Exp1[@e1]>, Box<Exp1[@e2]>) -> Exp1[set_union(e1.free, e2.free)])]
    Bin(Op, Box<Exp1>, Box<Exp1>),

    /// let x = e1 in e2
    #[variant((Id[@x], Box<Exp1[@e1]>, Box<Exp1[@e2]>) -> Exp1[set_union(e1.free, set_del(x, e2.free))])]
    Let(Id, Box<Exp1>, Box<Exp1>),
}

fn eval_op(op: Op, v1: Val, v2: Val) -> Val {
    match op {
        Op::Add => v1 + v2,
        Op::Sub => v1 - v2,
        Op::Mul => v1 * v2,
    }
}

impl Exp1 {
    #[spec(fn(&Exp1[@e], &Rc<Env>[@env]) -> Val requires set_subset(e.free, env.inner))]
    fn eval(&self, env: &Rc<Env>) -> Val {
        match self {
            Exp1::Num(n) => *n,
            Exp1::Var(x) => lookup(&env, x),
            Exp1::Bin(op, e1, e2) => {
                let v1 = e1.eval(env);
                let v2 = e2.eval(env);
                eval_op(*op, v1, v2)
            }
            Exp1::Let(x, e1, e2) => {
                let v1 = e1.eval(env);
                let envcloned = Rc::clone(env);
                let env1 = Rc::new(Env::Bind(x.clone(), v1,Rc::clone(env)));
                e2.eval(&env1)
            }
        }
    }
}
