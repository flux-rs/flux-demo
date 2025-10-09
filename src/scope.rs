use std::rc::Rc;

use flux_rs::{attrs::*, assert };
// use flux_alloc::string::mk_string;
use crate::rset::*;


fn test() {
    let x = 1;
    let y = 2;
    let z = 3;
    assert(x + y == z);
    // let bob: Option<u32> = None;
    // let b = bob.unwrap();
}

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

/// Values --------------------------------------------------------------
type Val = i32;

pub fn test_clone() {
    let bob1 = mk_string("bob");
    let rc_bob = Rc::new(bob1);
    let bob2 = mk_string("bob"); // bob1.clone();
    assert(bob2 == *rc_bob);
}



/// Environments --------------------------------------------------------

type Id = String;

#[refined_by(binds: Set<String>)]
enum Env<V> {
    #[variant(Env<V>[set_emp()])]
    Empty,

    #[variant((Id[@x], V, Rc<Env<V>>[@env]) -> Env<V>[set_add(x, env.inner)])]
    Bind(Id, V, Rc<Env<V>>),
}

/// Environment lookup
#[spec(fn(&Env<V>[@env], &String[@x]) -> &V requires set_is_in(x, env))]
fn lookup<'a, V>(env: &'a Env<V>, x: &String) -> &'a V {
    match env {
        Env::Bind(y, v, env1) => {
            if *x == *y {
                v
            } else {
                lookup(env1, x)
            }
        }
        Env::Empty => impossible(),
    }
}

/// Environment lookup -- OPT!
#[spec(fn(&Env<V>[@env], &String[@x]) -> Option<&V>[set_is_in(x, env)])]
fn lookup_opt<'a, V>(env: &'a Env<V>, x: &String) -> Option<&'a V> {
    match env {
        Env::Bind(y, v, env1) => {
            if *x == *y {
                Some(v)
            } else {
                lookup_opt(env1, x)
            }
        }
        Env::Empty => None,
    }
}

fn test_lookup_opt() -> Val {
    let x = mk_string("x");
    let y = mk_string("y");
    let z = mk_string("z");
    let env = Rc::new(Env::Bind(x.clone(), 1, Rc::new(Env::Bind(y.clone(), 2, Rc::new(Env::Empty)))));
    let xval = *lookup_opt(&env, &x).unwrap();
    let yval = *lookup_opt(&env, &y).unwrap();
    // let zval = *lookup_opt(&env, &z).unwrap();
    xval + yval // + zval
}


/// Operators ----------------------------------------------------------

#[derive(Clone, Copy)]
enum Op {
    Add,
    Sub,
    Mul,
}

fn eval_op(op: Op, v1: Val, v2: Val) -> Val {
    match op {
        Op::Add => v1 + v2,
        Op::Sub => v1 - v2,
        Op::Mul => v1 * v2,
    }
}

/// Expressions ----------------------------------------------------------

#[refined_by(free: Set<String>)]
enum Exp {
    /// variables: x, y, z, ...
    #[variant((String[@x]) -> Exp[set_singleton(x)])]
    Var(String),

    /// numbers: 0, 1, 2, ...
    #[variant((i32) -> Exp[set_emp()])]
    Num(i32),

    /// numbers: 0, 1, 2, ...
    #[variant((Op, Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[set_union(e1.free, e2.free)])]
    Bin(Op, Box<Exp>, Box<Exp>),

    /// let x = e1 in e2
    #[variant((Id[@x], Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[set_union(e1.free, set_del(x, e2.free))])]
    Let(Id, Box<Exp>, Box<Exp>),
}

/// ----------------------------------------------------------------------------
#[spec(fn(&Exp[@e], &Rc<Env<Val>>[@env]) -> Val requires set_subset(e.free, env.inner))]
fn eval(e: &Exp, env: &Rc<Env<Val>>) -> Val {
    match e {
        Exp::Num(n) => *n,
        Exp::Var(x) => *lookup_opt(&env, x).unwrap(),
        Exp::Bin(op, e1, e2) => {
            let v1 = eval(e1, env);
            let v2 = eval(e2, env);
            eval_op(*op, v1, v2)
        }
        Exp::Let(x, e1, e2) => {
            let v1 = eval(e1, env);
            let envcloned = Rc::clone(env);
            let env1 = Rc::new(Env::Bind(x.clone(), v1, Rc::clone(env)));
            eval(e2, &env1)
        }
    }
}
