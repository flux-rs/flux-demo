use crate::rvec::RVec;
use crate::rvec::rvec;
use flux_rs::assert;
use flux_rs::attrs::*;

fn test() {
    assert(10 < 20)
}

type Id = String;

#[derive(Clone, Copy)]
enum Op {
    Add,
    Sub,
    Mul,
}

#[refined_by(imm: bool, anf: bool)]
enum Exp {
    // variables: x, y, z, ...
    #[variant((String) -> Exp[{imm: true, anf: true}])]
    Var(String),

    // numbers: 0, 1, 2, ...
    #[variant((i32) -> Exp[{imm: true, anf: true}])]
    Num(i32),

    // numbers: 0, 1, 2, ...
    #[variant((Op, Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[{imm: false, anf: e1.imm && e2.imm}])]
    Bin(Op, Box<Exp>, Box<Exp>),

    #[variant((Id, Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[{imm: false, anf: e1.anf && e2.anf}])]
    Let(Id, Box<Exp>, Box<Exp>),
}

// subset of Exp that are in ANF
#[alias(type Anf[e:Exp] = {Exp[e] | e.anf})]
type Anf = Exp;

// subset of Exp that are IMM
#[alias(type Imm[e:Exp] = {Exp[e] | e.imm && e.anf})]
type Imm = Exp;

//---------------------------------------------------------------------------------------

fn var(s: &str) -> Imm {
    Exp::Var(s.to_string())
}

fn num(n: i32) -> Imm {
    Exp::Num(n)
}

#[spec(fn(_, e1: Exp, e2: Exp) -> Exp[{imm: false, anf: e1.anf && e2.anf}])]
fn lett(id: &str, e1: Exp, e2: Exp) -> Exp {
    Exp::Let(id.to_string(), Box::new(e1), Box::new(e2))
}

#[spec(fn(Op, Exp[@e1], Exp[@e2]) -> Exp[{imm: false, anf: e1.imm && e2.imm}])]
fn bin(op: Op, e1: Exp, e2: Exp) -> Exp {
    Exp::Bin(op, Box::new(e1), Box::new(e2))
}

//---------------------------------------------------------------------------------------

// ((2 + 3) * (12 - 4)) * (7 + 8)
#[spec(fn() -> Exp[{imm: false, anf: false}])]
fn exp0() -> Exp {
    bin(
        Op::Mul,
        bin(
            Op::Mul,
            bin(Op::Add, num(2), num(3)),
            bin(Op::Sub, num(12), num(4)),
        ),
        bin(Op::Add, num(7), num(8)),
    )
}

// let x = 2 + 3 in (x + 4)
#[spec(fn() -> Exp[{imm: false, anf: true}])]
fn exp1() -> Exp {
    lett(
        "x",
        bin(Op::Add, num(2), num(3)),
        bin(Op::Add, var("x"), num(4)),
    )
}

//---------------------------------------------------------------------------------------

fn fresh_id(count: &mut usize) -> Id {
    let name = format!("tmp{}", count);
    *count += 1;
    name.to_string()
}

fn stitch(mut binds: RVec<(Id, Anf)>, e: Anf) -> Anf {
    let mut res = e;
    if binds.len() > 0 {
        let (x, e) = binds.pop();
        stitch(binds, lett(&x, e, res))
    } else {
        res
    }
}

impl Exp {
    #[spec(fn(&Exp[@e]) -> bool[e.imm])]
    fn is_imm(&self) -> bool {
        match self {
            Exp::Var(_) => true,
            Exp::Num(_) => true,
            Exp::Bin(_, e1, e2) => false,
            Exp::Let(_, e1, e2) => false,
        }
    }

    #[spec(fn(&Exp[@e]) -> bool[e.anf])]
    fn is_anf(&self) -> bool {
        match self {
            Exp::Var(_) => true,
            Exp::Num(_) => true,
            Exp::Bin(_, e1, e2) => e1.is_imm() && e2.is_imm(),
            Exp::Let(_, e1, e2) => e1.is_anf() && e2.is_anf(),
        }
    }

    #[spec(fn (_, count: &mut usize, binds: &mut RVec<(Id, Exp{v:v.anf})>) -> Imm)]
    fn to_imm(&self, count: &mut usize, binds: &mut RVec<(Id, Anf)>) -> Imm {
        match self {
            Exp::Var(x) => var(x),
            Exp::Num(n) => num(*n),
            Exp::Bin(op, e1, e2) => {
                let v1 = e1.to_imm(count, binds);
                let v2 = e2.to_imm(count, binds);
                let tmp = fresh_id(count);
                binds.push((tmp.clone(), bin(*op, v1, v2)));
                Exp::Var(tmp)
            }
            Exp::Let(x, e1, e2) => {
                let a = self.to_anf(count);
                let tmp = fresh_id(count);
                binds.push((tmp.clone(), a));
                Exp::Var(tmp)
            }
        }
    }

    fn to_anf(&self, count: &mut usize) -> Anf {
        match self {
            Exp::Var(x) => var(x),
            Exp::Num(n) => num(*n),
            Exp::Bin(op, e1, e2) => {
                let mut binds = rvec![];
                let v1 = e1.to_imm(count, &mut binds);
                let v2 = e2.to_imm(count, &mut binds);
                stitch(binds, bin(*op, v1, v2))
                // ASK-NICO
                // while 0 < binds.len() {
                //    let (x, a) = binds.pop();
                //    assert(a.is_anf());
                //    assert(res.is_anf());
                // res = lett(&x, e, res);
                // }
            }
            Exp::Let(x, e1, e2) => {
                let a = self.to_anf(count);
                lett(x, e1.to_anf(count), a)
            }
        }
    }
}

fn test_anf(e: &Exp) {
    let res = e.to_anf(&mut 0);
    assert(res.is_anf());
}
