use flux_rs::attrs::*;

use crate::rvec::RVec;
use rand::{Rng, rngs::ThreadRng};

#[spec(fn (bool[true]))]
fn assert(b: bool) {
    if !b {
        panic!("assertion failed");
    }
}

#[spec(fn () -> i32[0])]
fn five() -> i32 {
    assert(2 + 3 == 5);
    0
}

#[spec(fn (n:i32) -> bool[n > 0])]
fn is_pos(n: i32) -> bool {
    n > 0
}

#[spec(fn (n:i32) -> i32[n+1])]
fn inc(n: i32) -> i32 {
    n + 1
}

#[spec( fn (n:i32) -> i32{ v: 0 <= v && n <= v})]
fn abs(n: i32) -> i32 {
    if n > 0 { n } else { 0 - n }
}

#[spec(fn (x: &[T][@len], i: usize{v: v < len}) -> &T)]
fn get<T>(x: &[T], i: usize) -> &T {
    &x[i]
}

fn test_mut() {
    let mut x = 1;
    assert(x == 1);
    incr_mut(&mut x);
    assert(x == 2);
    // x += 10;
    // assert(x == 10);
    // x += 10;
    // assert(x == 20);
}

#[spec(fn (x: &mut i32[@n], b:bool) ensures x: i32{v: v == if b { n + 1} else { n - 1}})]
fn incr_funny(x: &mut i32, b: bool) {
    if b {
        *x += 1;
    } else {
        *x -= 1;
    }
}

#[spec(fn (x: &mut i32[@n]) ensures x: i32[n + 1] )]
fn incr_mut(x: &mut i32) {
    *x += 1;
}

#[spec(fn (x: &mut i32{v: v > 0}))]
fn decr_mut(x: &mut i32) {
    let n = *x;
    assert(n > 0);
    if n > 1 {
        *x = n - 1;
    }
    // *x = n + 1;
    // *x = n - 1;
}

fn test() {
    assert(abs(-5) >= 0);
    assert(abs(5) >= 5);

    assert(is_pos(5));
    assert(!is_pos(-3));
    assert(inc(4) == 5);
}

fn test_rvec() -> RVec<i32> {
    let mut vec = RVec::new();
    assert(vec.len() == 0);
    vec.push(10);
    vec.push(20);
    vec.push(30);
    assert(vec.len() == 3);
    vec
}

#[spec(fn (n:usize, f:F) -> RVec<A>[n])]
fn init<F, A>(n: usize, mut f: F) -> RVec<A>
where
    F: FnMut(usize) -> A,
{
    let mut res = RVec::new(); // res: RVec<A>[0]
    let mut i = 0;
    while i < n {
        res.push(f(i)); // res: RVec<A>[i-ish]
        i += 1;
    }
    res // res: RVec<A>[n]
}

#[spec(fn dot(x: &RVec<f64>[@n], y: &RVec<f64>[n]) -> f64)]
fn dot(x: &RVec<f64>, y: &RVec<f64>) -> f64 {
    let mut i = 0;
    let n = x.len();
    let mut res = 0.0;
    while i < n {
        res += x[i] * y[i];
        i += 1;
    }
    res
}

// ---------------------------------------------------------------------------------

// Define the structure of a single layer in the network
#[refined_by(i: int, o: int)]
struct Layer {
    #[field(usize[i])]
    num_inputs: usize,

    #[field(usize[o])]
    num_outputs: usize,

    #[field(RVec<RVec<f64>[i]>[o])]
    weight: RVec<RVec<f64>>,

    #[field(RVec<f64>[o])]
    bias: RVec<f64>,

    #[field(RVec<f64>[o])]
    outputs: RVec<f64>,
}

fn sigmoid(x: f64) -> f64 {
    1.0 / (1.0 + (-x).exp())
}

impl Layer {
    #[spec(fn(i: usize, o: usize) -> Layer[i, o])]
    fn new(i: usize, o: usize) -> Layer {
        let mut rng = rand::thread_rng();
        Layer {
            num_inputs: i,
            num_outputs: o,
            weight: init(o, |_| init(i, |_| rng.gen_range(-1.0..1.0))),
            bias: init(o, |_| rng.gen_range(-1.0..1.0)),
            outputs: init(o, |_| 0.0),
        }
    }

    #[spec(fn (&mut Layer[@l], input: &RVec<f64>[l.i]))]
    fn forward(&mut self, input: &RVec<f64>) {
        (0..self.num_outputs).for_each(|i| {
            let weighted_input = dot(&self.weight[i], input);
            self.outputs[i] = sigmoid(weighted_input + self.bias[i])
        })
    }
}

#[spec(fn() -> T requires false)]
pub fn never<T>() -> T {
    loop {}
}

#[refined_by(size:int)]
#[invariant(size >= 0)]
pub enum List<T> {
    #[variant(List<T>[0])]
    Nil,
    #[variant((T, Box<List<T>[@n]>) -> List<T>[n+1])]
    Cons(T, Box<List<T>>),
}

#[spec(fn get_nth<T>(&List<T>[@l], n: usize{v: v < l.size}) -> &T)]
fn get_nth<T>(l: &List<T>, n: usize) -> &T {
    match l {
        List::Nil => never(),
        List::Cons(h, tl) if n == 0 => h,
        List::Cons(h, tl) => get_nth(tl, n - 1),
    }
}

#[refined_by(i: int, o: int)]
enum NeuralNetwork {
    #[variant((Layer[@i, @o]) -> NeuralNetwork[i, o])]
    Last(Layer),

    #[variant((Layer[@i, @h], Box<NeuralNetwork[h, @o]>) -> NeuralNetwork[i, o])]
    Next(Layer, Box<NeuralNetwork>),
}

impl NeuralNetwork {
    #[spec(fn forward(&mut Self[@i, @o], input: &RVec<f64>[i]) -> RVec<f64>[o])]
    fn forward(&mut self, input: &RVec<f64>) -> RVec<f64> {
        match self {
            NeuralNetwork::Last(layer) => {
                layer.forward(input);
                layer.outputs.clone()
            }
            NeuralNetwork::Next(layer, next) => {
                layer.forward(input);
                next.forward(&layer.outputs)
            }
        }
    }
}

type Id = String;

enum Op {
    Add,
    Sub,
    Mul,
    Div,
}

#[refined_by(imm: bool, anf: bool)]
enum Exp {
    #[variant((Id) -> Exp[{imm: true, anf: true }])]
    Var(Id),
    #[variant((i32) -> Exp[{imm: true, anf: true }])]
    Num(i32),

    #[variant((Op, Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[{imm: false, anf: e1.imm && e2.imm}])]
    Bin(Op, Box<Exp>, Box<Exp>),

    #[variant((Id, Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[{imm: false, anf: e1.anf && e2.anf}])]
    Let(Id, Box<Exp>, Box<Exp>),
}
