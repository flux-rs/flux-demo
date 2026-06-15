#import "tufte-handout.typ": margin-note, template

#show raw.where(block: true): it => block(
  stroke: 0.5pt + luma(150),
  inset: (x: 0.75em, y: 0.65em),
  radius: 2pt,
  width: 100%,
  it,
)

#set page(footer: context align(center, text(size: 7pt, counter(page).display("1"))))

#show: doc => template(
  title: "CSE 231: Normal Forms",
  author: "Ranjit Jhala",
  date: "May 18, 2026",
  doc,
)

= Normal Forms

One of the key steps in compilation is the
conversion to *A-Normal Form (ANF)*
where, informally speaking, each call or primitive
operation's arguments are *immediate* values,
i.e. constants or variable lookups whose values can
be loaded with a single machine instruction. For example,
the expression

```clojure
((2 + 3) * (12 - 4)) * (7 + 8)
```

has the A-Normal Form:

```clojure
(let (?tmp0 (+ 2 3))
  (let (?tmp1 (- 12 4))
    (let (?tmp2 (* ?tmp0 ?tmp1))
      (let (?tmp3 (+ 7 8))
        (* ?tmp2 ?tmp3)))))
```

The usual presentation of ANF conversion
is very elegant but relies upon a clever
use of continuations.

Lets look at another perhaps simpler approach,
where we can use *refinement types* to light the way.

= Source Language

Lets commence by defining the source language that we wish to work with:

```rust
type Id = String;

enum Op { Add, Sub, Mul }

enum Exp {
  Var(String),                 // vars: x, y, ...
  Num(i32),                    // numbers: 0, 1,...
  Bin(Op, Box<Exp>, Box<Exp>), // binops
  Let(Id, Box<Exp>, Box<Exp>), // let-binders
}
```

The language, defined by `Exp`, has integers, variables, binary operators,
and let-binders.

For example, the source expression above corresponds to:

```rust
// ((2 + 3) * (12 - 4)) * (7 + 8)
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
```

= A-Normal Form

Before we can describe a _conversion_ to A-Normal Form (ANF),
we must pin down what ANF _is_. Our informal description was:

*Immediate Values:*
"_constants or variable lookups whose values can be loaded with a single machine instruction_"

*ANF Values:*
"_each call or primitive operation's arguments are *immediate* values, i.e. constants or variable lookups_"

#margin-note([
  We _could_ define brand new types, say `ImmExp` and `AnfExp`,
  whose values correspond to _immediate_ and _ANF_ terms.
  Unfortunately, doing so leads to a bunch of code duplication,
  e.g. duplicate printers for `Exp` and `AnfExp`.
  Try it, as an exercise.
])

Lets see how we can use *Flux* refinements to carve out suitable
subsets of `Exp`.

= Specifying ANF via Refined Types

First, we add two boolean indices to `Exp` using `refined_by`:

```rust
#[refined_by(n: int)]
#[invariant(0 <= n)]
enum Exp {
  Var(String)
    -> Exp[{imm: true, anf: true}],
  Num(i32)
    -> Exp[{imm: true, anf: true}],
  Bin(Op, Box<Exp[@e1]>, Box<Exp[@e2]>)
    -> Exp[{imm: false, anf: e1.imm && e2.imm}],
  Let(Id, Box<Exp[@e1]>, Box<Exp[@e2]>)
    -> Exp[{imm: false, anf: e1.anf && e2.anf}],
}
```

- The `imm` index tracks whether an expression is _immediate_
- The `anf` index tracks whether it is in _A-Normal Form_.
- The `invariant` says every _immediate_ expression is also ANF (since immediates are a subset of ANF).

#colbreak()

== Immediate Expressions

An `Exp` is *immediate* if it is a `Num` or a `Var`,
specified by giving the `Var` and `Num` constructors
`imm: true` and `anf: true`.

== ANF Expressions

An `Exp` is in *ANF* if all arguments to binary operators
are *immediate*, specified by `e1.imm && e2.imm`.

For `Let`, sub-expressions must themselves be ANF, also
specified by `e1.anf && e2.anf`.

== Refined Type Aliases

We can write type aliases for the subsets of interest:

```rust
#[alias(type Anf = Exp{e: e.anf})]
type Anf = Exp;

#[alias(type Imm = Exp{e: e.imm})]
type Imm = Exp;
```

= Checking Predicates

Lets write runtime tests to *mirror* the refinement indices.

For example, `is_imm` returns `true` exactly when the expression's
`imm` index is `true`:

```rust
impl Exp {
  #[spec(fn(&Exp[@e]) -> bool[e.imm])]
  fn is_imm(&self) -> bool {
    match self {
      Var(_) => true,
      Num(_) => true,
      Bin(_, _, _) => false,
      Let(_, _, _) => false,
    }
  }

  #[spec(fn(&Exp[@e]) -> bool[e.anf])]
  fn is_anf(&self) -> bool {
    match self {
      Var(_) => true,
      Num(_) => true,
      Bin(_, e1, e2) => e1.is_imm() && e2.is_imm(),
      Let(_, e1, e2) => e1.is_anf() && e2.is_anf(),
    }
  }
}
```

The `#[spec(...)]` tells Flux that the return value of
`is_imm` (resp. `is_anf`) _equals_ the expression's `imm`
(resp. `anf`) index, _connecting_ the run-time test to the compile-time
refinement.

= Smart Constructors

We define some _smart constructors_ with refined signatures.

== Var and Num

The smart constructors for `Var` and `Num` are straightforward, as they
return `Imm` expressions

```rust
fn var(s: &str) -> Imm {
    Exp::Var(s.to_string())
}

fn num(n: i32) -> Imm {
    Exp::Num(n)
}
```

== Bin and Let

The smart constructors for `Bin` and `Let` are more interesting, as they return `Exp` expressions whose `anf` index depends on the `imm` and `anf` indices of their arguments.


Lets define an _alias_ for an `Exp` whose `anf` index depends on the `imm` of two _other_ expressions.

```rust
defs!{
  fn anf2(e1: Exp, e2: Exp) -> Exp {
    { imm: false, anf: e1.imm && e2.imm }
  }
}

#[alias(type Exp2[e1:Exp,e2:Exp] = Exp[anf2(e1,e2)])]
type Exp2 = Exp;
```

We can now define the types for the smart constructors for `Bin` and `Let`, to say that
they return `Exp` expressions whose `anf` index depends on the `imm` and `anf` indices
of their arguments:

```rust
fn let_(id: &str, e1: Exp, e2: Exp) -> Exp2[e1,e2]
{
    let id = id.to_string();
    Exp::Let(id, Box::new(e1), Box::new(e2))
}

fn bin(op: Op, e1: Exp, e2: Exp) -> Exp2[e1, e2]
{
    Exp::Bin(op, Box::new(e1), Box::new(e2))
}
```

#colbreak()

= ANF Conversion: Intuition

Now that we have clearly demarcated the territories belonging to plain `Exp`,
immediate `Imm` and A-Normal `Anf`, lets see how we can convert `Exp` to `Anf`.

Recall that our goal is to convert expressions like

```clojure
((2 + 3) * (12 - 4)) * (7 + 8)
```

into

```clj
(let (?tmp0 (+ 2 3))
  (let ?tmp1 = (- 12 4) in
    (let ?tmp2 = (* ?tmp0 ?tmp1) in
      (let ?tmp3 = (+ 7 8) in
        (* ?tmp2 ?tmp3)))))
```

Generalizing a bit, we want to convert

```clj
(+ e1 e2)
```

into

```clj
(let (x1 a1)
  ...
  (let (xn an)
    (let (x1' a1')
      ...
      (let (xm' am')
        (+ v1 v2) ...) ... )
```

where `v1` and `v2` are immediate, and each `ai` is ANF.

= Forcing Arguments to be Immediate

The key requirement is a way to *force* arbitrary _argument expressions_ like `e1` into *a pair*:

- a vector of bindings `[(x1, a1), ..., (xn, an)]` where each `ai` is `Anf`, and
- an immediate expression `v1` of type `Imm`.

so `e1` is _equivalent_ to `(let (x1 a1) ... (let (xn an) v1))`.

Thus, we need a method:

```rust
fn to_imm(
    &self,
    count: &mut usize,
    binds: &mut Vec<(Id, Anf)>
) -> Imm
```

which we will use to *make arguments immediate*, yielding
a top-level conversion method:

```rust
fn to_anf(&self, count: &mut usize) -> Anf
```

As we need to generate "temporary" intermediate
binders, we use a `count: &mut usize` parameter
to produce `fresh` variable names:

```rust
fn fresh_id(count: &mut usize) -> Id {
    let name = format!("?tmp{}", count);
    *count += 1;
    name.to_string()
}
```

= ANF Conversion: Code

== Making Arguments Immediate: `to_imm`

```rust
fn to_imm(&self, count: &mut usize,
    binds: &mut RVec<(Id, Anf)>) -> Imm
{
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
```

- *Numbers and variables* are already immediate, and are returned directly.
- *Binary operators* recursively make their operands immediate,
  generate a fresh binder for the operation, and return the
  fresh variable.
- *Let-binders* are converted to ANF and assigned to a fresh binder.

== Top-Level Conversion: `to_anf`

```rust
fn to_anf(&self, count: &mut usize) -> Anf {
    match self {
        Exp::Var(x) => var(x),
        Exp::Num(n) => num(*n),
        Exp::Let(x, e1, e2) => {
            let e1 = e1.to_anf(count);
            let e2 = e2.to_anf(count);
            let_(x, e1, e2)
        }
        Exp::Bin(op, e1, e2) => {
            let mut binds = rvec![];
            let v1 = e1.to_imm(count, &mut binds);
            let v2 = e2.to_imm(count, &mut binds);
            let mut res = bin(*op, v1, v2);
            while !binds.is_empty() {
                let (x, a) = binds.pop();
                res = let_(&x, a, res);
            }
            res
        }
    }
}
```

In `to_anf`, the real work happens inside `to_imm` which takes an arbitrary
_argument_ expression and makes it *immediate* by generating temporary
(ANF) bindings. The resulting bindings (and immediate values) are
composed by popping from the `binds` vector and wrapping the result
with `let_` to stitch them into a single `Anf` expression.

= Verifying the Conversion

We can test the conversion and use Flux to *verify* that
the result is in ANF:

```rust
fn test_anf(e: &Exp) {
    let res = e.to_anf(&mut 0);
    assert(res.is_anf());
}
```

The call to `assert` statically checks that `res.is_anf()` is `true`,
as guaranteed by the refined return type `Anf` of `to_anf`.
