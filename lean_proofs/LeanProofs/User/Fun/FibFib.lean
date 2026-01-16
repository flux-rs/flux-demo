import LeanProofs.Flux.Prelude

def fib_rec (n : Nat) : Nat := if n ≤ 1 then 1 else fib_rec (n - 1) + fib_rec (n - 2)

def fib_fib : Int -> Int := fun n => fib_rec n.natAbs
