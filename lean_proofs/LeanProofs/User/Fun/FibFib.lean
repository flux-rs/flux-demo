import LeanProofs.Flux.Prelude

namespace F

def fib_fib (n: Int) : Int := if n ≤ 1 then 1 else fib_fib (n - 1) + fib_fib (n - 2)
  termination_by n.toNat

end F
