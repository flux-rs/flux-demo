import LeanProofs.Lib
import LeanProofs.OpaqueSorts
import LeanProofs.OpaqueFuncs
def fib_fib_slow := (∀ (reftgen_n_0 : Int), (∀ (__ : Int), ((reftgen_n_0 ≥ 0) -> ((∀ (__ : Int), ((¬(reftgen_n_0 ≤ 1)) -> (((reftgen_n_0 - 1) ≥ 0) ∧ (∀ (__ : Int), (((fib_fib (reftgen_n_0 - 1)) ≥ 0) -> (((reftgen_n_0 - 2) ≥ 0) ∧ (∀ (__ : Int), (((fib_fib (reftgen_n_0 - 2)) ≥ 0) -> (((fib_fib (reftgen_n_0 - 1)) + (fib_fib (reftgen_n_0 - 2))) = (fib_fib reftgen_n_0)))))))))) ∧ (∀ (__ : Int), ((reftgen_n_0 ≤ 1) -> (1 = (fib_fib reftgen_n_0))))))))
