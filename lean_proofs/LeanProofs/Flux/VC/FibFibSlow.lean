import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.FibFib

namespace F



def FibFibSlow := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((!(n₀ ≤ 1)) ->
    (((n₀ - 1) ≥ 0)) ∧
    (((fib_fib (n₀ - 1)) ≥ 0) ->
     (((n₀ - 2) ≥ 0)) ∧
     (((fib_fib (n₀ - 2)) ≥ 0) ->
      (((fib_fib (n₀ - 1)) + (fib_fib (n₀ - 2))) = (fib_fib n₀)))
     )
    ) ∧
   ((n₀ ≤ 1) ->
    (1 = (fib_fib n₀)))
   
end F
