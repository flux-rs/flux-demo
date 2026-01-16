import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.FibFib
namespace FibFibFastKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₃ : Int) (a'₄ : Int) (a'₅ : Int) (a'₆ : Int) : Prop :=
  ((¬(a'₆ < a'₃)) ∧ (¬(a'₃ ≤ 1)) ∧ (a'₃ > 0) ∧ (a'₃ ≥ 0) ∧ (a'₃ ≤ a'₆))

end FibFibFastKVarSolutions


open FibFibFastKVarSolutions




def FibFibFast := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((!(n₀ ≤ 1)) ->
    (((k0 2 1 2 n₀))) ∧
    (∀ (i₀ : Int),
     ∀ (prev₀ : Int),
      ∀ (curr₀ : Int),
       ((k0 i₀ prev₀ curr₀ n₀)) ->
        ((!(i₀ < n₀)) ->
         (curr₀ = (fib_fib n₀))) ∧
        ((i₀ < n₀) ->
         ((k0 (i₀ + 1) curr₀ (prev₀ + curr₀) n₀)))
        )
    ) ∧
   ((n₀ ≤ 1) ->
    (1 = (fib_fib n₀)))
   