import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibFast

set_option linter.unusedVariables false

def k0 : Int → Int → Int → Int → Prop := fun idx prev curr n => idx ≥ 2 ∧ idx ≤ n ∧ curr = fib_fib idx ∧ prev = fib_fib (idx - 1)

def FibFibFast_proof : FibFibFast := by
  unfold FibFibFast
  exists k0 ; unfold k0 at *
  intro n ; intros
  simp at *
  · intros
    and_intros <;> try grind [fib_fib, fib_rec]
    intros
    and_intros <;> try grind [fib_fib, fib_rec]
    intros
    and_intros
    · intros ; grind
    · intros
      and_intros <;> try grind
      simp_all
      conv => rhs ; unfold fib_fib fib_rec
      grind [fib_fib]
