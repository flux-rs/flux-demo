import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibSlow
def FibFibSlow_proof : FibFibSlow := by
  unfold FibFibSlow
  intro n ; intros
  and_intros
  · intros
    and_intros
    · grind
    · intros
      and_intros
      · grind
      · intros
        unfold fib_fib
        conv => rhs ; unfold fib_rec
        grind
  · intros
    grind [fib_fib, fib_rec]
