import LeanProofs.Lib
import LeanProofs.FibFibSlow
import LeanProofs.SharedTheorems

def fib_fib_slow_proof : fib_fib_slow := by
  unfold fib_fib_slow
  intro n ; intros
  and_intros
  · intros
    and_intros
    · omega
    · intros
      and_intros
      · omega
      · intros
        simp [fib_fib_eq]
        conv => rhs ; unfold fib_rec
        have h : ¬ n.natAbs ≤ 1 := by omega
        simp [h]
        grind
  · intros
    grind [fib_fib_eq, fib_rec]
