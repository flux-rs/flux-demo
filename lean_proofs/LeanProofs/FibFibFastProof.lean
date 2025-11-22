import LeanProofs.Lib
import LeanProofs.FibFibFast
import LeanProofs.SharedTheorems

def k0 : Int → Int → Int → Int → Prop := fun idx prev curr n => idx ≥ 2 ∧ idx ≤ n ∧ curr = fib_fib idx ∧ prev = fib_fib (idx - 1)
def k1 : Int → Int → Int → Prop := fun _ _ _ => True
def k2 : Int → Int → Prop := fun _ _ => True

def fib_fib_fast_proof : fib_fib_fast := by
  unfold fib_fib_fast
  exists k0
  exists k1
  exists k2
  intro n ; intros
  and_intros
  · intros
    unfold k0 k1 k2 at *;
    and_intros
    · intros
      and_intros <;>
        grind [fib_fib_eq, fib_rec]
    · intro idx ; intros
      and_intros
      · intros
        have idx_eq_n : idx = n := by omega
        rw [←idx_eq_n]
        omega
      · intros _ idx_lt_n next_idx next_idx_eq next_fib next_fib_eq
        rw [next_fib_eq, next_idx_eq]
        simp [fib_fib_eq, *]
        conv => rhs ; rhs ; rhs ; unfold fib_rec
        and_intros <;> grind
  · intros ; grind [fib_fib_eq, fib_rec]
