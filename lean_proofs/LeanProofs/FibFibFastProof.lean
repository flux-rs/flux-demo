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
    and_intros
    · intros idx idx_eq prev prev_eq curr curr_eq
      and_intros
      · omega
      · omega
      · simp [fib_fib_eq]
        unfold fib_rec fib_rec
        simp [idx_eq] ; assumption
      · simp [fib_fib_eq]
        unfold fib_rec fib_rec
        simp [idx_eq] ; assumption
      · trivial
      · trivial
    · intros idx prev curr _ ks_hold
      unfold k0 at ks_hold ; have k0_holds := ks_hold.left ; clear ks_hold
      and_intros
      · intros _ idx_ge_n
        have idx_eq_n : idx = n := by omega
        rw [←idx_eq_n]
        omega
      · intros _ idx_lt_n next_idx next_idx_eq next_fib next_fib_eq
        and_intros
        · omega
        · omega
        · rw [next_fib_eq, next_idx_eq]
          simp [k0_holds, fib_fib_eq]
          conv => rhs; unfold fib_rec
          grind
        · simp [next_idx_eq, k0_holds]
        · trivial
        · trivial
  · intros ; simp [fib_fib_eq] ; unfold fib_rec ; grind
