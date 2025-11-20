import LeanProofs.Lib
import LeanProofs.LemmaSortedSlice
import LeanProofs.SharedTheorems

def lemma_sorted_slice_proof : lemma_sorted_slice := by
  unfold lemma_sorted_slice
  intros v l r _ vsorted _ l_ubound _ r_bounds _ h_slice _ v_len_lbound _ l_lbound _ _
  rw [svec_is_sorted_eq] at *
  intros i j i_bounds j_bounds
  simp [svec_slice_eq, map_slice] at *
  have tmp1 : ¬ r - l < 0 := by omega
  have tmp2 : ¬ j < 0 := by omega
  simp [tmp1] at *
  simp [i_bounds, j_bounds, tmp2]
  apply_assumption <;> omega
