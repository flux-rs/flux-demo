import LeanProofs.Lib
import LeanProofs.LemmaAppendEmptyRfl
import LeanProofs.SharedTheorems

def lemma_append_empty_rfl_proof : lemma_append_empty_rfl := by
  unfold lemma_append_empty_rfl
  intros b e _ b_slice _ b_len_nonneg _ e_len_nonneg _ e_h
  have b_slice': svec_svec_slice b 0 b.fld0_1 = b := by exact b_slice
  rw [←b_slice', svec_append_eq, svec_slice_eq] ; unfold map_append map_slice; simp
  funext x
  grind
