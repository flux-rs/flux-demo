import LeanProofs.Lib
import LeanProofs.LemmaSliceGet
import LeanProofs.SharedTheorems

def lemma_slice_get_proof : lemma_slice_get := by
  unfold lemma_slice_get
  intros v l r pos _ l_ub _ r_b _ pos_ub _ h_v _ v_len_lb _ l_lb _ _ _ pos_lb
  simp [svec_slice_eq, SmtMap_select, map_slice]
  grind
