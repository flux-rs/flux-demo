import LeanProofs.Lib
import LeanProofs.LemmaEmptyAppendLeftIdentity
import LeanProofs.SharedTheorems

def lemma_empty_append_left_identity_proof : lemma_empty_append_left_identity := by
  unfold lemma_empty_append_left_identity
  intros v _ h_v _ vlen_nonneg
  have h_v : svec_svec_slice v 0 v.fld0_1 = v := by assumption
  rw [←h_v, svec_append_eq, svec_slice_eq, svec_empty_seq_eq] ; unfold map_append map_slice ; simp
  funext x
  grind
