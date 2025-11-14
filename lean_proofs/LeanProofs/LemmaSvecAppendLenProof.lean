import LeanProofs.Lib
import LeanProofs.LemmaSvecAppendLen
import LeanProofs.SharedTheorems

def lemma_svec_append_len_proof : lemma_svec_append_len := by
  unfold lemma_svec_append_len
  intros v1 v2 _ h_v2 _ v2_len_nonneg
  rw [svec_append_eq] ; unfold map_append
  simp
