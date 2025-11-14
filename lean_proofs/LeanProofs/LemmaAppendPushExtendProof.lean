import LeanProofs.Lib
import LeanProofs.LemmaAppendPushExtend
import LeanProofs.SharedTheorems

def lemma_append_push_extend_proof : lemma_append_push_extend := by
  unfold lemma_append_push_extend
  intros app l r idx _ h _ idx_bounded _ h_app _ app_len_nonneg _ h_r _ r_len_nonneg _ _
  have ⟨app_eq, llen_nonneg⟩ := h ; clear h
  rw [app_eq, svec_append_eq, svec_slice_eq] ; unfold SmtMap_store SmtMap_select map_append map_slice
  ext
  · funext x ; grind
  · grind
