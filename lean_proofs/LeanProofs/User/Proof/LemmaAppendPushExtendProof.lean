import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaAppendPushExtend
def LemmaAppendPushExtend_proof : LemmaAppendPushExtend := by
  unfold LemmaAppendPushExtend
  intros app l r idx h idx_bounded h_app app_len_nonneg h_r r_len_nonneg _
  have ⟨app_eq, llen_nonneg⟩ := h ; clear h
  rw [app_eq] ; simp ; unfold SmtMap_store SmtMap_select
  and_intros
  · funext x ; grind
  · grind
