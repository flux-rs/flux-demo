import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSlicePushExtend
def LemmaSlicePushExtend_proof : LemmaSlicePushExtend := by
  unfold LemmaSlicePushExtend
  intros ; simp at *
  unfold SmtMap_store SmtMap_select
  and_intros
  · funext x ; grind
  · grind
