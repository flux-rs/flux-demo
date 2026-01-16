import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaEmptyAppendLeftIdentity
def LemmaEmptyAppendLeftIdentity_proof : LemmaEmptyAppendLeftIdentity := by
  unfold LemmaEmptyAppendLeftIdentity
  intros ; simp at *
  ext
  · funext x ; grind
  · grind
