import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaAppendEmptyRfl
def LemmaAppendEmptyRfl_proof : LemmaAppendEmptyRfl := by
  unfold LemmaAppendEmptyRfl
  intros ; simp at *
  ext
  · funext x ; grind
  · grind
