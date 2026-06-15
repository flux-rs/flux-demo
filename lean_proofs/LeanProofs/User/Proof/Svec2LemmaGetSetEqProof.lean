import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Svec2LemmaGetSetEq
def Svec2LemmaGetSetEq_proof : Svec2LemmaGetSetEq := by
  unfold Svec2LemmaGetSetEq
  intros ; simp at *
  rw [List.getElem?_set]
  grind
