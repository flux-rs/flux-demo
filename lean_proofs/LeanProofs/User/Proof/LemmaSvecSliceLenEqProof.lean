import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSvecSliceLenEq
def LemmaSvecSliceLenEq_proof : LemmaSvecSliceLenEq := by
  unfold LemmaSvecSliceLenEq
  intros ; simp at * ; grind
