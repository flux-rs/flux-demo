import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSliceZeroToLenEq
def LemmaSliceZeroToLenEq_proof : LemmaSliceZeroToLenEq := by
  unfold LemmaSliceZeroToLenEq
  intros ; simp at *
  ext <;> grind
