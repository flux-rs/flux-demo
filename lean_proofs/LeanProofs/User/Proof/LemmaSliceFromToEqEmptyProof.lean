import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSliceFromToEqEmpty
def LemmaSliceFromToEqEmpty_proof : LemmaSliceFromToEqEmpty := by
  unfold LemmaSliceFromToEqEmpty
  intros ; simp at *
  unfold svec_empty_seq
  funext x
  have tmp : ¬(0 ≤ x ∧ x < 0) := by omega
  simp [tmp]
