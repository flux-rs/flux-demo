import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSvecAppendGet
def LemmaSvecAppendGet_proof : LemmaSvecAppendGet := by
  unfold LemmaSvecAppendGet
  intros ; simp [SmtMap_select] at *
  grind
