import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Svec2LemmaPopPushEq
def Svec2LemmaPopPushEq_proof : Svec2LemmaPopPushEq := by
  unfold Svec2LemmaPopPushEq
  intros ; simp [flip] at *
  grind
