import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test09

namespace F

def Test09_proof : Test09 := by
  unfold Test09
  exists (fun _ => True)
  exists (fun _ => True)
  exists (fun _ => True)
  simp
end F
