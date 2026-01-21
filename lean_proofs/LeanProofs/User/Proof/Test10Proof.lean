import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test10

namespace F

def Test10_proof : Test10 := by
  unfold Test10
  exists (fun _ => True)
  exists (fun _ => True)
  exists (fun _ => True)
  exists (fun _ => True)
  simp [svec3_set]

end F
