import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Vector
import LeanProofs.User.Struct.Vector

namespace F

def svec3_set : {t0 : Type} -> [Inhabited t0] -> (Vector t0) -> Int -> t0 -> (Vector t0) := fun v p e =>
  let p := v.length - 1 - p
  if 0 ≤ p ∧ p < v.length
  then v.set p.toNat e
  else v


end F
