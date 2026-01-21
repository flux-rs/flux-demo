import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Vector

namespace F

@[simp]
def svec3_get : {t0 : Type} -> [Inhabited t0] -> (Vector t0) -> Int -> t0 := fun v p =>
  let p := v.length - 1 - p
  if h : 0 ≤ p ∧ p < v.length
  then v.get (Fin.mk p.toNat (by omega))
  else default

end F
