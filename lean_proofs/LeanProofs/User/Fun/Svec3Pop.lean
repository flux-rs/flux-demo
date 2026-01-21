import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Vector
import LeanProofs.User.Struct.Vector

namespace F

@[simp]
def svec3_pop : {t0 : Type} -> [Inhabited t0] -> (Vector t0) -> (Vector t0) := fun v => match v with
  | [] => []
  | (_::t) => t

end F
