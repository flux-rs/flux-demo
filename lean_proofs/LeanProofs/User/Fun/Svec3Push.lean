import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Vector
import LeanProofs.User.Struct.Vector

namespace F

@[simp]
def svec3_push : {t0 : Type} -> [Inhabited t0] -> (Vector t0) -> t0 -> (Vector t0) := fun l e => e :: l


end F
