import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Vector

namespace F

@[simp]
def svec3_len : {t0 : Type} -> [Inhabited t0] -> (Vector t0) -> Int :=  fun v => List.length v


end F
