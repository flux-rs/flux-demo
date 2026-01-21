import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.VSeq

namespace F

def svec2_vseq_get : {t0 : Type} -> [Inhabited t0] -> (VSeq t0) -> Int -> t0 :=
  fun l pos => l.getD (List.length l - pos - 1).natAbs default


end F
