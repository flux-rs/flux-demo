import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.VSeq
import LeanProofs.User.Struct.VSeq

namespace F

def svec2_vseq_pop : {t0 : Type} -> [Inhabited t0] -> (VSeq t0) -> (VSeq t0) := fun v => match v with
  | []     => []
  | (_::t) => t


end F
