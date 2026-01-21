import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.VSeq
import LeanProofs.User.Struct.VSeq

namespace F

def svec2_vseq_push : {t0 : Type} -> [Inhabited t0] -> (VSeq t0) -> t0 -> (VSeq t0) := flip List.cons


end F
