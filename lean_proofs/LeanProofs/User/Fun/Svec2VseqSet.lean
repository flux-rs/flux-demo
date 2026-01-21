import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.VSeq
import LeanProofs.User.Struct.VSeq

namespace F

def svec2_vseq_set : {t0 : Type} -> [Inhabited t0] -> (VSeq t0) -> Int -> t0 -> (VSeq t0) :=
  fun l p e => List.set l (List.length l - p - 1).natAbs e
end F
