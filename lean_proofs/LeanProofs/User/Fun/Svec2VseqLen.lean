import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.VSeq

@[simp]
def svec2_vseq_len : {t0 : Type} -> [Inhabited t0] -> (VSeq t0) -> Int := Int.ofNat ∘ List.length
