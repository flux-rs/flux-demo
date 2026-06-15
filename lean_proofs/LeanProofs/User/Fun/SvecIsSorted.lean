import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.SharedTheorems

@[simp]
def svec_is_sorted : (SvecSVec Int) -> Bool := map_vec_is_sorted
