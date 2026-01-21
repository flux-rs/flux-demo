import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec

namespace F

def map_vec_is_sorted (v : SvecSVec Int) : Bool :=
  (List.range' 0 v.len.natAbs).all
    (fun i => (List.range' i (v.len.natAbs - i)).all
      (fun j => v.elems (Int.ofNat i) ≤ v.elems (Int.ofNat j))
    )

end F
