import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecSlice


def LemmaSliceZeroToLenEq := 
 ∀ (v₀ : (SvecSVec Int)),
  ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
   ((SvecSVec.len v₀) ≥ 0) ->
    ((svec_svec_slice (t0 := Int) v₀ 0 (SvecSVec.len v₀)) = v₀)