import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecAppend
import LeanProofs.User.Fun.SvecSvecSlice


def LemmaSvecAppendLen := 
 ∀ (v1₀ : (SvecSVec Int)),
  ∀ (v2₀ : (SvecSVec Int)),
   ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v2₀) (SvecSVec.len v2₀)) 0 (SvecSVec.len v2₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v2₀) (SvecSVec.len v2₀))) ->
    ((SvecSVec.len v2₀) ≥ 0) ->
     ((SvecSVec.len (svec_svec_append (t0 := Int) v1₀ v2₀)) = ((SvecSVec.len v1₀) + (SvecSVec.len v2₀)))