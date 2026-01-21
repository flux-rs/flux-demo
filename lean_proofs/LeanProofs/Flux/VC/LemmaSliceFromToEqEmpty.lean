import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecEmptySeq
import LeanProofs.User.Fun.SvecSvecSlice

namespace F



def LemmaSliceFromToEqEmpty := 
 ∀ (v₀ : (SvecSVec Int)),
  ∀ (idx₀ : Int),
   (idx₀ ≤ (SvecSVec.len v₀)) ->
    ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
     ((SvecSVec.len v₀) ≥ 0) ->
      (idx₀ ≥ 0) ->
       ((svec_svec_slice (t0 := Int) v₀ idx₀ idx₀) = (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0))
end F
