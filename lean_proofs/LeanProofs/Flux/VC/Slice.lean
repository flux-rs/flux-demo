import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecEmptySeq
import LeanProofs.User.Fun.SvecSvecSlice

namespace F



def Slice := 
 ∀ (v₀ : (SvecSVec Int)),
  ∀ (l₀ : Int),
   ∀ (r₀ : Int),
    ((0 ≤ l₀) ∧ (l₀ ≤ (SvecSVec.len v₀))) ->
     ((l₀ ≤ r₀) ∧ (r₀ ≤ (SvecSVec.len v₀))) ->
      ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
       ((SvecSVec.len v₀) ≥ 0) ->
        (l₀ ≥ 0) ->
         (r₀ ≥ 0) ->
          ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0) 0 0) = (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0)) ->
           ((svec_svec_slice (t0 := Int) v₀ l₀ l₀) = (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0)) ->
            (((l₀ + 0) ≤ r₀)) ∧
            (((SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0) = (svec_svec_slice (t0 := Int) v₀ l₀ (l₀ + 0))))
            
end F
