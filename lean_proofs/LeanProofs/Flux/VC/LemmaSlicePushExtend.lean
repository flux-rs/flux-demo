import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecSlice


def LemmaSlicePushExtend := 
 ∀ (v₀ : (SvecSVec Int)),
  ∀ (l₀ : Int),
   ∀ (r₀ : Int),
    (l₀ < (SvecSVec.len v₀)) ->
     ((l₀ ≤ r₀) ∧ (r₀ < (SvecSVec.len v₀))) ->
      ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
       ((SvecSVec.len v₀) ≥ 0) ->
        (l₀ ≥ 0) ->
         (r₀ ≥ 0) ->
          ((SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ l₀ r₀)) (r₀ - l₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v₀) r₀)) ((r₀ - l₀) + 1)) = (svec_svec_slice (t0 := Int) v₀ l₀ (r₀ + 1)))