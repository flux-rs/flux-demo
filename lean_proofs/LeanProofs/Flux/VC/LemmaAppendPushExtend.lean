import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecAppend
import LeanProofs.User.Fun.SvecSvecSlice


def LemmaAppendPushExtend := 
 ∀ (append₀ : (SvecSVec Int)),
  ∀ (l₀ : (SvecSVec Int)),
   ∀ (r₀ : (SvecSVec Int)),
    ∀ (ext_idx₀ : Int),
     ((append₀ = (svec_svec_append (t0 := Int) l₀ (svec_svec_slice (t0 := Int) r₀ 0 ext_idx₀))) ∧ ((SvecSVec.len l₀) ≥ 0)) ->
      ((0 ≤ ext_idx₀) ∧ (ext_idx₀ ≤ (SvecSVec.len r₀))) ->
       ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems append₀) (SvecSVec.len append₀)) 0 (SvecSVec.len append₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems append₀) (SvecSVec.len append₀))) ->
        ((SvecSVec.len append₀) ≥ 0) ->
         ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems r₀) (SvecSVec.len r₀)) 0 (SvecSVec.len r₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems r₀) (SvecSVec.len r₀))) ->
          ((SvecSVec.len r₀) ≥ 0) ->
           (ext_idx₀ ≥ 0) ->
            ((SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems append₀) (SvecSVec.len append₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems r₀) ext_idx₀)) ((SvecSVec.len append₀) + 1)) = (svec_svec_append (t0 := Int) l₀ (svec_svec_slice (t0 := Int) r₀ 0 (ext_idx₀ + 1))))