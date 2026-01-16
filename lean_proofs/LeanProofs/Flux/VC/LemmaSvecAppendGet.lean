import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecAppend
import LeanProofs.User.Fun.SvecSvecSlice


def LemmaSvecAppendGet := 
 ∀ (v1₀ : (SvecSVec Int)),
  ∀ (v2₀ : (SvecSVec Int)),
   ∀ (pos₀ : Int),
    ((0 ≤ pos₀) ∧ (pos₀ < (SvecSVec.len (svec_svec_append (t0 := Int) v1₀ v2₀)))) ->
     ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v2₀) (SvecSVec.len v2₀)) 0 (SvecSVec.len v2₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v2₀) (SvecSVec.len v2₀))) ->
      ((SvecSVec.len v2₀) ≥ 0) ->
       (pos₀ ≥ 0) ->
        ((SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_append (t0 := Int) v1₀ v2₀)) pos₀) = (if (pos₀ < (SvecSVec.len v1₀)) then (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v1₀) pos₀) else (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v2₀) (pos₀ - (SvecSVec.len v1₀)))))