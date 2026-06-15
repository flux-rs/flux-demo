import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecEmptySeq
import LeanProofs.User.Fun.SvecSvecAppend
import LeanProofs.User.Fun.SvecSvecSlice


def LemmaEmptyAppendLeftIdentity := 
 ∀ (v₀ : (SvecSVec Int)),
  ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
   ((SvecSVec.len v₀) ≥ 0) ->
    ((svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0) v₀) = v₀)