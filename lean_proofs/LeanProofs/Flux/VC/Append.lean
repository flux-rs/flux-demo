import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecAppend
import LeanProofs.User.Fun.SvecSvecSlice

namespace F



def Append := 
 ∀ (b₀ : (SvecSVec Int)),
  ∀ (e₀ : (SvecSVec Int)),
   ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems b₀) (SvecSVec.len b₀)) 0 (SvecSVec.len b₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems b₀) (SvecSVec.len b₀))) ->
    ((SvecSVec.len b₀) ≥ 0) ->
     ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems e₀) (SvecSVec.len e₀)) 0 (SvecSVec.len e₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems e₀) (SvecSVec.len e₀))) ->
      ((SvecSVec.len e₀) ≥ 0) ->
       (b₀ = (svec_svec_append (t0 := Int) b₀ (svec_svec_slice (t0 := Int) e₀ 0 0))) ->
        ((svec_svec_slice (t0 := Int) e₀ 0 (SvecSVec.len e₀)) = e₀) ->
         ((0 ≤ (SvecSVec.len e₀))) ∧
         (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_append (t0 := Int) b₀ (svec_svec_slice (t0 := Int) e₀ 0 (SvecSVec.len e₀)))) (SvecSVec.len (svec_svec_append (t0 := Int) b₀ (svec_svec_slice (t0 := Int) e₀ 0 (SvecSVec.len e₀))))) 0 (SvecSVec.len (svec_svec_append (t0 := Int) b₀ (svec_svec_slice (t0 := Int) e₀ 0 (SvecSVec.len e₀))))) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_append (t0 := Int) b₀ (svec_svec_slice (t0 := Int) e₀ 0 (SvecSVec.len e₀)))) (SvecSVec.len (svec_svec_append (t0 := Int) b₀ (svec_svec_slice (t0 := Int) e₀ 0 (SvecSVec.len e₀)))))) ->
          ((SvecSVec.len (svec_svec_append (t0 := Int) b₀ (svec_svec_slice (t0 := Int) e₀ 0 (SvecSVec.len e₀)))) ≥ 0) ->
           ((svec_svec_append (t0 := Int) b₀ (svec_svec_slice (t0 := Int) e₀ 0 (SvecSVec.len e₀))) = (svec_svec_append (t0 := Int) b₀ e₀)))
         
end F
