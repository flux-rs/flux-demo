import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecAppend
import LeanProofs.User.Fun.SvecSvecSlice

namespace F



def AppendHelp := ∃ k0 : (a0 : Int) -> (a1 : (SmtMap Int Int)) -> (a2 : Int) -> (a3 : (SmtMap Int Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : (SmtMap Int Int)) -> (a7 : Int) -> Prop, 
 ∀ (b₀ : (SvecSVec Int)),
  ∀ (e₀ : (SvecSVec Int)),
   ∀ (ext_idx₀ : Int),
    ∀ (l₀ : (SvecSVec Int)),
     ((b₀ = (svec_svec_append (t0 := Int) l₀ (svec_svec_slice (t0 := Int) e₀ 0 ext_idx₀))) ∧ ((SvecSVec.len l₀) ≥ 0)) ->
      ((0 ≤ ext_idx₀) ∧ (ext_idx₀ ≤ (SvecSVec.len e₀))) ->
       ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems b₀) (SvecSVec.len b₀)) 0 (SvecSVec.len b₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems b₀) (SvecSVec.len b₀))) ->
        ((SvecSVec.len b₀) ≥ 0) ->
         ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems e₀) (SvecSVec.len e₀)) 0 (SvecSVec.len e₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems e₀) (SvecSVec.len e₀))) ->
          ((SvecSVec.len e₀) ≥ 0) ->
           (ext_idx₀ ≥ 0) ->
            ((!(ext_idx₀ < (SvecSVec.len e₀))) ->
             (b₀ = (svec_svec_append (t0 := Int) l₀ (svec_svec_slice (t0 := Int) e₀ 0 (SvecSVec.len e₀))))) ∧
            ((ext_idx₀ < (SvecSVec.len e₀)) ->
             ((SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems b₀) (SvecSVec.len b₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems e₀) ext_idx₀)) ((SvecSVec.len b₀) + 1)) = (svec_svec_append (t0 := Int) l₀ (svec_svec_slice (t0 := Int) e₀ 0 (ext_idx₀ + 1)))) ->
              (∀ (a'₀ : Int),
               ((k0 a'₀ (SvecSVec.elems b₀) (SvecSVec.len b₀) (SvecSVec.elems e₀) (SvecSVec.len e₀) ext_idx₀ (SvecSVec.elems l₀) (SvecSVec.len l₀)))) ∧
              (((k0 (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems e₀) ext_idx₀) (SvecSVec.elems b₀) (SvecSVec.len b₀) (SvecSVec.elems e₀) (SvecSVec.len e₀) ext_idx₀ (SvecSVec.elems l₀) (SvecSVec.len l₀))) ->
               ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems b₀) (SvecSVec.len b₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems e₀) ext_idx₀)) ((SvecSVec.len b₀) + 1)) 0 ((SvecSVec.len b₀) + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems b₀) (SvecSVec.len b₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems e₀) ext_idx₀)) ((SvecSVec.len b₀) + 1))) ->
                (((SvecSVec.len b₀) + 1) ≥ 0) ->
                 ((0 ≤ (ext_idx₀ + 1))) ∧
                 (((ext_idx₀ + 1) ≤ (SvecSVec.len e₀)))
                 )
              )
            
end F
