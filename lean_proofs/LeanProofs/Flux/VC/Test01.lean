import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecDefaultElem
import LeanProofs.User.Fun.SvecEmptySeq
import LeanProofs.User.Fun.SvecSvecSlice

namespace F



def Test01 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, 
 ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0) 0 0) = (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0)) ->
  (((k0 1))) ∧
  (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1)) 0 (0 + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1))) ->
   ((0 + 1) ≥ 0) ->
    (∀ (a'₀ : Int),
     ((k0 a'₀)) ->
      ((k1 a'₀))) ∧
    (((k1 2))) ∧
    (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) 0 ((0 + 1) + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1))) ->
     (((0 + 1) + 1) ≥ 0) ->
      ((((0 + 1) + 1) > 0)) ∧
      (∀ (a'₁ : Int),
       ((k1 a'₁)) ->
        ((k2 a'₁))) ∧
      (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) (((0 + 1) + 1) - 1) (svec_default_elem (t0 := Int))) (((0 + 1) + 1) - 1)) 0 (((0 + 1) + 1) - 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) (((0 + 1) + 1) - 1) (svec_default_elem (t0 := Int))) (((0 + 1) + 1) - 1))) ->
       ((((0 + 1) + 1) - 1) ≥ 0) ->
        ((k2 (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) (((0 + 1) + 1) - 1)))) ->
         ((SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) (((0 + 1) + 1) - 1)) = 2))
      )
    )
  
end F
