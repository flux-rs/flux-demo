import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecEmptySeq
import LeanProofs.User.Fun.SvecSvecSlice
import LeanProofs.User.Fun.SvecIsSorted

namespace F



def Test07 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : (SmtMap Int Int)) -> (a2 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : (SmtMap Int Int)) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k1 a'₁)) ∧
 (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0) 0 0) = (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0)) ->
  ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1)) 0 (0 + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1))) ->
   ((0 + 1) ≥ 0) ->
    ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 2) ((0 + 1) + 1)) 0 ((0 + 1) + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 2) ((0 + 1) + 1))) ->
     (((0 + 1) + 1) ≥ 0) ->
      ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 2) ((0 + 1) + 1) 1) (((0 + 1) + 1) + 1)) 0 (((0 + 1) + 1) + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 2) ((0 + 1) + 1) 1) (((0 + 1) + 1) + 1))) ->
       ((((0 + 1) + 1) + 1) ≥ 0) ->
        ∀ (v₀ : (SvecSVec Int)),
         (svec_is_sorted v₀) ->
          ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
           ((SvecSVec.len v₀) ≥ 0) ->
            (((k2 0 (SvecSVec.elems v₀) (SvecSVec.len v₀)))) ∧
            (∀ (i₀ : Int),
             ((k2 i₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
              (i₀ < (SvecSVec.len v₀)) ->
               ((0 ≤ i₀)) ∧
               (∀ (a'₄ : Int),
                ((k3 a'₄ (SvecSVec.elems v₀) (SvecSVec.len v₀) i₀))) ∧
               (((k3 (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v₀) i₀) (SvecSVec.elems v₀) (SvecSVec.len v₀) i₀)) ->
                ∀ (a'₅ : Int),
                 (a'₅ = 0) ->
                  (k0 a'₅) ->
                   ∀ (a'₆ : Int),
                    (a'₆ = 0) ->
                     (k1 a'₆) ->
                      ((k2 (i₀ + 1) (SvecSVec.elems v₀) (SvecSVec.len v₀))))
               )
            )
 
end F
