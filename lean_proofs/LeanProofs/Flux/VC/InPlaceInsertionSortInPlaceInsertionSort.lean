import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecSlice
import LeanProofs.User.Fun.SvecIsSorted

namespace F

namespace InPlaceInsertionSortInPlaceInsertionSortKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₅ : (SmtMap Int Int)) (a'₆ : Int) (a'₇ : Int) (a'₈ : (SmtMap Int Int)) (a'₉ : Int) : Prop :=
  True
-- acyclic (non-cut) kvars
def k1 (vec₀ : (SvecSVec Int)) (a'₁ : (SvecSVec Int)) (i₀ : Int) (a'₁₀ : Int) (a'₁₁ : (SmtMap Int Int)) (a'₁₂ : Int) (a'₁₃ : (SmtMap Int Int)) (a'₁₄ : Int) (a'₁₅ : Int) : Prop :=
  ((¬((SvecSVec.len vec₀) ≤ 1)) ∧ (a'₁₁ = (SvecSVec.elems vec₀)) ∧ (a'₁₂ = (SvecSVec.len vec₀)) ∧ (a'₁₃ = (SvecSVec.elems a'₁)) ∧ (a'₁₄ = (SvecSVec.len a'₁)) ∧ (a'₁₅ = i₀) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems vec₀)) (SvecSVec.len vec₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len vec₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems vec₀)) (SvecSVec.len vec₀))) ∧ ((SvecSVec.len vec₀) ≥ 0) ∧ ((SvecSVec.len a'₁) ≥ 0) ∧ (i₀ < (SvecSVec.len a'₁)))

end InPlaceInsertionSortInPlaceInsertionSortKVarSolutions


open InPlaceInsertionSortInPlaceInsertionSortKVarSolutions




def InPlaceInsertionSortInPlaceInsertionSort := ∃ k0 : (a0 : (SmtMap Int Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (SmtMap Int Int)) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : (SvecSVec Int)) -> (a1 : (SvecSVec Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : (SmtMap Int Int)) -> (a5 : Int) -> (a6 : (SmtMap Int Int)) -> (a7 : Int) -> (a8 : Int) -> Prop, 
 ∀ (vec₀ : (SvecSVec Int)),
  ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems vec₀) (SvecSVec.len vec₀)) 0 (SvecSVec.len vec₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems vec₀) (SvecSVec.len vec₀))) ->
   ((SvecSVec.len vec₀) ≥ 0) ->
    ((!((SvecSVec.len vec₀) ≤ 1)) ->
     (((k0 (SvecSVec.elems vec₀) (SvecSVec.len vec₀) 1 (SvecSVec.elems vec₀) (SvecSVec.len vec₀)))) ∧
     (∀ (a'₁ : (SvecSVec Int)),
      ∀ (i₀ : Int),
       ((k0 (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀ (SvecSVec.elems vec₀) (SvecSVec.len vec₀))) ->
        ((SvecSVec.len a'₁) ≥ 0) ->
         ((!(i₀ < (SvecSVec.len a'₁))) ->
          (svec_is_sorted a'₁)) ∧
         ((i₀ < (SvecSVec.len a'₁)) ->
          ((0 ≤ i₀)) ∧
          (∀ (a'₃ : Int),
           ((k1 vec₀ a'₁ i₀ a'₃ (SvecSVec.elems vec₀) (SvecSVec.len vec₀) (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀))) ∧
          (((k1 vec₀ a'₁ i₀ (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) i₀) (SvecSVec.elems vec₀) (SvecSVec.len vec₀) (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀)) ->
           ((svec_is_sorted (svec_svec_slice (t0 := Int) a'₁ 0 i₀))) ∧
           ((1 ≤ i₀)) ∧
           (∀ (v₀ : (SvecSVec Int)),
            ((svec_is_sorted (svec_svec_slice (t0 := Int) v₀ 0 (i₀ + 1))) ∧ ((SvecSVec.len v₀) = (SvecSVec.len a'₁))) ->
             ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
              ((SvecSVec.len v₀) ≥ 0) ->
               ((k0 (SvecSVec.elems v₀) (SvecSVec.len v₀) (i₀ + 1) (SvecSVec.elems vec₀) (SvecSVec.len vec₀))))
           )
          )
         )
     ) ∧
    (((SvecSVec.len vec₀) ≤ 1) ->
     (svec_is_sorted vec₀))
    
end F
