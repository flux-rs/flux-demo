import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecSlice
import LeanProofs.User.Fun.SvecIsSorted

namespace F

namespace InPlaceInsertionSortInsertSortedKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₇ : (SmtMap Int Int)) (a'₈ : Int) (a'₉ : Int) (a'₁₀ : (SmtMap Int Int)) (a'₁₁ : Int) (a'₁₂ : Int) (a'₁₃ : Int) : Prop :=
  True
def k1 (a'₁₄ : Int) (a'₁₅ : (SmtMap Int Int)) (a'₁₆ : Int) (a'₁₇ : Int) (a'₁₈ : (SmtMap Int Int)) (a'₁₉ : Int) (a'₂₀ : Int) (a'₂₁ : Int) : Prop :=
  True
-- acyclic (non-cut) kvars
def k3 (v1₀ : (SvecSVec Int)) (sorted_bound₀ : Int) (e₀ : Int) (a'₁ : (SvecSVec Int)) (i₀ : Int) (a'₂₂ : Int) (a'₂₃ : (SmtMap Int Int)) (a'₂₄ : Int) (a'₂₅ : Int) (a'₂₆ : Int) (a'₂₇ : (SmtMap Int Int)) (a'₂₈ : Int) (a'₂₉ : Int) : Prop :=
  ((((svec_is_sorted) : (((SvecSVec Int) -> Bool))) (((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) v1₀)) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) sorted_bound₀)) ∧ (a'₂₃ = (SvecSVec.elems v1₀)) ∧ (a'₂₄ = (SvecSVec.len v1₀)) ∧ (a'₂₅ = sorted_bound₀) ∧ (a'₂₆ = e₀) ∧ (a'₂₇ = (SvecSVec.elems a'₁)) ∧ (a'₂₈ = (SvecSVec.len a'₁)) ∧ (a'₂₉ = i₀) ∧ (e₀ = ((SmtMap_select (SvecSVec.elems v1₀)) sorted_bound₀)) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len v1₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀))) ∧ (sorted_bound₀ ≥ 0) ∧ ((SvecSVec.len v1₀) ≥ 0) ∧ (i₀ < sorted_bound₀) ∧ (sorted_bound₀ < (SvecSVec.len v1₀)) ∧ (1 ≤ sorted_bound₀))
def k5 (v1₀ : (SvecSVec Int)) (sorted_bound₀ : Int) (a'₁ : (SvecSVec Int)) (i₀ : Int) (e₀ : Int) (a'₃₀ : Int) (a'₃₁ : (SmtMap Int Int)) (a'₃₂ : Int) (a'₃₃ : Int) (a'₃₄ : Int) (a'₃₅ : (SmtMap Int Int)) (a'₃₆ : Int) (a'₃₇ : Int) : Prop :=
  (((((svec_is_sorted) : (((SvecSVec Int) -> Bool))) (((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) v1₀)) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) sorted_bound₀)) ∧ (a'₃₀ = ((SmtMap_select (SvecSVec.elems a'₁)) ((sorted_bound₀ - i₀) - 1))) ∧ (a'₃₁ = (SvecSVec.elems v1₀)) ∧ (a'₃₂ = (SvecSVec.len v1₀)) ∧ (a'₃₃ = sorted_bound₀) ∧ (a'₃₄ = e₀) ∧ (a'₃₅ = (SvecSVec.elems a'₁)) ∧ (a'₃₆ = (SvecSVec.len a'₁)) ∧ (a'₃₇ = i₀) ∧ (e₀ = ((SmtMap_select (SvecSVec.elems v1₀)) sorted_bound₀)) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len v1₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀))) ∧ (((SmtMap_select (SvecSVec.elems a'₁)) ((sorted_bound₀ - i₀) - 1)) > e₀) ∧ (sorted_bound₀ ≥ 0) ∧ ((SvecSVec.len v1₀) ≥ 0) ∧ (i₀ < sorted_bound₀) ∧ (sorted_bound₀ < (SvecSVec.len v1₀)) ∧ (1 ≤ sorted_bound₀)) ∨ ((((svec_is_sorted) : (((SvecSVec Int) -> Bool))) (((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) v1₀)) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) sorted_bound₀)) ∧ (a'₃₁ = (SvecSVec.elems v1₀)) ∧ (a'₃₂ = (SvecSVec.len v1₀)) ∧ (a'₃₃ = sorted_bound₀) ∧ (a'₃₄ = e₀) ∧ (a'₃₅ = (SvecSVec.elems a'₁)) ∧ (a'₃₆ = (SvecSVec.len a'₁)) ∧ (a'₃₇ = i₀) ∧ (e₀ = ((SmtMap_select (SvecSVec.elems v1₀)) sorted_bound₀)) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len v1₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀))) ∧ (((SmtMap_select (SvecSVec.elems a'₁)) ((sorted_bound₀ - i₀) - 1)) > e₀) ∧ (sorted_bound₀ ≥ 0) ∧ ((SvecSVec.len v1₀) ≥ 0) ∧ (i₀ < sorted_bound₀) ∧ (sorted_bound₀ < (SvecSVec.len v1₀)) ∧ (1 ≤ sorted_bound₀)))
def k4 (v1₀ : (SvecSVec Int)) (sorted_bound₀ : Int) (e₀ : Int) (a'₁ : (SvecSVec Int)) (i₀ : Int) (a'₃₈ : Int) (a'₃₉ : (SmtMap Int Int)) (a'₄₀ : Int) (a'₄₁ : Int) (a'₄₂ : Int) (a'₄₃ : (SmtMap Int Int)) (a'₄₄ : Int) (a'₄₅ : Int) : Prop :=
  ((((svec_is_sorted) : (((SvecSVec Int) -> Bool))) (((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) v1₀)) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) sorted_bound₀)) ∧ (a'₃₉ = (SvecSVec.elems v1₀)) ∧ (a'₄₀ = (SvecSVec.len v1₀)) ∧ (a'₄₁ = sorted_bound₀) ∧ (a'₄₂ = e₀) ∧ (a'₄₃ = (SvecSVec.elems a'₁)) ∧ (a'₄₄ = (SvecSVec.len a'₁)) ∧ (a'₄₅ = i₀) ∧ (e₀ = ((SmtMap_select (SvecSVec.elems v1₀)) sorted_bound₀)) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len v1₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀))) ∧ (((SmtMap_select (SvecSVec.elems a'₁)) ((sorted_bound₀ - i₀) - 1)) > e₀) ∧ (sorted_bound₀ ≥ 0) ∧ ((SvecSVec.len v1₀) ≥ 0) ∧ (i₀ < sorted_bound₀) ∧ (sorted_bound₀ < (SvecSVec.len v1₀)) ∧ (1 ≤ sorted_bound₀))
def k2 (v1₀ : (SvecSVec Int)) (sorted_bound₀ : Int) (a'₁ : (SvecSVec Int)) (i₀ : Int) (e₀ : Int) (a'₄₆ : (SmtMap Int Int)) (a'₄₇ : Int) (a'₄₈ : Int) (a'₄₉ : Int) (a'₅₀ : (SmtMap Int Int)) (a'₅₁ : Int) (a'₅₂ : Int) : Prop :=
  (((((svec_is_sorted) : (((SvecSVec Int) -> Bool))) (((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) v1₀)) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) sorted_bound₀)) ∧ (¬(((SmtMap_select (SvecSVec.elems a'₁)) ((sorted_bound₀ - i₀) - 1)) > e₀)) ∧ (a'₄₆ = (SvecSVec.elems v1₀)) ∧ (a'₄₇ = (SvecSVec.len v1₀)) ∧ (a'₄₈ = sorted_bound₀) ∧ (a'₄₉ = e₀) ∧ (a'₅₀ = (SvecSVec.elems a'₁)) ∧ (a'₅₁ = (SvecSVec.len a'₁)) ∧ (a'₅₂ = i₀) ∧ (e₀ = ((SmtMap_select (SvecSVec.elems v1₀)) sorted_bound₀)) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len v1₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀))) ∧ (sorted_bound₀ ≥ 0) ∧ ((SvecSVec.len v1₀) ≥ 0) ∧ (i₀ < sorted_bound₀) ∧ (sorted_bound₀ < (SvecSVec.len v1₀)) ∧ (1 ≤ sorted_bound₀)) ∨ ((((svec_is_sorted) : (((SvecSVec Int) -> Bool))) (((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) v1₀)) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) sorted_bound₀)) ∧ (¬(i₀ < sorted_bound₀)) ∧ (a'₄₆ = (SvecSVec.elems v1₀)) ∧ (a'₄₇ = (SvecSVec.len v1₀)) ∧ (a'₄₈ = sorted_bound₀) ∧ (a'₄₉ = e₀) ∧ (a'₅₀ = (SvecSVec.elems a'₁)) ∧ (a'₅₁ = (SvecSVec.len a'₁)) ∧ (a'₅₂ = i₀) ∧ (e₀ = ((SmtMap_select (SvecSVec.elems v1₀)) sorted_bound₀)) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len v1₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀)) (SvecSVec.len v1₀))) ∧ (sorted_bound₀ ≥ 0) ∧ ((SvecSVec.len v1₀) ≥ 0) ∧ (sorted_bound₀ < (SvecSVec.len v1₀)) ∧ (1 ≤ sorted_bound₀)))

end InPlaceInsertionSortInsertSortedKVarSolutions


open InPlaceInsertionSortInsertSortedKVarSolutions




def InPlaceInsertionSortInsertSorted := ∃ k0 : (a0 : (SmtMap Int Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (SmtMap Int Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (SmtMap Int Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : (SmtMap Int Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k2 : (a0 : (SvecSVec Int)) -> (a1 : Int) -> (a2 : (SvecSVec Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : (SmtMap Int Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (SmtMap Int Int)) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k3 : (a0 : (SvecSVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (SvecSVec Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : (SmtMap Int Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : (SmtMap Int Int)) -> (a11 : Int) -> (a12 : Int) -> Prop, ∃ k4 : (a0 : (SvecSVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (SvecSVec Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : (SmtMap Int Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : (SmtMap Int Int)) -> (a11 : Int) -> (a12 : Int) -> Prop, ∃ k5 : (a0 : (SvecSVec Int)) -> (a1 : Int) -> (a2 : (SvecSVec Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : (SmtMap Int Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : (SmtMap Int Int)) -> (a11 : Int) -> (a12 : Int) -> Prop, 
 ∀ (v1₀ : (SvecSVec Int)),
  ∀ (sorted_bound₀ : Int),
   ∀ (e₀ : Int),
    (svec_is_sorted (svec_svec_slice (t0 := Int) v1₀ 0 sorted_bound₀)) ->
     ((1 ≤ sorted_bound₀) ∧ (sorted_bound₀ < (SvecSVec.len v1₀))) ->
      (e₀ = (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v1₀) sorted_bound₀)) ->
       ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀)) 0 (SvecSVec.len v1₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀))) ->
        ((SvecSVec.len v1₀) ≥ 0) ->
         (sorted_bound₀ ≥ 0) ->
          (((k0 (SvecSVec.elems v1₀) (SvecSVec.len v1₀) 0 (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀))) ∧
          (∀ (a'₀ : Int),
           ((k1 a'₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) 0 (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀))) ∧
          (∀ (a'₁ : (SvecSVec Int)),
           ∀ (i₀ : Int),
            ((k0 (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀)) ->
             ((!(i₀ < sorted_bound₀)) ->
              ((k2 v1₀ sorted_bound₀ a'₁ i₀ e₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀))) ∧
             ((i₀ < sorted_bound₀) ->
              (((sorted_bound₀ - i₀) ≥ 0)) ∧
              ((((sorted_bound₀ - i₀) - 1) ≥ 0)) ∧
              (((0 ≤ ((sorted_bound₀ - i₀) - 1))) ∧
              ((((sorted_bound₀ - i₀) - 1) < (SvecSVec.len a'₁)))
              ) ∧
              (∀ (a'₃ : Int),
               ((k1 a'₃ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀)) ->
                ((k3 v1₀ sorted_bound₀ e₀ a'₁ i₀ a'₃ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀))) ∧
              (((k3 v1₀ sorted_bound₀ e₀ a'₁ i₀ (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) ((sorted_bound₀ - i₀) - 1)) (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀)) ->
               ((!((SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) ((sorted_bound₀ - i₀) - 1)) > e₀)) ->
                ((k2 v1₀ sorted_bound₀ a'₁ i₀ e₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀))) ∧
               (((SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) ((sorted_bound₀ - i₀) - 1)) > e₀) ->
                (((sorted_bound₀ - i₀) ≥ 0)) ∧
                (((sorted_bound₀ - i₀) ≥ 0)) ∧
                ((((sorted_bound₀ - i₀) - 1) ≥ 0)) ∧
                (((0 ≤ ((sorted_bound₀ - i₀) - 1))) ∧
                ((((sorted_bound₀ - i₀) - 1) < (SvecSVec.len a'₁)))
                ) ∧
                (∀ (a'₄ : Int),
                 ((k1 a'₄ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀)) ->
                  ((k4 v1₀ sorted_bound₀ e₀ a'₁ i₀ a'₄ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀))) ∧
                (((k4 v1₀ sorted_bound₀ e₀ a'₁ i₀ (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) ((sorted_bound₀ - i₀) - 1)) (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀)) ->
                 (((0 ≤ (sorted_bound₀ - i₀))) ∧
                 (((sorted_bound₀ - i₀) < (SvecSVec.len a'₁)))
                 ) ∧
                 (∀ (a'₅ : Int),
                  ((k1 a'₅ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀)) ->
                   ((k5 v1₀ sorted_bound₀ a'₁ i₀ e₀ a'₅ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀))) ∧
                 (((k5 v1₀ sorted_bound₀ a'₁ i₀ e₀ (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) ((sorted_bound₀ - i₀) - 1)) (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀))) ∧
                 (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) (sorted_bound₀ - i₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) ((sorted_bound₀ - i₀) - 1))) (SvecSVec.len a'₁)) 0 (SvecSVec.len a'₁)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) (sorted_bound₀ - i₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) ((sorted_bound₀ - i₀) - 1))) (SvecSVec.len a'₁))) ->
                  ((SvecSVec.len a'₁) ≥ 0) ->
                   (((k0 (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) (sorted_bound₀ - i₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) ((sorted_bound₀ - i₀) - 1))) (SvecSVec.len a'₁) (i₀ + 1) (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀))) ∧
                   (∀ (a'₆ : Int),
                    ((k5 v1₀ sorted_bound₀ a'₁ i₀ e₀ a'₆ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀)) ->
                     ((k1 a'₆ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) (sorted_bound₀ - i₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) ((sorted_bound₀ - i₀) - 1))) (SvecSVec.len a'₁) (i₀ + 1) (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀)))
                   )
                 )
                )
               )
              ) ∧
             (((k2 v1₀ sorted_bound₀ a'₁ i₀ e₀ (SvecSVec.elems v1₀) (SvecSVec.len v1₀) sorted_bound₀ e₀ (SvecSVec.elems a'₁) (SvecSVec.len a'₁) i₀)) ->
              (((sorted_bound₀ - i₀) ≥ 0)) ∧
              (((0 ≤ (sorted_bound₀ - i₀))) ∧
              (((sorted_bound₀ - i₀) < (SvecSVec.len a'₁)))
              ) ∧
              (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) (sorted_bound₀ - i₀) e₀) (SvecSVec.len a'₁)) 0 (SvecSVec.len a'₁)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) (sorted_bound₀ - i₀) e₀) (SvecSVec.len a'₁))) ->
               ((SvecSVec.len a'₁) ≥ 0) ->
                ((svec_is_sorted (svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems a'₁) (sorted_bound₀ - i₀) e₀) (SvecSVec.len a'₁)) 0 (sorted_bound₀ + 1)))) ∧
                (((SvecSVec.len a'₁) = (SvecSVec.len v1₀)))
                )
              )
             )
          
end F
