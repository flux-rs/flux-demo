import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecEmptySeq
import LeanProofs.User.Fun.SvecSvecSlice
import LeanProofs.User.Fun.SvecIsSorted

namespace F

namespace SortedKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₄ : Int) (a'₅ : (SmtMap Int Int)) (a'₆ : Int) (a'₇ : (SmtMap Int Int)) (a'₈ : Int) : Prop :=
  ((a'₄ ≥ 0) ∧ (0 ≤ a'₄) ∧ (a'₄ ≤ a'₈))
-- acyclic (non-cut) kvars
def k1 (v₀ : (SvecSVec Int)) (i₀ : Int) (res₀ : (SvecSVec Int)) (a'₉ : Int) (a'₁₀ : (SmtMap Int Int)) (a'₁₁ : Int) (a'₁₂ : Int) (a'₁₃ : (SmtMap Int Int)) (a'₁₄ : Int) : Prop :=
  ((a'₁₀ = (SvecSVec.elems v₀)) ∧ (a'₁₁ = (SvecSVec.len v₀)) ∧ (a'₁₂ = i₀) ∧ (a'₁₃ = (SvecSVec.elems res₀)) ∧ (a'₁₄ = (SvecSVec.len res₀)) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀)) (SvecSVec.len v₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len v₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀)) (SvecSVec.len v₀))) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ svec_empty_seq) 0))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) 0) = ((SvecSVec.mkSvecSVec₀ svec_empty_seq) 0)) ∧ (i₀ ≥ 0) ∧ ((SvecSVec.len v₀) ≥ 0) ∧ (i₀ < (SvecSVec.len v₀)) ∧ (0 ≤ i₀) ∧ (i₀ ≤ (SvecSVec.len v₀)))

end SortedKVarSolutions


open SortedKVarSolutions




def Sorted := ∃ k0 : (a0 : Int) -> (a1 : (SmtMap Int Int)) -> (a2 : Int) -> (a3 : (SmtMap Int Int)) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : (SvecSVec Int)) -> (a1 : Int) -> (a2 : (SvecSVec Int)) -> (a3 : Int) -> (a4 : (SmtMap Int Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : (SmtMap Int Int)) -> (a8 : Int) -> Prop, 
 ∀ (v₀ : (SvecSVec Int)),
  ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
   ((SvecSVec.len v₀) ≥ 0) ->
    ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0) 0 0) = (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0)) ->
     (((k0 0 (svec_empty_seq (t0 := Int)) 0 (SvecSVec.elems v₀) (SvecSVec.len v₀)))) ∧
     (∀ (i₀ : Int),
      ∀ (res₀ : (SvecSVec Int)),
       ((k0 i₀ (SvecSVec.elems res₀) (SvecSVec.len res₀) (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
        ((!(i₀ < (SvecSVec.len v₀))) ->
         (svec_is_sorted res₀)) ∧
        ((i₀ < (SvecSVec.len v₀)) ->
         ((0 ≤ i₀)) ∧
         (∀ (a'₂ : Int),
          ((k1 v₀ i₀ res₀ a'₂ (SvecSVec.elems v₀) (SvecSVec.len v₀) i₀ (SvecSVec.elems res₀) (SvecSVec.len res₀)))) ∧
         (((k1 v₀ i₀ res₀ (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v₀) i₀) (SvecSVec.elems v₀) (SvecSVec.len v₀) i₀ (SvecSVec.elems res₀) (SvecSVec.len res₀))) ->
          ((svec_is_sorted res₀)) ∧
          (∀ (v₁ : (SvecSVec Int)),
           (svec_is_sorted v₁) ->
            ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₁) (SvecSVec.len v₁)) 0 (SvecSVec.len v₁)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₁) (SvecSVec.len v₁))) ->
             ((SvecSVec.len v₁) ≥ 0) ->
              ((k0 (i₀ + 1) (SvecSVec.elems v₁) (SvecSVec.len v₁) (SvecSVec.elems v₀) (SvecSVec.len v₀))))
          )
         )
        )
     
end F
