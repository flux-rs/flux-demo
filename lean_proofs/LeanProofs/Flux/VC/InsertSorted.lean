import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecAppend
import LeanProofs.User.Fun.SvecSvecSlice
import LeanProofs.User.Fun.SvecIsSorted
namespace InsertSortedKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₂ : Int) (a'₃ : (SmtMap Int Int)) (a'₄ : Int) (a'₅ : Int) : Prop :=
  ((a'₂ ≥ 0) ∧ (0 ≤ a'₂) ∧ (a'₂ ≤ a'₄))
-- acyclic (non-cut) kvars
def k1 (s₀ : (SvecSVec Int)) (e₀ : Int) (i₀ : Int) (a'₆ : (SmtMap Int Int)) (a'₇ : Int) (a'₈ : Int) (a'₉ : Int) : Prop :=
  (((((svec_is_sorted) : (((SvecSVec Int) -> Bool))) s₀) ∧ (¬(e₀ > ((SmtMap_select (SvecSVec.elems s₀)) i₀))) ∧ (a'₆ = (SvecSVec.elems s₀)) ∧ (a'₇ = (SvecSVec.len s₀)) ∧ (a'₈ = e₀) ∧ (a'₉ = i₀) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀)) (SvecSVec.len s₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len s₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀)) (SvecSVec.len s₀))) ∧ (i₀ ≥ 0) ∧ ((SvecSVec.len s₀) ≥ 0) ∧ (i₀ < (SvecSVec.len s₀)) ∧ (0 ≤ i₀) ∧ (i₀ ≤ (SvecSVec.len s₀))) ∨ ((((svec_is_sorted) : (((SvecSVec Int) -> Bool))) s₀) ∧ (¬(i₀ < (SvecSVec.len s₀))) ∧ (a'₆ = (SvecSVec.elems s₀)) ∧ (a'₇ = (SvecSVec.len s₀)) ∧ (a'₈ = e₀) ∧ (a'₉ = i₀) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀)) (SvecSVec.len s₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len s₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀)) (SvecSVec.len s₀))) ∧ (i₀ ≥ 0) ∧ ((SvecSVec.len s₀) ≥ 0) ∧ (0 ≤ i₀) ∧ (i₀ ≤ (SvecSVec.len s₀))))
def k2 (s₀ : (SvecSVec Int)) (e₀ : Int) (i₀ : Int) (a'₁₀ : Int) (a'₁₁ : (SmtMap Int Int)) (a'₁₂ : Int) (a'₁₃ : Int) (a'₁₄ : Int) : Prop :=
  ((((svec_is_sorted) : (((SvecSVec Int) -> Bool))) s₀) ∧ (a'₁₁ = (SvecSVec.elems s₀)) ∧ (a'₁₂ = (SvecSVec.len s₀)) ∧ (a'₁₃ = e₀) ∧ (a'₁₄ = i₀) ∧ ((((((((((svec_svec_slice) : (((SvecSVec Int) -> (Int -> (Int -> (SvecSVec Int)))))) ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀)) (SvecSVec.len s₀)))) : ((Int -> (Int -> (SvecSVec Int))))) 0)) : ((Int -> (SvecSVec Int)))) (SvecSVec.len s₀)) = ((SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀)) (SvecSVec.len s₀))) ∧ (i₀ ≥ 0) ∧ ((SvecSVec.len s₀) ≥ 0) ∧ (i₀ < (SvecSVec.len s₀)) ∧ (0 ≤ i₀) ∧ (i₀ ≤ (SvecSVec.len s₀)))

end InsertSortedKVarSolutions


open InsertSortedKVarSolutions




def InsertSorted := ∃ k0 : (a0 : Int) -> (a1 : (SmtMap Int Int)) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : (SvecSVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (SmtMap Int Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k2 : (a0 : (SvecSVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (SmtMap Int Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, 
 ∀ (s₀ : (SvecSVec Int)),
  ∀ (e₀ : Int),
   (svec_is_sorted s₀) ->
    ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀) (SvecSVec.len s₀)) 0 (SvecSVec.len s₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀) (SvecSVec.len s₀))) ->
     ((SvecSVec.len s₀) ≥ 0) ->
      (((k0 0 (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀))) ∧
      (∀ (i₀ : Int),
       ((k0 i₀ (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀)) ->
        ((!(i₀ < (SvecSVec.len s₀))) ->
         ((k1 s₀ e₀ i₀ (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀ i₀))) ∧
        ((i₀ < (SvecSVec.len s₀)) ->
         ((0 ≤ i₀)) ∧
         (∀ (a'₁ : Int),
          ((k2 s₀ e₀ i₀ a'₁ (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀ i₀))) ∧
         (((k2 s₀ e₀ i₀ (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems s₀) i₀) (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀ i₀)) ->
          ((!(e₀ > (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems s₀) i₀))) ->
           ((k1 s₀ e₀ i₀ (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀ i₀))) ∧
          ((e₀ > (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems s₀) i₀)) ->
           ((k0 (i₀ + 1) (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀)))
          )
         ) ∧
        (((k1 s₀ e₀ i₀ (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀ i₀)) ->
         ((i₀ ≠ (SvecSVec.len s₀)) ->
          (((0 ≤ i₀)) ∧
          ((i₀ ≤ (SvecSVec.len s₀)))
          ) ∧
          (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) s₀ 0 i₀)) i₀ e₀) (i₀ + 1)) (svec_svec_slice (t0 := Int) s₀ i₀ (SvecSVec.len s₀)))) (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) s₀ 0 i₀)) i₀ e₀) (i₀ + 1)) (svec_svec_slice (t0 := Int) s₀ i₀ (SvecSVec.len s₀))))) 0 (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) s₀ 0 i₀)) i₀ e₀) (i₀ + 1)) (svec_svec_slice (t0 := Int) s₀ i₀ (SvecSVec.len s₀))))) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) s₀ 0 i₀)) i₀ e₀) (i₀ + 1)) (svec_svec_slice (t0 := Int) s₀ i₀ (SvecSVec.len s₀)))) (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) s₀ 0 i₀)) i₀ e₀) (i₀ + 1)) (svec_svec_slice (t0 := Int) s₀ i₀ (SvecSVec.len s₀)))))) ->
           ((SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) s₀ 0 i₀)) i₀ e₀) (i₀ + 1)) (svec_svec_slice (t0 := Int) s₀ i₀ (SvecSVec.len s₀)))) ≥ 0) ->
            (svec_is_sorted (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) s₀ 0 i₀)) i₀ e₀) (i₀ + 1)) (svec_svec_slice (t0 := Int) s₀ i₀ (SvecSVec.len s₀)))))
          ) ∧
         ((!(i₀ ≠ (SvecSVec.len s₀))) ->
          ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀) ((SvecSVec.len s₀) + 1)) 0 ((SvecSVec.len s₀) + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀) ((SvecSVec.len s₀) + 1))) ->
           (((SvecSVec.len s₀) + 1) ≥ 0) ->
            (svec_is_sorted (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems s₀) (SvecSVec.len s₀) e₀) ((SvecSVec.len s₀) + 1))))
         )
        )
      