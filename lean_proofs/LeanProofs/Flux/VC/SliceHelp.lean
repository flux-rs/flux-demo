import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecSlice

namespace F



def SliceHelp := ∃ k0 : (a0 : Int) -> (a1 : (SmtMap Int Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : (SmtMap Int Int)) -> (a6 : Int) -> Prop, 
 ∀ (v₀ : (SvecSVec Int)),
  ∀ (l₀ : Int),
   ∀ (r₀ : Int),
    ∀ (s₀ : (SvecSVec Int)),
     (((l₀ + (SvecSVec.len s₀)) ≤ r₀) ∧ (s₀ = (svec_svec_slice (t0 := Int) v₀ l₀ (l₀ + (SvecSVec.len s₀))))) ->
      ((0 ≤ l₀) ∧ (l₀ ≤ (SvecSVec.len v₀))) ->
       ((l₀ ≤ r₀) ∧ (r₀ ≤ (SvecSVec.len v₀))) ->
        ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
         ((SvecSVec.len v₀) ≥ 0) ->
          (l₀ ≥ 0) ->
           (r₀ ≥ 0) ->
            ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀) (SvecSVec.len s₀)) 0 (SvecSVec.len s₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems s₀) (SvecSVec.len s₀))) ->
             ((SvecSVec.len s₀) ≥ 0) ->
              ((!((l₀ + (SvecSVec.len s₀)) < r₀)) ->
               (s₀ = (svec_svec_slice (t0 := Int) v₀ l₀ r₀))) ∧
              (((l₀ + (SvecSVec.len s₀)) < r₀) ->
               ((l₀ < (SvecSVec.len v₀))) ∧
               (((l₀ ≤ (l₀ + (SvecSVec.len s₀)))) ∧
               (((l₀ + (SvecSVec.len s₀)) < (SvecSVec.len v₀)))
               ) ∧
               (((SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ l₀ (l₀ + (SvecSVec.len s₀)))) ((l₀ + (SvecSVec.len s₀)) - l₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v₀) (l₀ + (SvecSVec.len s₀)))) (((l₀ + (SvecSVec.len s₀)) - l₀) + 1)) = (svec_svec_slice (t0 := Int) v₀ l₀ ((l₀ + (SvecSVec.len s₀)) + 1))) ->
                (((0 ≤ (l₀ + (SvecSVec.len s₀)))) ∧
                (((l₀ + (SvecSVec.len s₀)) < (SvecSVec.len v₀)))
                ) ∧
                (∀ (a'₀ : Int),
                 ((k0 a'₀ (SvecSVec.elems v₀) (SvecSVec.len v₀) l₀ r₀ (SvecSVec.elems s₀) (SvecSVec.len s₀)))) ∧
                (((k0 (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v₀) (l₀ + (SvecSVec.len s₀))) (SvecSVec.elems v₀) (SvecSVec.len v₀) l₀ r₀ (SvecSVec.elems s₀) (SvecSVec.len s₀))) ->
                 ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems s₀) (SvecSVec.len s₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v₀) (l₀ + (SvecSVec.len s₀)))) ((SvecSVec.len s₀) + 1)) 0 ((SvecSVec.len s₀) + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems s₀) (SvecSVec.len s₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v₀) (l₀ + (SvecSVec.len s₀)))) ((SvecSVec.len s₀) + 1))) ->
                  (((SvecSVec.len s₀) + 1) ≥ 0) ->
                   (((l₀ + ((SvecSVec.len s₀) + 1)) ≤ r₀)) ∧
                   (((SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems s₀) (SvecSVec.len s₀) (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems v₀) (l₀ + (SvecSVec.len s₀)))) ((SvecSVec.len s₀) + 1)) = (svec_svec_slice (t0 := Int) v₀ l₀ (l₀ + ((SvecSVec.len s₀) + 1)))))
                   )
                )
               )
              
end F
