import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecSvecAppend
import LeanProofs.User.Fun.SvecSvecSlice

namespace F



def Insert := 
 ∀ (v₀ : (SvecSVec Int)),
  ∀ (pos₀ : Int),
   ∀ (e₀ : Int),
    ((0 ≤ pos₀) ∧ (pos₀ ≤ (SvecSVec.len v₀))) ->
     ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀)) 0 (SvecSVec.len v₀)) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems v₀) (SvecSVec.len v₀))) ->
      ((SvecSVec.len v₀) ≥ 0) ->
       (pos₀ ≥ 0) ->
        (((SvecSVec.len v₀) ≤ (SvecSVec.len v₀))) ∧
        (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀))) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀)))) 0 (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀)))) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀))) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀))))) ->
         ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀))) ≥ 0) ->
          ((0 ≤ (SvecSVec.len v₀))) ∧
          (((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) = (pos₀ - 0)) ->
           ((0 ≤ (SvecSVec.len v₀))) ∧
           (((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀))) 0 (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀))) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)))) ->
            ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) ≥ 0) ->
             ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) e₀) ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1)) 0 ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) e₀) ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1))) ->
              (((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1) ≥ 0) ->
               ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) e₀) ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1)) (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀)))) (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) e₀) ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1)) (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀))))) 0 (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) e₀) ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1)) (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀))))) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) e₀) ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1)) (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀)))) (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) e₀) ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1)) (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀)))))) ->
                ((SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) e₀) ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1)) (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀)))) ≥ 0) ->
                 ((svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) (SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) e₀) ((SvecSVec.len (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) + 1)) (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀))) = (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_slice (t0 := Int) v₀ 0 pos₀)) pos₀ e₀) (pos₀ + 1)) (svec_svec_slice (t0 := Int) v₀ pos₀ (SvecSVec.len v₀)))))
           )
          )
        
end F
