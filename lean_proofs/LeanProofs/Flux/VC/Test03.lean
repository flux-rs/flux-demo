import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.User.Fun.SvecEmptySeq
import LeanProofs.User.Fun.SvecSvecAppend
import LeanProofs.User.Fun.SvecSvecSlice

namespace F



def Test03 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0) 0 0) = (SvecSVec.mkSvecSVec₀ (svec_empty_seq (t0 := Int)) 0)) ->
  ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1)) 0 (0 + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1))) ->
   ((0 + 1) ≥ 0) ->
    ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) 0 ((0 + 1) + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1))) ->
     (((0 + 1) + 1) ≥ 0) ->
      ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1)) 0 (0 + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1))) ->
       ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)) 0 ((0 + 1) + 1)) = (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1))) ->
        ((svec_svec_slice (t0 := Int) (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)))) (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1))))) 0 (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1))))) = (SvecSVec.mkSvecSVec₀ (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)))) (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)))))) ->
         ((SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)))) ≥ 0) ->
          ((SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)))) = (((0 + 1) + 1) + ((0 + 1) + 1))) ->
           (((k0 0))) ∧
           (∀ (i₀ : Int),
            ((k0 i₀)) ->
             (i₀ < (SvecSVec.len (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1))))) ->
              ((0 ≤ i₀)) ∧
              (((SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)))) i₀) = (if (i₀ < ((0 + 1) + 1)) then (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) i₀) else (SmtMap_select (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) (i₀ - ((0 + 1) + 1))))) ->
               ((0 ≤ i₀)) ∧
               (∀ (a'₁ : Int),
                ((k1 a'₁ i₀))) ∧
               (((k1 (SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)))) i₀) i₀)) ->
                ((SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)))) i₀) ≥ 0) ->
                 ((((SmtMap_select (t0 := Int) (t1 := Int) (SvecSVec.elems (svec_svec_append (t0 := Int) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 1) (0 + 1) 2) ((0 + 1) + 1)) (SvecSVec.mkSvecSVec₀ (SmtMap_store (t0 := Int) (t1 := Int) (SmtMap_store (t0 := Int) (t1 := Int) (svec_empty_seq (t0 := Int)) 0 3) (0 + 1) 4) ((0 + 1) + 1)))) i₀) = (i₀ + 1)) = true)) ∧
                 (((k0 (i₀ + 1))))
                 )
               )
              )
           
end F
