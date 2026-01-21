import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.VSeq
import LeanProofs.User.Fun.Svec2VseqEmpty
import LeanProofs.User.Fun.Svec2VseqPush
import LeanProofs.User.Fun.Svec2VseqPop
import LeanProofs.User.Fun.Svec2VseqGet
import LeanProofs.User.Fun.Svec2VseqLen

namespace F



def Test05 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, 
 ((svec2_vseq_len (t0 := Int) (svec2_vseq_empty (t0 := Int))) = 0) ->
  (((k0 1))) ∧
  (((svec2_vseq_get (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 0) = 1) ->
   ((svec2_vseq_len (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1)) = (0 + 1)) ->
    ((0 + 1) ≥ 0) ->
     (∀ (a'₀ : Int),
      ((k0 a'₀)) ->
       ((k1 a'₀))) ∧
     (((k1 2))) ∧
     (((svec2_vseq_get (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2) (0 + 1)) = 2) ->
      ((svec2_vseq_len (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2)) = ((0 + 1) + 1)) ->
       (((0 + 1) + 1) ≥ 0) ->
        ((((0 + 1) + 1) > 0)) ∧
        (∀ (a'₁ : Int),
         ((k1 a'₁)) ->
          ((k2 a'₁))) ∧
        (((svec2_vseq_len (t0 := Int) (svec2_vseq_pop (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2))) = (((0 + 1) + 1) - 1)) ->
         ((((0 + 1) + 1) - 1) ≥ 0) ->
          ((k2 (svec2_vseq_get (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2) (((0 + 1) + 1) - 1)))) ->
           ((svec2_vseq_get (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2) (((0 + 1) + 1) - 1)) = 2))
        )
     )
  
end F
