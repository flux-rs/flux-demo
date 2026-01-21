import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.VSeq
import LeanProofs.User.Fun.Svec2VseqEmpty
import LeanProofs.User.Fun.Svec2VseqPush
import LeanProofs.User.Fun.Svec2VseqPop
import LeanProofs.User.Fun.Svec2VseqGet
import LeanProofs.User.Fun.Svec2VseqSet
import LeanProofs.User.Fun.Svec2VseqLen

namespace F



def Test06 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, 
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
        ((1 < ((0 + 1) + 1))) ∧
        (∀ (a'₁ : Int),
         ((k1 a'₁)) ->
          ((k2 a'₁))) ∧
        (((k2 3))) ∧
        (((svec2_vseq_get (t0 := Int) (svec2_vseq_set (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2) 1 3) 1) = 3) ->
         ((svec2_vseq_len (t0 := Int) (svec2_vseq_set (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2) 1 3)) = ((0 + 1) + 1)) ->
          ((((0 + 1) + 1) > 0)) ∧
          (∀ (a'₂ : Int),
           ((k2 a'₂)) ->
            ((k3 a'₂))) ∧
          (((svec2_vseq_len (t0 := Int) (svec2_vseq_pop (t0 := Int) (svec2_vseq_set (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2) 1 3))) = (((0 + 1) + 1) - 1)) ->
           ((((0 + 1) + 1) - 1) ≥ 0) ->
            ((k3 (svec2_vseq_get (t0 := Int) (svec2_vseq_set (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2) 1 3) (((0 + 1) + 1) - 1)))) ->
             ((svec2_vseq_get (t0 := Int) (svec2_vseq_set (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_push (t0 := Int) (svec2_vseq_empty (t0 := Int)) 1) 2) 1 3) (((0 + 1) + 1) - 1)) = 3))
          )
        )
     )
  
end F
