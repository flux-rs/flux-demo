import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Vector
import LeanProofs.User.Fun.Svec3Empty
import LeanProofs.User.Fun.Svec3Push
import LeanProofs.User.Fun.Svec3Pop
import LeanProofs.User.Fun.Svec3Get
import LeanProofs.User.Fun.Svec3Len

namespace F



def Test09 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, 
 ((svec3_len (t0 := Int) (svec3_empty (t0 := Int))) ≥ 0) ->
  (((k0 1))) ∧
  (((svec3_len (t0 := Int) (svec3_push (t0 := Int) (svec3_empty (t0 := Int)) 1)) ≥ 0) ->
   (∀ (a'₀ : Int),
    ((k0 a'₀)) ->
     ((k1 a'₀))) ∧
   (((k1 2))) ∧
   (((svec3_len (t0 := Int) (svec3_push (t0 := Int) (svec3_push (t0 := Int) (svec3_empty (t0 := Int)) 1) 2)) ≥ 0) ->
    (((svec3_len (t0 := Int) (svec3_push (t0 := Int) (svec3_push (t0 := Int) (svec3_empty (t0 := Int)) 1) 2)) > 0)) ∧
    (∀ (a'₁ : Int),
     ((k1 a'₁)) ->
      ((k2 a'₁))) ∧
    (((svec3_len (t0 := Int) (svec3_pop (t0 := Int) (svec3_push (t0 := Int) (svec3_push (t0 := Int) (svec3_empty (t0 := Int)) 1) 2))) ≥ 0) ->
     ((k2 (svec3_get (t0 := Int) (svec3_push (t0 := Int) (svec3_push (t0 := Int) (svec3_empty (t0 := Int)) 1) 2) ((svec3_len (t0 := Int) (svec3_push (t0 := Int) (svec3_push (t0 := Int) (svec3_empty (t0 := Int)) 1) 2)) - 1)))) ->
      ((svec3_get (t0 := Int) (svec3_push (t0 := Int) (svec3_push (t0 := Int) (svec3_empty (t0 := Int)) 1) 2) ((svec3_len (t0 := Int) (svec3_push (t0 := Int) (svec3_push (t0 := Int) (svec3_empty (t0 := Int)) 1) 2)) - 1)) = 2))
    )
   )
  
end F
