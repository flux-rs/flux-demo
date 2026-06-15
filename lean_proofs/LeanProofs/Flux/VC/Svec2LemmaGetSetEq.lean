import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.VSeq
import LeanProofs.User.Fun.Svec2VseqGet
import LeanProofs.User.Fun.Svec2VseqSet
import LeanProofs.User.Fun.Svec2VseqLen


def Svec2LemmaGetSetEq := 
 ∀ (elems₀ : (VSeq Int)),
  ∀ (len₀ : Int),
   ∀ (i₀ : Int),
    ∀ (e₀ : Int),
     ((0 ≤ i₀) ∧ (i₀ < len₀)) ->
      ((svec2_vseq_len (t0 := Int) elems₀) = len₀) ->
       (len₀ ≥ 0) ->
        (i₀ ≥ 0) ->
         ((svec2_vseq_get (t0 := Int) (svec2_vseq_set (t0 := Int) elems₀ i₀ e₀) i₀) = e₀)