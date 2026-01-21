import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.VSeq
import LeanProofs.User.Fun.Svec2VseqPush
import LeanProofs.User.Fun.Svec2VseqGet
import LeanProofs.User.Fun.Svec2VseqLen

namespace F



def Svec2LemmaPopPushEq := 
 ∀ (elems₀ : (VSeq Int)),
  ∀ (len₀ : Int),
   ∀ (e₀ : Int),
    ((svec2_vseq_len (t0 := Int) elems₀) = len₀) ->
     (len₀ ≥ 0) ->
      ((svec2_vseq_get (t0 := Int) (svec2_vseq_push (t0 := Int) elems₀ e₀) len₀) = e₀)
end F
