import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test05

namespace F

def Test05_proof : Test05 := by
  unfold Test05
  -- k0, k1, k2 : Int -> Prop (all trivially true)
  refine ⟨fun _ => True, fun _ => True, fun _ => True, ?_⟩
  intro _h_empty_len
  constructor
  · trivial  -- k0 1
  · intro _h_get1 _h_len1 _h_len1_nonneg
    constructor
    · intro _ _; trivial  -- k0 a → k1 a
    constructor
    · trivial  -- k1 2
    · intro _h_get2 _h_len2 _h_len2_nonneg
      constructor
      · omega  -- 2 > 0
      constructor
      · intro _ _; trivial  -- k1 a → k2 a
      · intro _h_pop_len _h_pop_len_nonneg _h_k2
        -- Goal: get (push (push empty 1) 2) ((0+1+1)-1) = 2
        -- = get (push (push empty 1) 2) 1 = 2
        simp only [svec2_vseq_get, svec2_vseq_push, svec2_vseq_empty, flip]
        native_decide

end F
