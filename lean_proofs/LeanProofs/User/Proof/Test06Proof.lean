import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test06

namespace F

def Test06_proof : Test06 := by
  unfold Test06
  -- k0, k1, k2, k3 : Int -> Prop (all trivially true)
  refine ⟨fun _ => True, fun _ => True, fun _ => True, fun _ => True, ?_⟩
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
      · omega  -- 1 < 2
      constructor
      · intro _ _; trivial  -- k1 a → k2 a
      constructor
      · trivial  -- k2 3
      · intro _h_get3 _h_len3
        constructor
        · omega  -- 2 > 0
        constructor
        · intro _ _; trivial  -- k2 a → k3 a
        · intro _h_pop_len _h_pop_len_nonneg _h_k3
          -- Goal: get (set (push (push empty 1) 2) 1 3) ((0+1+1)-1) = 3
          -- = get (set (push (push empty 1) 2) 1 3) 1 = 3
          simp only [svec2_vseq_get, svec2_vseq_set, svec2_vseq_push, svec2_vseq_empty, flip]
          native_decide

end F
