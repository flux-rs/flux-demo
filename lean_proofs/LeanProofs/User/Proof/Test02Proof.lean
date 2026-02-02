import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test02

namespace F

def Test02_proof : Test02 := by
  unfold Test02
  -- All kvars are trivially true
  refine ⟨fun _ => True, fun _ => True, fun _ => True, fun _ => True, ?_⟩
  intro _h_slice
  constructor
  · trivial  -- k0 1
  · intro _h_slice1
    intro _h_len1
    constructor
    · intro _ _; trivial  -- ∀ a, k0 a → k1 a
    constructor
    · trivial  -- k1 2
    · intro _h_slice2
      intro _h_len2
      constructor
      · omega  -- 1 < 2
      constructor
      · intro _ _; trivial  -- ∀ a, k1 a → k2 a
      constructor
      · trivial  -- k2 3
      · intro _h_slice3
        constructor
        · omega  -- 2 > 0
        constructor
        · intro _ _; trivial  -- ∀ a, k2 a → k3 a
        · intro _h_slice4
          intro _h_len3
          intro _h_k3
          -- Goal: SmtMap_select (store (store (store empty 0 1) 1 2) 1 3) ((0+1+1)-1) = 3
          -- (0+1+1)-1 = 1, and store ... 1 3 at index 1 gives 3
          simp only [SmtMap_select, SmtMap_store]
          native_decide

end F
