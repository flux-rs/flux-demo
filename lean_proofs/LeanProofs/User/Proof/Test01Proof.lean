import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test01

namespace F

def Test01_proof : Test01 := by
  unfold Test01
  -- Choose k0, k1, k2 to be trivially true
  refine ⟨fun _ => True, fun _ => True, fun _ => True, ?_⟩
  intro _h_slice_empty
  constructor
  · -- k0 1 is True
    trivial
  · intro _h_slice_1
    intro _h_len_1
    constructor
    · -- ∀ a'₀, k0 a'₀ → k1 a'₀
      intro _ _
      trivial
    constructor
    · -- k1 2 is True
      trivial
    · intro _h_slice_2
      intro _h_len_2
      constructor
      · -- (0 + 1) + 1 > 0
        omega
      constructor
      · -- ∀ a'₁, k1 a'₁ → k2 a'₁
        intro _ _
        trivial
      · intro _h_slice_3
        intro _h_len_3
        intro _h_k2
        -- Goal: SmtMap_select (SmtMap_store (SmtMap_store empty 0 1) 1 2) 1 = 2
        -- Simplify: ((0+1)+1)-1 = 1, and store at 1 gives 2
        unfold SmtMap_select SmtMap_store
        simp only [beq_iff_eq]
        -- The index is ((0+1)+1)-1 = 1
        -- SmtMap_store ... 1 2 at index 1 returns 2
        native_decide

end F
