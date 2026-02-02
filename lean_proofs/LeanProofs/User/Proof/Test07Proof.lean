import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test07

namespace F

def Test07_proof : Test07 := by
  unfold Test07
  -- k0, k1 : Int -> Prop (can be True)
  -- k2 : Int -> SmtMap Int Int -> Int -> Prop (should track i ≥ 0)
  -- k3 : Int -> SmtMap Int Int -> Int -> Int -> Prop (can be True)
  refine ⟨fun _ => True, fun _ => True, fun i _ _ => i ≥ 0, fun _ _ _ _ => True, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro _ _; trivial  -- ∀ a'₀, a'₀ = 0 → k0 a'₀
  · intro _ _; trivial  -- ∀ a'₁, a'₁ = 0 → k1 a'₁
  · intro _h1 _h2 _h3 _h4 _h5 _h6 _h7
    intro v₀ _h_sorted _h_slice _h_len_nonneg
    constructor
    · -- k2 0 elems len = 0 ≥ 0
      omega
    · intro i₀ h_k2 h_i_lt
      -- h_k2 : i₀ ≥ 0
      constructor
      · -- 0 ≤ i₀ : follows from h_k2
        omega
      constructor
      · intro _; trivial  -- k3
      · intro _h_k3 _a5 _ha5 _hk0 _a6 _ha6 _hk1
        -- k2 (i₀ + 1) elems len = i₀ + 1 ≥ 0
        omega

end F
