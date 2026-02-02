import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Test03

namespace F

def Test03_proof : Test03 := by
  unfold Test03
  -- k0 : Int -> Prop (should track i ≥ 0)
  -- k1 : Int -> Int -> Prop (can be True)
  refine ⟨fun i => i ≥ 0, fun _ _ => True, ?_⟩
  intro _h1 _h2 _h3 _h4 _h5 _h6 _h7 _h8 _h9
  intro h_len_eq
  constructor
  · -- k0 0 = 0 ≥ 0
    omega
  · intro i₀ h_k0 h_i_lt
    -- h_k0 : i₀ ≥ 0
    constructor
    · -- 0 ≤ i₀ : follows from h_k0
      omega
    · intro h_get_eq
      constructor
      · -- 0 ≤ i₀ : follows from h_k0
        omega
      constructor
      · intro _; trivial  -- k1
      · intro _h_k1 _h_ge
        constructor
        · -- (append.elems i₀) = (i₀ + 1) = true
          -- The vectors are [1,2] ++ [3,4] = [1,2,3,4]
          -- So elems[i] = i+1 for i ∈ {0,1,2,3}
          simp only [svec_svec_append, map_append, SmtMap_select, SmtMap_store, svec_empty_seq] at h_get_eq h_i_lt ⊢
          -- h_i_lt : i₀ < 4, h_k0 : i₀ ≥ 0
          -- Simplify the if-then-else expressions using bounds
          have h_not_neg : ¬(i₀ < 0) := by omega
          simp only [h_not_neg, ↓reduceIte]
          -- The goal now has the form: (if i₀ < 2 then ... else ...) = i₀ + 1 = True
          -- We case split on i₀'s concrete values
          have h_i_cases : i₀ = 0 ∨ i₀ = 1 ∨ i₀ = 2 ∨ i₀ = 3 := by omega
          rcases h_i_cases with rfl | rfl | rfl | rfl <;> native_decide
        · -- k0 (i₀ + 1) = i₀ + 1 ≥ 0
          omega

end F
