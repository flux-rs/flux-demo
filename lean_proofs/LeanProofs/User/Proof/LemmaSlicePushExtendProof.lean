import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSlicePushExtend

namespace F

def LemmaSlicePushExtend_proof : LemmaSlicePushExtend := by
  unfold LemmaSlicePushExtend
  intro v₀ l₀ r₀ h_l_lt_len h_bounds h_self_slice h_len_nonneg h_l_nonneg h_r_nonneg
  obtain ⟨h_l_le_r, h_r_lt_len⟩ := h_bounds
  -- Goal: mkSvecSVec₀ (store (elems (slice v₀ l₀ r₀)) (r₀ - l₀) (v₀.elems r₀)) ((r₀ - l₀) + 1)
  --     = slice v₀ l₀ (r₀ + 1)
  simp only [svec_svec_slice, map_slice, SmtMap_select]
  ext
  -- Prove elems are equal (functional extensionality)
  · funext x
    -- SmtMap_store returns v if x == key, else the original map
    unfold SmtMap_store
    simp only [beq_iff_eq]
    by_cases hx : x = r₀ - l₀
    · -- x = r₀ - l₀: LHS is v₀.elems r₀, RHS should also be v₀.elems r₀
      simp only [hx, ↓reduceIte]
      have h1 : 0 ≤ r₀ - l₀ := by omega
      have h2 : r₀ - l₀ < r₀ + 1 - l₀ := by omega
      simp only [h1, h2, and_self, ↓reduceIte]
      congr 1
      omega
    · -- x ≠ r₀ - l₀
      simp only [hx, ↓reduceIte]
      by_cases h_in_old : 0 ≤ x ∧ x < r₀ - l₀
      · -- x is in the old slice range
        have h_in_new : 0 ≤ x ∧ x < r₀ + 1 - l₀ := by omega
        simp only [h_in_old, h_in_new]
      · -- x is outside the old slice range
        simp only [h_in_old, ↓reduceIte]
        by_cases h_in_new : 0 ≤ x ∧ x < r₀ + 1 - l₀
        · -- x is in new range but not old: must be x = r₀ - l₀, contradiction
          omega
        · simp only [h_in_new, ↓reduceIte]
  -- Prove lengths are equal
  · have h : ¬(r₀ + 1 - l₀ < 0) := by omega
    simp only [h, ↓reduceIte]
    omega

end F
