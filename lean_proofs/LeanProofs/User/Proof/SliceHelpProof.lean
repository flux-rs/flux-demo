import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SliceHelp

namespace F

def SliceHelp_proof : SliceHelp := by
  unfold SliceHelp
  -- Choose k0 to be trivially true
  refine ⟨fun _ _ _ _ _ _ _ => True, ?_⟩
  intro v₀ l₀ r₀ s₀
  intro h1
  obtain ⟨h_sum_le_r, h_s_eq_slice⟩ := h1
  intro h2
  obtain ⟨h_l_nonneg, h_l_le_len⟩ := h2
  intro h3
  obtain ⟨h_l_le_r, h_r_le_len⟩ := h3
  intro _h_self_slice_v
  intro h_len_v_nonneg
  intro h_l_ge_0
  intro h_r_ge_0
  intro _h_self_slice_s
  intro h_len_s_nonneg
  constructor
  · -- Case: ¬(l₀ + len(s₀) < r₀), need to show s₀ = slice v₀ l₀ r₀
    intro h_not_lt
    -- From h_sum_le_r and h_not_lt, we have l₀ + len(s₀) = r₀
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h_not_lt
    have h_eq : l₀ + s₀.len = r₀ := by omega
    rw [← h_eq]
    exact h_s_eq_slice
  · -- Case: l₀ + len(s₀) < r₀
    intro h_lt
    constructor
    · -- l₀ < len(v₀)
      omega
    constructor
    · -- l₀ ≤ l₀ + len(s₀) ∧ l₀ + len(s₀) < len(v₀)
      constructor <;> omega
    · -- Given the slice push extend property
      intro h_slice_push_extend
      constructor
      · -- 0 ≤ l₀ + len(s₀) ∧ l₀ + len(s₀) < len(v₀)
        constructor <;> omega
      constructor
      · -- ∀ a'₀, k0 ... is trivially true
        intro _
        trivial
      · -- k0 ... → rest
        intro _
        intro _h_self_slice_s'
        intro _h_len_s'_nonneg
        constructor
        · -- l₀ + (s₀.len + 1) ≤ r₀
          omega
        · -- The extended slice equals slice v₀ l₀ (l₀ + (s₀.len + 1))
          -- Use extensionality
          simp only [svec_svec_slice, map_slice] at h_s_eq_slice h_slice_push_extend ⊢
          -- From h_s_eq_slice we know s₀.elems and s₀.len
          have h_s_len : s₀.len = (if l₀ + s₀.len - l₀ < 0 then 0 else l₀ + s₀.len - l₀) := by
            have := congrArg SvecSVec.len h_s_eq_slice
            simp only at this
            exact this
          have h_s_len_simp : s₀.len = s₀.len := rfl
          -- The key: h_slice_push_extend says the extended slice equals svec_svec_slice v₀ l₀ (l₀ + s₀.len + 1)
          -- We need to show our goal equals slice v₀ l₀ (l₀ + (s₀.len + 1))
          -- Note: l₀ + s₀.len + 1 = l₀ + (s₀.len + 1)
          have h_idx_eq : l₀ + s₀.len + 1 = l₀ + (s₀.len + 1) := by omega
          rw [← h_idx_eq]
          -- Now use h_slice_push_extend after showing the LHS matches
          ext
          · -- elems equality
            have h1 := congrArg SvecSVec.elems h_s_eq_slice
            have h2 := congrArg SvecSVec.elems h_slice_push_extend
            simp only at h1 h2
            rw [h1]
            have h_idx_eq2 : l₀ + s₀.len - l₀ = s₀.len := by omega
            simp only [h_idx_eq2] at h2 ⊢
            exact h2
          · -- len equality
            have h1 := congrArg SvecSVec.len h_slice_push_extend
            simp only at h1
            have h_idx_eq2 : l₀ + s₀.len - l₀ + 1 = s₀.len + 1 := by omega
            simp only [h_idx_eq2] at h1 ⊢
            exact h1

end F
