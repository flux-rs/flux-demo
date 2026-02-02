import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaAppendPushExtend

namespace F

def LemmaAppendPushExtend_proof : LemmaAppendPushExtend := by
  unfold LemmaAppendPushExtend
  intro append₀ l₀ r₀ ext_idx₀
  intro h1
  obtain ⟨h_append_eq, h_l_len_nonneg⟩ := h1
  intro h2
  obtain ⟨h_ext_nonneg, h_ext_le_r_len⟩ := h2
  intro _h_self_slice_append
  intro h_append_len_nonneg
  intro _h_self_slice_r
  intro h_r_len_nonneg
  intro h_ext_ge_0
  -- Goal: mkSvecSVec₀ (store append₀.elems append₀.len (select r₀.elems ext_idx₀)) (append₀.len + 1)
  --     = svec_svec_append l₀ (svec_svec_slice r₀ 0 (ext_idx₀ + 1))
  simp only [svec_svec_append, map_append, svec_svec_slice, map_slice, SmtMap_select]
  -- Use extensionality to prove equality of SvecSVec structures
  ext
  · -- Prove elems are equal
    funext x
    unfold SmtMap_store
    simp only [beq_iff_eq]
    -- First, establish append₀.len = l₀.len + ext_idx₀
    have h_append_len : append₀.len = l₀.len + ext_idx₀ := by
      rw [h_append_eq]
      simp only [svec_svec_append, map_append, svec_svec_slice, map_slice]
      have h_slice_len_nonneg : ¬(ext_idx₀ - 0 < 0) := by omega
      simp only [h_slice_len_nonneg, ↓reduceIte]
      omega
    -- Simplify the slice length in RHS
    have h_slice_new_len : ¬(ext_idx₀ + 1 - 0 < 0) := by omega
    simp only [h_slice_new_len, ↓reduceIte]
    by_cases hx : x = append₀.len
    · -- x = append₀.len: LHS is r₀.elems ext_idx₀
      simp only [hx, ↓reduceIte]
      rw [h_append_len]
      have h1 : ¬(l₀.len + ext_idx₀ < 0) := by omega
      have h2 : ¬(l₀.len + ext_idx₀ < l₀.len) := by omega
      have h3 : l₀.len + ext_idx₀ < l₀.len + (ext_idx₀ + 1 - 0) := by omega
      simp only [h1, h2, h3, ↓reduceIte]
      have h4 : 0 ≤ l₀.len + ext_idx₀ - l₀.len := by omega
      have h5 : l₀.len + ext_idx₀ - l₀.len < ext_idx₀ + 1 - 0 := by omega
      simp only [h4, h5, and_self, ↓reduceIte]
      congr 1
      omega
    · -- x ≠ append₀.len
      simp only [hx, ↓reduceIte]
      -- We need to show: append₀.elems x = (append l₀ (slice r₀ 0 (ext_idx₀+1))).elems x
      rw [h_append_eq]
      simp only [svec_svec_append, map_append, svec_svec_slice, map_slice]
      have h_slice_len_nonneg : ¬(ext_idx₀ - 0 < 0) := by omega
      simp only [h_slice_len_nonneg, ↓reduceIte]
      by_cases hx_neg : x < 0
      · simp only [hx_neg, ↓reduceIte]
      · simp only [hx_neg, ↓reduceIte]
        by_cases hx_l : x < l₀.len
        · simp only [hx_l, ↓reduceIte]
        · simp only [hx_l, ↓reduceIte]
          by_cases hx_old : x < l₀.len + (ext_idx₀ - 0)
          · -- x is in the old slice range
            have hx_new : x < l₀.len + (ext_idx₀ + 1 - 0) := by omega
            simp only [hx_old, hx_new, ↓reduceIte]
            have h_in_old : 0 ≤ x - l₀.len ∧ x - l₀.len < ext_idx₀ - 0 := by omega
            have h_in_new : 0 ≤ x - l₀.len ∧ x - l₀.len < ext_idx₀ + 1 - 0 := by omega
            simp only [h_in_old, h_in_new]
          · -- x is outside old slice range
            simp only [hx_old, ↓reduceIte]
            by_cases hx_new : x < l₀.len + (ext_idx₀ + 1 - 0)
            · -- x is in new range but not old: x = l₀.len + ext_idx₀ = append₀.len
              -- But we have hx : x ≠ append₀.len, contradiction
              exfalso
              rw [h_append_len] at hx
              omega
            · simp only [hx_new, ↓reduceIte]
  · -- Prove lengths are equal
    simp only
    have h_append_len : append₀.len = l₀.len + ext_idx₀ := by
      rw [h_append_eq]
      simp only [svec_svec_append, map_append, svec_svec_slice, map_slice]
      have h : ¬(ext_idx₀ - 0 < 0) := by omega
      simp only [h, ↓reduceIte]
      omega
    rw [h_append_len]
    have h : ¬(ext_idx₀ + 1 - 0 < 0) := by omega
    simp only [h, ↓reduceIte]
    omega

end F
