import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Insert

namespace F

def Insert_proof : Insert := by
  unfold Insert
  intro v₀ pos₀ e₀
  intro h_bounds
  obtain ⟨h_pos_nonneg, h_pos_le_len⟩ := h_bounds
  intro _h_self_slice_v
  intro h_v_len_nonneg
  intro h_pos_ge_0
  constructor
  · -- v₀.len ≤ v₀.len
    omega
  · intro _h_self_slice_tail
    intro h_tail_len_nonneg
    constructor
    · -- 0 ≤ v₀.len
      omega
    · intro h_head_slice_len_eq
      -- h_head_slice_len_eq : (slice v₀ 0 pos₀).len = pos₀ - 0
      constructor
      · -- 0 ≤ v₀.len
        omega
      · intro _h_self_slice_head
        intro h_head_len_nonneg
        intro _h_self_slice_extended
        intro h_extended_len_nonneg
        intro _h_self_slice_result
        intro h_result_len_nonneg
        -- Goal: the two appends are equal
        -- LHS uses (slice v₀ 0 pos₀).len, RHS uses pos₀
        -- Since h_head_slice_len_eq tells us (slice v₀ 0 pos₀).len = pos₀ - 0 = pos₀
        -- The two sides should be definitionally equal after this substitution
        have h_len_eq : (svec_svec_slice v₀ 0 pos₀).len = pos₀ := by
          simp only [svec_svec_slice, map_slice]
          have h : ¬(pos₀ - 0 < 0) := by omega
          simp only [h, ↓reduceIte]
          omega
        simp only [h_len_eq]

end F
