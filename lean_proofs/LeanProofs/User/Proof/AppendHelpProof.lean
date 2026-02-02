import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.AppendHelp

namespace F

def AppendHelp_proof : AppendHelp := by
  unfold AppendHelp
  -- Choose k0 to be trivially true
  refine ⟨fun _ _ _ _ _ _ _ _ => True, ?_⟩
  intro b₀ e₀ ext_idx₀ l₀
  intro h1
  obtain ⟨h_b_eq, h_l_len_nonneg⟩ := h1
  intro h2
  obtain ⟨h_ext_nonneg, h_ext_le_e_len⟩ := h2
  intro _h_self_slice_b
  intro h_b_len_nonneg
  intro _h_self_slice_e
  intro h_e_len_nonneg
  intro h_ext_ge_0
  constructor
  · -- Case: ¬(ext_idx₀ < e₀.len), need to show b₀ = append l₀ (slice e₀ 0 e₀.len)
    intro h_not_lt
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h_not_lt
    -- From h_ext_le_e_len and h_not_lt, we have ext_idx₀ = e₀.len
    have h_eq : ext_idx₀ = e₀.len := by omega
    rw [← h_eq]
    exact h_b_eq
  · -- Case: ext_idx₀ < e₀.len
    intro h_lt
    intro _h_append_extend
    constructor
    · -- ∀ a'₀, k0 ... is trivially true
      intro _
      trivial
    · -- k0 ... → rest
      intro _
      intro _h_self_slice_b'
      intro _h_b'_len_nonneg
      -- Need to show: 0 ≤ ext_idx₀ + 1 ∧ ext_idx₀ + 1 ≤ e₀.len
      constructor <;> omega

end F
