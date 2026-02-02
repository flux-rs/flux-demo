import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Append

namespace F

def Append_proof : Append := by
  unfold Append
  intro b₀ e₀
  intro _h_self_slice_b
  intro h_b_len_nonneg
  intro _h_self_slice_e
  intro h_e_len_nonneg
  intro _h_b_eq_append_empty
  intro h_slice_e_eq
  constructor
  · -- 0 ≤ e₀.len
    omega
  · -- Given the self-slice property, prove append b₀ (slice e₀ 0 e₀.len) = append b₀ e₀
    intro _h_self_slice_result
    intro _h_result_len_nonneg
    -- h_slice_e_eq : slice e₀ 0 e₀.len = e₀
    -- Goal: append b₀ (slice e₀ 0 e₀.len) = append b₀ e₀
    rw [h_slice_e_eq]

end F
