import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Slice

namespace F

def Slice_proof : Slice := by
  unfold Slice
  intro v₀ l₀ r₀
  intro h1
  obtain ⟨h_l_nonneg, h_l_le_len⟩ := h1
  intro h2
  obtain ⟨h_l_le_r, h_r_le_len⟩ := h2
  intro _h_self_slice_v
  intro h_len_v_nonneg
  intro h_l_ge_0
  intro h_r_ge_0
  intro _h_empty_slice
  intro h_slice_l_l_eq_empty
  constructor
  · -- (l₀ + 0) ≤ r₀
    omega
  · -- empty = slice v₀ l₀ (l₀ + 0)
    -- We have h_slice_l_l_eq_empty : slice v₀ l₀ l₀ = empty
    -- Need: empty = slice v₀ l₀ (l₀ + 0)
    -- Since l₀ + 0 = l₀, this is just the symmetric version
    have h_eq : l₀ + 0 = l₀ := by omega
    rw [h_eq]
    exact h_slice_l_l_eq_empty.symm

end F
