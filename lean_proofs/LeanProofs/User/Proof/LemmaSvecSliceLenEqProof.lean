import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSvecSliceLenEq

namespace F

def LemmaSvecSliceLenEq_proof : LemmaSvecSliceLenEq := by
  unfold LemmaSvecSliceLenEq
  intro v₀ l₀ r₀
  intro h_l_le_len
  intro h_bounds
  obtain ⟨h_l_le_r, h_r_le_len⟩ := h_bounds
  intro _h_self_slice
  intro h_len_nonneg
  intro h_l_nonneg
  intro h_r_nonneg
  -- Goal: (svec_svec_slice v₀ l₀ r₀).len = r₀ - l₀
  simp only [svec_svec_slice, map_slice]
  -- The length is: if r₀ - l₀ < 0 then 0 else r₀ - l₀
  -- Since l₀ ≤ r₀, we have r₀ - l₀ ≥ 0
  have h : ¬(r₀ - l₀ < 0) := by omega
  simp only [h, ↓reduceIte]

end F
