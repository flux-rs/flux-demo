import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSliceFromToEqEmpty

namespace F

def LemmaSliceFromToEqEmpty_proof : LemmaSliceFromToEqEmpty := by
  unfold LemmaSliceFromToEqEmpty
  intro v₀ idx₀
  intro h_idx_le_len
  intro _h_self_slice
  intro h_len_nonneg
  intro h_idx_nonneg
  -- Goal: svec_svec_slice v₀ idx₀ idx₀ = mkSvecSVec₀ svec_empty_seq 0
  simp only [svec_svec_slice, map_slice]
  ext
  · -- Prove elems are equal
    funext x
    -- slice elems: if 0 ≤ x ∧ x < idx₀ - idx₀ then v₀.elems (x + idx₀) else default
    -- Since idx₀ - idx₀ = 0, condition 0 ≤ x ∧ x < 0 is always false
    have h : ¬(0 ≤ x ∧ x < idx₀ - idx₀) := by omega
    simp only [h, ↓reduceIte]
    -- Now need to show: default = svec_empty_seq x
    unfold svec_empty_seq
    rfl
  · -- Prove lengths are equal
    -- slice len: if idx₀ - idx₀ < 0 then 0 else idx₀ - idx₀ = 0
    have h : ¬(idx₀ - idx₀ < 0) := by omega
    simp only [h, ↓reduceIte]
    omega

end F
