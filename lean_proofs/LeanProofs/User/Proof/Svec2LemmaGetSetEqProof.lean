import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Svec2LemmaGetSetEq

namespace F

def Svec2LemmaGetSetEq_proof : Svec2LemmaGetSetEq := by
  unfold Svec2LemmaGetSetEq
  intro elems₀ len₀ i₀ e₀
  intro h1
  obtain ⟨h_i_nonneg, h_i_lt_len⟩ := h1
  intro h_len_eq
  intro h_len_nonneg
  intro h_i_ge_0
  -- Goal: svec2_vseq_get (svec2_vseq_set elems₀ i₀ e₀) i₀ = e₀
  unfold svec2_vseq_get svec2_vseq_set
  -- Since List.set doesn't change length:
  simp only [List.length_set]
  unfold svec2_vseq_len at h_len_eq
  have h_len_nat : (elems₀.length : Int) = len₀ := h_len_eq
  -- Show the index is nonnegative and valid
  have h_pos : (elems₀.length : Int) - i₀ - 1 ≥ 0 := by omega
  have h_idx_valid : (↑elems₀.length - i₀ - 1).natAbs < elems₀.length := by
    have h_eq : (↑elems₀.length - i₀ - 1).natAbs = (↑elems₀.length - i₀ - 1).toNat := by
      exact Int.toNat_of_nonneg h_pos ▸ rfl
    rw [h_eq]
    have h2 : (↑elems₀.length - i₀ - 1) < elems₀.length := by omega
    have h3 : 0 ≤ (↑elems₀.length - i₀ - 1) := h_pos
    -- toNat preserves order for non-negative integers
    rw [Int.toNat_lt h3]
    exact h2
  -- Use the fact that getD (set l n e) n d = e when n < l.length
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_set_self h_idx_valid]
  rfl

end F
