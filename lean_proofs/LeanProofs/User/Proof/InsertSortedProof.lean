import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.InsertSorted

namespace F

def InsertSorted_proof : InsertSorted := by
  unfold InsertSorted
  -- Use the predefined kvar solutions
  refine ⟨InsertSortedKVarSolutions.k0,
          InsertSortedKVarSolutions.k1,
          InsertSortedKVarSolutions.k2, ?_⟩
  intro s₀ e₀
  intro h_sorted
  intro h_slice_eq
  intro h_len_nonneg
  unfold InsertSortedKVarSolutions.k0
  constructor
  · -- k0 0 ... : (0 ≥ 0) ∧ (0 ≤ 0) ∧ (0 ≤ s₀.len)
    omega
  · intro i₀
    intro h_k0
    obtain ⟨h_i_ge_0, h_i_ge_0', h_i_le_len⟩ := h_k0
    constructor
    · -- ¬(i₀ < len) → k1 ...
      intro h_not_lt
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h_not_lt
      unfold InsertSortedKVarSolutions.k1
      right
      refine ⟨h_sorted, h_not_lt, rfl, rfl, rfl, rfl, h_slice_eq, ?_, h_len_nonneg, ?_, h_i_le_len⟩
      · omega
      · omega
    constructor
    · -- i₀ < len → ...
      intro h_lt
      constructor
      · omega
      constructor
      · -- ∀ a'₁, k2 ...
        intro a'₁
        unfold InsertSortedKVarSolutions.k2
        refine ⟨h_sorted, rfl, rfl, rfl, rfl, h_slice_eq, ?_, h_len_nonneg, h_lt, ?_, h_i_le_len⟩
        · omega
        · omega
      · -- k2 ... → ...
        intro h_k2
        constructor
        · -- ¬(e₀ > s₀[i₀]) → k1 ...
          intro h_not_gt
          simp only [Bool.not_eq_true', decide_eq_false_iff_not, gt_iff_lt] at h_not_gt
          unfold InsertSortedKVarSolutions.k1
          left
          refine ⟨h_sorted, h_not_gt, rfl, rfl, rfl, rfl, h_slice_eq, ?_, h_len_nonneg, h_lt, ?_, h_i_le_len⟩
          · omega
          · omega
        · -- e₀ > s₀[i₀] → k0 (i₀ + 1) ...
          intro _h_gt
          omega
    · -- k1 ... → ...
      intro h_k1
      unfold InsertSortedKVarSolutions.k1 at h_k1
      constructor
      · -- i₀ ≠ len → bounds ∧ sorted
        intro h_neq
        simp only [ne_eq] at h_neq
        constructor
        · omega
        · intro _h_slice_eq'
          intro _h_result_len_nonneg
          -- Need to prove sorted after insertion at position i₀
          -- This requires semantic reasoning about insertion maintaining sortedness
          sorry
      · -- ¬(i₀ ≠ len) → sorted
        intro h_eq_len
        simp only [Bool.not_eq_true', ne_eq, decide_eq_false_iff_not, Decidable.not_not] at h_eq_len
        intro _h_slice_eq'
        intro _h_result_len_nonneg
        -- Need to prove sorted after appending at end
        -- This requires semantic reasoning about appending to sorted list
        sorry

end F
