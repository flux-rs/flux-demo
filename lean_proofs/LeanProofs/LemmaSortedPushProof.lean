import LeanProofs.Lib
import LeanProofs.LemmaSortedPush
import LeanProofs.SharedTheorems

def lemma_sorted_push_proof : lemma_sorted_push := by
  unfold lemma_sorted_push
  intros v e _ h _ h_slice _ len_lbound
  have ⟨v_sorted, e_gt_last⟩ := h ; clear h
  rw [svec_is_sorted_eq] at *
  intros i j i_bounds j_bounds
  simp [SmtMap_store] at *
  by_cases h : i = v.fld0_1
  · have h' : j = v.fld0_1 := by omega
    simp [h, h']
  · simp [h]
    by_cases h' : j = v.fld0_1 <;> simp [h']
    · simp [SmtMap_select] at e_gt_last
      have at_i_lt_last : v.fld0_0 i ≤ v.fld0_0 (v.fld0_1 -1) := by
        apply_assumption <;> omega
      omega
    · apply_assumption <;> omega
