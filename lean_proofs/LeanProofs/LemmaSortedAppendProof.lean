import LeanProofs.Lib
import LeanProofs.LemmaSortedAppend
import LeanProofs.SharedTheorems

def lemma_sorted_append_proof : lemma_sorted_append := by
  unfold lemma_sorted_append
  intros v1 v2 _ h _ h_v1 _ v1_len_nonneg _ h_v2 _ v2_len_nonneg
  have ⟨v1_sorted, v2_sorted, v1_nonnempty, v2_nonnempty, v1_last_le_v2_first⟩ := h ; clear h
  simp [svec_is_sorted_eq, svec_append_eq, svec_slice_eq, map_append, map_slice, SmtMap_select] at *
  intros i j i_lb i_ub i_le_j j_ub
  have tmp1 : ¬ i < 0 := by omega
  have tmp2 : ¬ j < 0 := by omega
  simp [tmp1, tmp2, i_ub, j_ub]
  by_cases h : j < v1.fld0_1
  · have tmp3 : i < v1.fld0_1 := by omega
    simp [h, tmp3]
    apply_assumption <;> omega
  by_cases h' : i < v1.fld0_1
  · simp [h, h']
    apply Int.le_trans
    · apply v1_sorted i (v1.fld0_1 - 1) <;> omega
    · apply Int.le_trans
      · apply v1_last_le_v2_first
      · apply_assumption <;> omega
  · simp [h, h']
    apply_assumption <;> omega
