import LeanProofs.Lib
import LeanProofs.InsertSorted
import LeanProofs.SharedTheorems

def k0 : Int → SmtMap Int Int → Int → Int → Prop := fun idx v_elems v_len elem_to_insert => 0 ≤ idx ∧ idx <= v_len ∧ (idx = 0 ∨ elem_to_insert > v_elems (idx - 1))
def k1 : SmtMap Int Int → Int → Int → Int → Prop := fun elems len e idx => len = idx ∨ e ≤ elems idx
def k2 : Int → SmtMap Int Int → Int → Int → Int → Prop := fun _ _ _ _ _ => True

theorem insert_sorted_proof : insert_sorted := by
  unfold insert_sorted
  exists k0 ; exists k1 ; exists k2
  intros v e _ v_sorted _ h_v _ v_len_lb
  and_intros
  · intros
    simp [k0, *] at *
  · intros idx v_elems v_elems_eq v_len v_len_eq _ k0_holds
    unfold k0 at *;
    and_intros
    · intros ; and_intros
      · intros _ loop_done v_elems v_elems_eq v_len v_len_eq
        simp [k1, *] at *
        left ; omega
      · intros _ idx_lt_v_len
        and_intros
        · omega
        · intros ; trivial
        · intros v_at_idx v_at_idx_eq v_elems v_elems_eq v_len v_len_eq _ k2_holds
          and_intros
          · intros
            simp [k1, SmtMap_select, *] at *
            omega
          · intros _ e_gt_v_at_idx next_idx next_idx_eq v_elems v_elems_eq v_len v_len_eq
            simp at *
            and_intros
            · omega
            · omega
            · right ; simp_all ; assumption
      · intros v_elems v_elems_eq v_len v_len_eq _ k1_holds _
        and_intros
        · intros _ idx_ne_v_len
          and_intros
          · omega
          · omega
          · intros _ h _ h'
            apply append_sorted
            · have h_len : (svec_svec_slice v 0 idx).fld0_1 = idx := by simp [svec_slice_eq, map_slice] ; grind
              conv => arg 1 ; arg 1 ; arg 2 ; rw [←h_len]
              conv => arg 1; arg 2 ; rw [←h_len]
              apply push_sorted (svec_svec_slice v 0 idx)
              · apply slice_sorted
                · omega
                · unfold k0 at * ; omega
                · assumption
              · by_cases h_idx_eq0 : idx = 0 <;> rw [h_len]
                · left ; assumption
                · right
                  simp [svec_slice_eq, map_slice] at *
                  grind
            · apply slice_sorted
              · omega
              · omega
              · assumption
            · simp ; right ; right
              and_intros
              · omega
              · simp [svec_slice_eq, map_slice] at *; omega
              · simp [SmtMap_store, svec_slice_eq, map_slice] at *
                have tmp : idx < v.fld0_1 := by omega
                simp [tmp]
                simp [k1, *] at *
                omega
        · intros _ idx_ne_v_len _ h_push _ _
          apply push_sorted
          · assumption
          · have tmp : v.fld0_1 = idx := by omega
            by_cases h_idx_eq0 : v.fld0_1 = 0
            · left ; assumption
            · right ; simp [*] at * ; omega
