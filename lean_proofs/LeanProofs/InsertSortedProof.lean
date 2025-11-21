import LeanProofs.Lib
import LeanProofs.InsertSorted
import LeanProofs.SharedTheorems

def k0 : Int → SmtMap Int Int → Int → Int → Prop := fun idx v_elems v_len elem_to_insert => 0 ≤ idx ∧ idx <= v_len ∧ (idx = 0 ∨ elem_to_insert > v_elems (idx - 1))
def k1 : SmtMap Int Int → Int → Int → Int → Prop := fun elems len e idx => len = idx ∨ e ≤ elems idx
def k2 : Int → SmtMap Int Int → Int → Int → Int → Prop := fun _ _ _ _ _ => True

theorem append_sorted (v1 v2 : Adt0 Int) (h1 : svec_is_sorted v1) (h2 : svec_is_sorted v2) (h3 : v1.fld0_1 = 0 ∨ v2.fld0_1 = 0 ∨ ( v1.fld0_1 > 0 ∧ v2.fld0_1 > 0 ∧ (v1.fld0_0 (v1.fld0_1 - 1) ≤ v2.fld0_0 0))) : svec_is_sorted (svec_svec_append v1 v2) := by
  simp [svec_is_sorted_eq, svec_append_eq, map_append]
  intros i j i_lb i_ub j_lb j_ub
  have tmp1 : ¬ i < 0 := by omega
  have tmp2 : ¬ j < 0 := by omega
  simp [tmp1, tmp2, i_ub, j_ub]
  cases h3 with
  | inl v1_len0 =>
    simp [v1_len0, tmp1, tmp2, svec_is_sorted_eq] at *
    grind
  | inr h_rest =>
    cases h_rest with
    | inl v2_len0 =>
      by_cases h : j < v1.fld0_1
      · have tmp3 : i < v1.fld0_1 := by omega
        simp [h, tmp3]
        apply_assumption <;> omega
      exfalso ; omega
    | inr nonempty_and_inc =>
      by_cases h : j < v1.fld0_1
      · have tmp3 : i < v1.fld0_1 := by omega
        simp [h, tmp3]
        apply_assumption <;> omega
      by_cases h' : i < v1.fld0_1
      · simp [h, h']
        apply Int.le_trans
        · apply h1 i (v1.fld0_1 - 1) <;> omega
        · apply Int.le_trans
          · apply nonempty_and_inc.right.right
          · apply_assumption <;> omega
      · simp [h, h']
        apply_assumption <;> omega

theorem push_sorted (v1 : Adt0 Int) (e : Int) (h1 : svec_is_sorted v1) (h2 : v1.fld0_1 = 0 ∨ v1.fld0_0 (v1.fld0_1 - 1) ≤ e) : svec_is_sorted (Adt0.mkadt0_0 (SmtMap_store v1.fld0_0 v1.fld0_1 e) (v1.fld0_1 + 1)) := by
  simp [svec_is_sorted_eq, SmtMap_store] at *
  cases h2 with
  | inl v1_len0 =>
    intros
    simp [v1_len0] at * ; omega
  | inr h_le =>
    intros i j i_lb i_ub j_lb j_ub
    by_cases h : i = v1.fld0_1
    · have h' : j = v1.fld0_1 := by omega
      simp [h, h']
    · simp [h]
      by_cases h' : j = v1.fld0_1 <;> simp [h']
      · have at_i_lt_last : v1.fld0_0 i ≤ v1.fld0_0 (v1.fld0_1 -1) := by
          apply_assumption <;> omega
        omega
      · apply_assumption <;> omega

theorem slice_sorted (v1 : Adt0 Int) (l r : Int) (h1 : l ≥ 0 ∧ l ≤ v1.fld0_1) (h2 : r ≥ l ∧ r ≤ v1.fld0_1) (h3 : svec_is_sorted v1) : svec_is_sorted (svec_svec_slice v1 l r) := by
  simp [svec_is_sorted_eq, svec_slice_eq, map_slice] at *
  intros i j i_lb i_ub j_lb j_ub
  have rl : ¬ r - l < 0 := by omega
  have j_lb' : 0 ≤ j := by omega
  simp [rl] at *
  simp [i_lb, i_ub, j_lb', j_ub]
  apply_assumption <;> omega

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
