import LeanProofs.Lib
import LeanProofs.InPlaceInsertionSortInsertSorted
import LeanProofs.SharedTheorems

theorem slice_slice_helper (v : Adt0 Int) (r l' r' : Int) (h1 : 0 ≤ l') (h2 : r' ≤ r ∧ r ≤ v.fld0_1) : svec_svec_slice v l' r' = svec_svec_slice (svec_svec_slice v 0 r) l' r' := by
  have tmp1 : l' = l' - 0 := by omega
  have tmp2 : r' = r' - 0 := by omega
  conv => rhs ; rw [tmp1, tmp2]
  apply slice_slice
  · omega
  · omega

theorem helper {f1 f2 : Int -> Int} (x : Int) (h : f1 = f2) : f1 x = f2 x :=
  by grind

-- loop invariant
def k0 : SmtMap Int Int → Int → Int → SmtMap Int Int → Int → Int → Int → Prop :=
  fun elems len idx v_elems v_len sorted_bound elem_to_insert =>
    idx ≥ 0 ∧ idx ≤ sorted_bound ∧ sorted_bound ≥ 1 ∧ sorted_bound < len ∧ len = v_len ∧
    svec_is_sorted (svec_svec_slice (Adt0.mkadt0_0 elems len) 0 sorted_bound) ∧
    (
      (
        idx = 0 ∧
        elems = v_elems ∧
        len = v_len ∧
        elem_to_insert = v_elems sorted_bound ∧
        elems sorted_bound = v_elems sorted_bound
      ) ∨
      (
        let v := Adt0.mkadt0_0 v_elems v_len
        idx ≠ 0 ∧
        svec_svec_slice (Adt0.mkadt0_0 elems len) 0 (sorted_bound + 1) = svec_svec_append (svec_svec_slice v 0 (sorted_bound - idx + 1)) (svec_svec_slice v (sorted_bound - idx) (sorted_bound)) ∧
        elem_to_insert < elems (sorted_bound - idx)
      )
    )

def k1 : Int → Int → SmtMap Int Int → Int → Int → Int → Prop :=
  fun _ _ _ _ _ _ => True
def k2 : Int → SmtMap Int Int → Int → Int → Int → Prop :=
  fun _ _ _ _ _ => True
def k3 : Int → SmtMap Int Int → Int → Int → SmtMap Int Int → Int → Int → Int → Prop :=
  fun _ _ _ _ _ _ _ _ => True
def k4 : SmtMap Int Int → Int → Int → Int → SmtMap Int Int → Int → Int → Prop :=
  fun _v1_elems _v1_len sorted_bound elem ps_elems _ps_len i =>
    i = sorted_bound ∨ elem ≥ ps_elems (sorted_bound - i - 1)
def k5 : Int → SmtMap Int Int → Int → Int → Int → SmtMap Int Int → Int → Int → Prop :=
  fun _ _ _ _ _ _ _ _ => True
def k6 : Int → SmtMap Int Int → Int → Int → Int → SmtMap Int Int → Int → Int → Prop :=
  fun _ _ _ _ _ _ _ _ => True
def k7 : Int → SmtMap Int Int → Int → Int → Int → SmtMap Int Int → Int → Int → Prop :=
  fun _ _ _ _ _ _ _ _ => True

def in_place_insertion_sort_insert_sorted_proof : in_place_insertion_sort_insert_sorted := by
  unfold in_place_insertion_sort_insert_sorted
  exists k0
  exists k1
  exists k2
  exists k3
  exists k4
  exists k5
  exists k6
  exists k7
  intros v1 sorted_bound elem _ sorted_up_to _ sorted_bound_ub _ elem_eq _ h_v1 _ v1_len_lb _ sorted_bound_lb
  unfold k0 k4 at *
  and_intros
  · intros v1_elems v1_elems_eq v1_len v1_len_eq idx idx_eq v1_elems v1_elems_eq v1_len v1_len_eq
    unfold k1 k2
    and_intros <;> simp [SmtMap_select, *]
  · intros -- a5 v1_elems v1_elems_eq v1_len v1_len_eq a8 a8_eq v1_elems v1_elems_eq v1_len v1_len_eq
    trivial
  · intros ps i ps_elems ps_elems_eq ps_len ps_len_eq v1_elems v1_elems_eq v1_len v1_len_eq _ ks_hold
    and_intros
    · intros ; omega
    · intros _ i_lt_sorted_bound
      and_intros
      · omega
      · omega
      · omega
      · omega
      · intros -- a21 ps_elems ps_elems_eq ps_len ps_len_eq v1_elems v1_elems_eq v1_len v1_len_eq _ k3_holds v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq
        -- k5 holds while i < sorted_bound & k3 holds
        trivial
      · intros ps_at_i ps_at_i_eq v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq _ k5_holds
        and_intros
        · intros _ elem_ge_ps_at_i v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq
          right ;
          simp [SmtMap_select] at elem_ge_ps_at_i
          simp [ps_elems_eq]
          omega
        · intros _ elem_lt_ps_at_i
          and_intros
          · omega
          · omega
          · omega
          · omega
          · unfold k0 at ks_hold ; omega
          · intros ; trivial
          · intros ps_at_i ps_at_i_eq v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq _ k6_holds
            and_intros
            · omega
            · unfold k0 at ks_hold ; omega
            · intros ; trivial
            · intros ; trivial
            · intros _ h_ps_dup _ ps_len_lb
              and_intros
              · intros ps_dup ps_dup_eq ps_len ps_len_eq next_i next_i_eq v1_elems v1_elems_eq v1_len v1_len_eq
                and_intros
                · unfold k0 at ks_hold ; omega
                · omega
                · unfold k0 at ks_hold ; omega
                · unfold k0 at ks_hold ; omega
                · unfold k0 at ks_hold ; omega
                · unfold k0 at ks_hold
                  simp [ps_dup_eq]
                  apply sorted_set_slice
                  · simp [*] at *
                    have tmp : svec_is_sorted (svec_svec_slice { fld0_0 := ps.fld0_0, fld0_1 := ps.fld0_1 } 0 sorted_bound) := by exact ks_hold.left.right.right.right.right.left
                    assumption
                  · simp [SmtMap_select, *] at *
                    by_cases i_eq0 : i = 0
                    · and_intros
                      · grind
                      · omega
                    · and_intros
                      · grind
                      · left
                        and_intros
                        · omega
                        · have tmp1 : ps.fld0_0 (sorted_bound - i - 1) = (svec_svec_slice ps 0 sorted_bound).fld0_0 (sorted_bound - i -1) := by
                            simp [svec_slice_eq, map_slice]
                            intros ; exfalso ; omega
                          have tmp2 : ps.fld0_0 (sorted_bound - i) = (svec_svec_slice ps 0 sorted_bound).fld0_0 (sorted_bound - i) := by
                            simp [svec_slice_eq, map_slice]
                            intros ; exfalso ; omega
                          rw [tmp1, tmp2]
                          apply ks_hold.left.right.right.right.right.left
                          and_intros
                          · omega
                          · simp [svec_slice_eq, map_slice] ; omega
                          · omega
                          · simp [svec_slice_eq, map_slice] ; omega
                  · omega
                · right
                  simp ; and_intros
                  · simp [k0, next_i_eq] at * ; omega
                  · simp [ps_dup_eq]
                    apply eq_append
                    · simp [svec_slice_eq, map_slice]
                      have tmp : ¬ sorted_bound - next_i + 1 < 0 := by omega
                      simp [tmp]
                      rfl
                    · simp [svec_slice_eq, map_slice]
                      have tmp : ¬  (sorted_bound - (sorted_bound - next_i) < 0) := by
                        simp [k0, next_i_eq] at *
                        omega
                      simp [tmp]
                      rfl
                    · omega
                    · simp [next_i_eq, k0] at * ; omega
                    · intros x x_lt_0
                      simp [svec_slice_eq, map_slice] ; grind
                    · intros x x_lt_0
                      simp [svec_slice_eq, map_slice] ; grind
                    · rw [←slice_slice_helper]
                      · simp [svec_slice_eq, map_slice, SmtMap_store, SmtMap_select, k0, *] at *
                        funext x
                        by_cases x_in_bounds : 0 ≤ x ∧ x < sorted_bound - (i + 1) + 1
                        · simp [x_in_bounds]
                          have tmp : ¬ x = sorted_bound - i := by omega
                          simp [tmp]
                          by_cases i_eq_0 : i = 0
                          · grind
                          · simp [*] at *
                            have h := ks_hold.left.right.right.right.right.right.left
                            simp [svec_append_eq, map_append] at h
                            have ⟨h_elems, h_lens⟩ := h
                            have tmp := helper x h_elems
                            grind
                        · omega
                      · omega
                      · simp [next_i_eq, k0] at * ; omega
                    · rw [←slice_slice_helper]
                      · simp [svec_slice_eq, map_slice, SmtMap_store, SmtMap_select, k0, *] at *
                        and_intros
                        · funext x
                          by_cases x_in_bounds : 0 ≤ x ∧ x < sorted_bound - (sorted_bound - (i + 1))
                          · have tmp1 : x < sorted_bound - (i + 1) + 1 + (sorted_bound - (sorted_bound - (i + 1))) - (sorted_bound - (i + 1) + 1) := by omega
                            simp [x_in_bounds, tmp1]
                            by_cases i_eq_0 : i = 0
                            · grind
                            · by_cases x_eq_0 : x = 0
                              · have tmp : (sorted_bound - (i + 1) + 1) = sorted_bound - i := by omega
                                simp [x_eq_0, tmp]
                                simp [*] at *
                                have h := ks_hold.left.right.right.right.right.right.left
                                simp [svec_append_eq, map_append] at h
                                have ⟨h_elems, h_lens⟩ := h
                                have tmp := helper (sorted_bound - (i + 1)) h_elems
                                grind
                              · have tmp : ¬ x + (sorted_bound - (i + 1) + 1) = sorted_bound - i := by omega
                                simp [tmp]
                                simp [*] at *
                                have h := ks_hold.left.right.right.right.right.right.left
                                simp [svec_append_eq, map_append] at h
                                have ⟨h_elems, h_lens⟩ := h
                                have tmp := helper ((x + (sorted_bound - (i + 1) + 1))) h_elems
                                grind
                          · omega
                        · omega
                      · simp [next_i_eq, k0] at * ; omega
                      · simp [next_i_eq, k0] at * ; omega
                    · simp [svec_slice_eq, map_slice, next_i_eq, k0] at *
                      omega
                  · simp [*, SmtMap_select, SmtMap_store] at *
                    grind
                · trivial
                · trivial
              · intros ; trivial
    · intros v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq _ k4_holds
      and_intros
      · unfold k0 at * ; omega
      · unfold k0 at * ; omega
      · unfold k0 at * ; omega
      · intros _ h_ps_with_elem _ ps_len_lb
        and_intros
        · apply sorted_set_slice
          · simp [k0, k4, *] at *
            by_cases i_eq_0 : i = 0
            · apply sorted_subslice <;>
                simp [*] at * <;> grind
            · simp [*] at *
              rw [ks_hold.left.right.right.right.right.right.left]
              apply append_sorted
              · have tmp : svec_svec_slice { fld0_0 := v1.fld0_0, fld0_1 := v1.fld0_1 } 0 (sorted_bound - i + 1) = svec_svec_slice ps 0 (sorted_bound - i + 1) := by
                  conv =>
                    rhs
                    rw [slice_slice ps 0 (sorted_bound + 1) 0 (sorted_bound - i + 1) (by omega) (by omega)]
                  apply slice_append_left
                  case a => exact ks_hold.left.right.right.right.right.right.left
                  · omega
                  · simp [svec_slice_eq, map_slice]; omega
                  · apply slice_slice <;> omega
                rw [tmp, slice_slice ps 0 sorted_bound 0 (sorted_bound - i + 1) (by omega) (by omega)]
                apply slice_sorted
                · simp [svec_slice_eq, map_slice] ; omega
                · simp [svec_slice_eq, map_slice] ; omega
                · exact ks_hold.left.right.right.right.right.left
              · rw [slice_slice v1 0 sorted_bound (sorted_bound - i) sorted_bound]
                · apply slice_sorted
                  · simp [svec_slice_eq, map_slice] ; omega
                  · simp [svec_slice_eq, map_slice] ; omega
                  · grind
                · omega
                · omega
              · right ; right
                and_intros <;>
                  (simp [svec_slice_eq, map_slice] at * ; grind)
          · simp [k0, k4, *] at *
            grind
          · omega
        · unfold k0 at * ; omega
