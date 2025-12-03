import LeanProofs.Lib
import LeanProofs.InPlaceInsertionSortInsertSorted
import LeanProofs.SharedTheorems




theorem slice_slice (v1 : Adt0 Int) (l r l' r' : Int) (h1 : l ≤ l') (h2: r' ≤ r) : svec_svec_slice v1 l' r' = svec_svec_slice (svec_svec_slice v1 l r) l' r' := by
  sorry

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

theorem slice_sorted (v1 : Adt0 Int) (l r : Int) (h1 : l ≥ 0 ∧ l ≤ v1.fld0_1) (h2 : r ≥ l ∧ r ≤ v1.fld0_1) (h3 : svec_is_sorted v1) : svec_is_sorted (svec_svec_slice v1 l r) := by
  simp [svec_is_sorted_eq, svec_slice_eq, map_slice] at *
  intros i j i_lb i_ub j_lb j_ub
  have rl : ¬ r - l < 0 := by omega
  have j_lb' : 0 ≤ j := by omega
  simp [rl] at *
  simp [i_lb, i_ub, j_lb', j_ub]
  apply_assumption <;> omega

theorem sorted_set_slice (v : Adt0 Int) (right idx elem : Int) (h1 : svec_is_sorted (svec_svec_slice v 0 right)) (h2: (idx = 0 ∨ elem ≥ v.fld0_0 (idx - 1)) ∧ (elem ≤ v.fld0_0 idx ∨ idx = right)) : svec_is_sorted (svec_svec_slice (Adt0.mkadt0_0 (SmtMap_store v.fld0_0 idx elem) v.fld0_1) 0 right) := by
  sorry

theorem eq_append (v1 v2 v3 : Adt0 Int) { l2 l3 : Int} { h1 : l2 = v2.fld0_1 } { h2 : l3 = v3.fld0_1 } : v2 = svec_svec_slice v1 0 l2 → v3 = svec_svec_slice v1 l2 (l2 + l3) → l2 + l3 = v1.fld0_1 → v1 = svec_svec_append v2 v3 := by
  sorry

theorem sorted_subslice (v : Adt0 Int) (r : Int) : svec_is_sorted (svec_svec_slice v 0 r) → v.fld0_0 r ≥ v.fld0_0 (r - 1) → svec_is_sorted (svec_svec_slice v 0 (r + 1)) := by
  sorry

theorem slice_append_left (v1 v2 v3 v4 : Adt0 Int) { l r : Int } : v1 = svec_svec_append v2 v3 → v4 = svec_svec_slice v2 l r → v4 = svec_svec_slice v1 l r := by
  sorry

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
  and_intros
  · intros v1_elems v1_elems_eq v1_len v1_len_eq idx idx_eq v1_elems v1_elems_eq v1_len v1_len_eq
    unfold k0 k1 k2
    and_intros <;> simp [SmtMap_select, *]
  · intros -- a5 v1_elems v1_elems_eq v1_len v1_len_eq a8 a8_eq v1_elems v1_elems_eq v1_len v1_len_eq
    trivial
  · intros ps i ps_elems ps_elems_eq ps_len ps_len_eq v1_elems v1_elems_eq v1_len v1_len_eq _ ks_hold
    and_intros
    · intros -- _ i_ge_sorted_bound v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq
      -- k4 holds when i >= sorted_bound
      unfold k4
      unfold k0 at * ; omega
    · intros _ i_lt_sorted_bound
      and_intros
      · omega
      · omega
      · omega
      · unfold k0 at ks_hold ; omega
      · intros -- a21 ps_elems ps_elems_eq ps_len ps_len_eq v1_elems v1_elems_eq v1_len v1_len_eq _ k3_holds v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq
        -- k5 holds while i < sorted_bound & k3 holds
        trivial
      · intros ps_at_i ps_at_i_eq v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq _ k5_holds
        and_intros
        · intros _ elem_ge_ps_at_i v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq
          unfold k4
          unfold k0 at *
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
          · intros -- a39 ps_elems ps_elems_eq ps_len ps_len_eq v1_elems v1_elems_eq v1_len v1_len_eq _ k3_holds v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq
            trivial
          · intros ps_at_i ps_at_i_eq v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq _ k6_holds
            and_intros
            · omega
            · unfold k0 at ks_hold ; omega
            · intros -- a53 ps_elems ps_elems_eq ps_len ps_len_eq v1_elems v1_elems_eq v1_len v1_len_eq _ k3_holds v1_elems v1_elems_eqv1 v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq
              trivial
            · intros -- ps_at_i ps_at_i_eq v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_e
              trivial
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
                    · right ; omega
                    · left
                      have tmp1 : ps.fld0_0 (sorted_bound - i - 1) = (svec_svec_slice ps 0 sorted_bound).fld0_0 (sorted_bound - i -1) := by
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
                    · rw [←slice_slice]
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
                    · rw [←slice_slice]
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
              · intros --a72 v1_elems v1_elems_eq v1_len v1_len_eq ps_elems ps_elems_eq ps_len ps_len_eq _ k7_holds ps_dup ps_dup_eq ps_dup_len ps_dup_len_eq next_i next_i_eq v1_elems v1_elems_eq v1_len v1_len_eq
                trivial
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
            · apply sorted_subslice <;> simp [*] at * ; grind
            · simp [*] at *
              rw [ks_hold.left.right.right.right.right.right.left]
              apply append_sorted
              · have tmp : svec_svec_slice { fld0_0 := v1.fld0_0, fld0_1 := v1.fld0_1 } 0 (sorted_bound - i + 1) = svec_svec_slice ps 0 (sorted_bound - i + 1) := by
                  conv =>
                    rhs
                    rw [slice_slice ps 0 (sorted_bound + 1) 0 (sorted_bound - i + 1) (by omega) (by omega)]
                  apply slice_append_left
                  · exact ks_hold.left.right.right.right.right.right.left
                  · apply slice_slice <;> omega
                rw [tmp, slice_slice ps 0 sorted_bound 0 (sorted_bound - i + 1) (by omega) (by omega)]
                apply slice_sorted
                · simp [svec_slice_eq, map_slice] ; omega
                · simp [svec_slice_eq, map_slice] ; omega
                · exact ks_hold.left.right.right.right.right.left
              · sorry
              · right ; right
                and_intros <;>
                  (simp [svec_slice_eq, map_slice] at * ; grind)
          · simp [k0, k4, *] at *
            grind
        · unfold k0 at * ; omega
