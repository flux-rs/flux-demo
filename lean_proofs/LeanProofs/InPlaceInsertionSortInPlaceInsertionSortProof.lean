import LeanProofs.Lib
import LeanProofs.InPlaceInsertionSortInPlaceInsertionSort
import LeanProofs.SharedTheorems

def k0 : SmtMap Int Int → Int → Int → SmtMap Int Int → Int → Prop := fun elems len idx _v_elems _v_len =>
  let v'  := Adt0.mkadt0_0 elems len
  1 ≤ idx ∧ idx ≤ len ∧ (svec_is_sorted <| svec_svec_slice v' 0 idx)

def k1 : Int → Int → SmtMap Int Int → Int → Prop := fun _ _ _ _ => True
def k2 : Int → SmtMap Int Int → Int → Prop := fun _ _ _ => True
def k3 : Int → SmtMap Int Int → Int → SmtMap Int Int → Int → Int → Prop := fun _ _ _ _ _ _ => True

theorem small_sorted (v : Adt0 Int) (h : 0 ≤ v.fld0_1 ∧ v.fld0_1 ≤ 1) : svec_is_sorted v := by
  simp [svec_is_sorted_eq]
  intros i j _ _ _ _
  by_cases i = 0
  · have j_eq0 : j = 0 := by omega
    simp [*]
  · have j_eqi : j = i := by omega
    simp [*]


def in_place_insertion_sort_in_place_insertion_sort_proof : in_place_insertion_sort_in_place_insertion_sort := by
  unfold in_place_insertion_sort_in_place_insertion_sort
  exists k0, k1, k2, k3
  unfold k0 k1 k2 k3 at *
  intros
  and_intros
  · intros
    and_intros
    · intros
      and_intros <;> try grind
      apply small_sorted
      simp [svec_slice_eq, map_slice]
      grind
    · intros ps idx ps_elems ps_elems_eq ps_len ps_len_eq v_elems v_elems_eq v_len v_len_eq _ ks _ ps_len_lb
      and_intros
      · intros _ idx_ge_ps_len
        have idx_eq : idx = ps.fld0_1 := by omega
        have tmp1 : ¬ ps.fld0_1 < 0 := by omega
        simp [idx_eq, svec_slice_eq, svec_is_sorted_eq, map_slice, tmp1] at *
        have tmp3 : 0 ≤ (0:Int) ∧ (0:Int) < ps.fld0_1 := by omega
        have tmp4 : (0:Int) ≤ (0:Int) ∧ (0:Int) < ps.fld0_1 := by omega
        simp [tmp3, tmp4, ps_elems_eq] at *
        grind
      · intros _ idx_lt_ps_len
        and_intros
        · omega
        · intros; trivial
        · intros
          and_intros
          · simp [*] at *
            exact ks.right.right
          · omega
          · intros next_vec _ next_vec_sorted _ h_next_vec _ next_vec_len_lb next_vec_elems next_vec_elems_eq next_vec_len next_vec_len_eq next_idx next_idx_eq v_elems v_elems_eq v_len v_len_eq
            have tmp1 : ¬ next_idx < 0 := by omega
            simp [svec_is_sorted_eq, svec_slice_eq, map_slice, tmp1] at *
            and_intros <;> try grind
            intros i j _ _ _ _
            have tmp2 : 0 ≤ i ∧ i < next_idx := by omega
            have tmp3 : 0 ≤ j ∧ j < next_idx := by omega
            have tmp5 : ¬ idx + 1 < 0 := by omega
            have tmp6 : i < idx + 1 := by omega
            have tmp7 : j < idx + 1 := by omega
            simp [next_idx_eq, tmp2, tmp3, tmp5, tmp6, tmp7, next_vec_elems_eq] at *
            grind
  · grind [small_sorted]
