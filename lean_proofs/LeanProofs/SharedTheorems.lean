import LeanProofs.OpaqueFuncs
import LeanProofs.Lib

theorem svec_empty_seq_eq { t0 : Type } [Inhabited t0] : svec_empty_seq = (fun _ => (inferInstance : Inhabited t0).default) := rfl
theorem svec_append_eq { t0 : Type } [Inhabited t0] : @svec_svec_append t0 = @map_append t0 := rfl
theorem svec_slice_eq { t0 : Type } [Inhabited t0] : @svec_svec_slice t0 = @map_slice t0 := rfl
theorem svec_is_sorted_eq (v : Adt0 Int) : svec_is_sorted v = ∀ i j : Int, (h1 : 0 ≤ i ∧ i < v.fld0_1) → (h2 : i ≤ j ∧ j < v.fld0_1) → v.fld0_0 i ≤ v.fld0_0 j := by rfl
theorem svec2_vseq_get_eq { t0 : Type } [i: Inhabited t0] : @svec2_vseq_get t0 i = fun l p => l.getD (l.length - p - 1).natAbs default := rfl
theorem svec2_vseq_set_eq { t0 : Type } [i: Inhabited t0] : @svec2_vseq_set t0 i = fun l p e => l.set (l.length - p - 1).natAbs e := rfl
theorem svec2_vseq_push_eq { t0 : Type } [i: Inhabited t0] : @svec2_vseq_push t0 i = flip List.cons := rfl
theorem svec2_vseq_len_eq { t0 : Type } [i: Inhabited t0] : @svec2_vseq_len t0 i = Int.ofNat ∘ List.length := rfl

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

theorem eq_append (v1 v2 v3 : Adt0 Int) { l2 l3 : Int} { h1 : l2 = v2.fld0_1 } { h2 : l3 = v3.fld0_1 } { h3 : l2 ≥ 0 } { h4 : l3 ≥ 0 } { h5 : ∀ x : Int, x < 0 → v1.fld0_0 x = 0 } { h6 : ∀ x : Int, x ≥ l2 + l3 → v1.fld0_0 x = 0 } : v2 = svec_svec_slice v1 0 l2 → v3 = svec_svec_slice v1 l2 (l2 + l3) → l2 + l3 = v1.fld0_1 → v1 = svec_svec_append v2 v3 := by
  intros h1 h2 h3
  rw [h1, h2]
  ext <;> simp [svec_append_eq, map_append, svec_slice_eq, map_slice]
  · funext x
    grind
  · omega

theorem sorted_subslice (v : Adt0 Int) (r : Int) { h : 1 ≤ r } { h' : r ≤ v.fld0_1 } : svec_is_sorted (svec_svec_slice v 0 r) → v.fld0_0 r ≥ v.fld0_0 (r - 1) → svec_is_sorted (svec_svec_slice v 0 (r + 1)) := by
  simp [svec_is_sorted_eq, svec_slice_eq, map_slice]
  intros h1 h2 i j i_lb i_ub j_lb j_ub
  have tmp1 : 0 ≤ i ∧ i < r + 1 := by omega
  have tmp2 : 0 ≤ j ∧ j < r + 1 := by omega
  simp [tmp1, tmp2]
  by_cases j < r
  · have tmp := h1 i j
    have tmp3 : ¬ r < 0 := by omega
    have tmp4 : 0 ≤ i ∧ i < r := by omega
    grind
  · by_cases tmp' : i = r
    · have tmp : j = r := by omega
      grind
    · have tmp : j = r := by omega
      rw [tmp]
      apply @Int.le_trans (v.fld0_0 i) (v.fld0_0 (r - 1))
      · have tmp := h1 i (r - 1)
        have tmp3 : ¬ r < 0 := by omega
        have tmp4 : r - 1 < r := by omega
        grind
      · assumption

theorem sorted_set_slice (v : Adt0 Int) (right idx elem : Int) (h1 : svec_is_sorted (svec_svec_slice v 0 right)) (h2: (idx = 0 ∨ (idx ≠ 0 ∧ elem ≥ v.fld0_0 (idx - 1))) ∧ ((idx ≠ right ∧ elem ≤ v.fld0_0 idx) ∨ idx = right)) { h3 : right ≥ 0 } : svec_is_sorted (svec_svec_slice (Adt0.mkadt0_0 (SmtMap_store v.fld0_0 idx elem) v.fld0_1) 0 right) := by
  have ⟨h2, h3⟩ := h2
  cases h2 with
  | inl idx_eq_0 =>
    simp [idx_eq_0, svec_is_sorted_eq, svec_slice_eq, map_slice, SmtMap_store]
    intros i j i_lb i_ub j_lb j_ub
    have tmp1 : ¬ right < 0 := by omega
    simp [tmp1] at i_ub j_ub
    have tmp2 : 0 ≤ j := by omega
    simp [i_lb, i_ub, tmp2, j_ub]
    by_cases j = 0
    · have tmp3 : i = 0 := by omega
      simp [*]
    · by_cases i = 0
      · simp [*]
        cases h3 with
        | inl elem_le_idx =>
          rw [idx_eq_0] at elem_le_idx
          apply @Int.le_trans elem (v.fld0_0 0)
          · grind
          · have tmp := h1 0 j
            have tmp4 : 0 < right := by omega
            simp [svec_slice_eq, map_slice, tmp1, tmp2, j_ub, tmp4] at tmp
            assumption
        | inr idx_eq_right => grind
      · simp [*]
        have tmp := h1 i j
        simp [svec_slice_eq, map_slice, tmp1, i_lb, i_ub, tmp2, j_ub] at tmp
        apply_assumption
        omega
  | inr elem_ge_prev =>
    cases h3 with
    | inl elem_le_next =>
      simp [svec_is_sorted_eq, svec_slice_eq, map_slice, SmtMap_store]
      intros i j i_lb i_ub j_lb j_ub
      have tmp1 : ¬ right < 0 := by omega
      simp [tmp1] at i_ub j_ub
      have tmp2 : 0 ≤ j := by omega
      simp [i_lb, tmp2, i_ub, j_ub]
      by_cases i_eq_idx : i = idx
      · by_cases j_eq_idx : j = idx
        · omega
        · simp [i_eq_idx, j_eq_idx]
          apply @Int.le_trans elem (v.fld0_0 idx)
          · grind
          · rw [←i_eq_idx]
            have tmp := h1 i j
            simp [svec_slice_eq, map_slice, tmp1, i_lb, tmp2, i_ub, j_ub] at tmp
            grind
      · by_cases j_eq_idx : j = idx
        · simp [i_eq_idx, j_eq_idx]
          apply @Int.le_trans (v.fld0_0 i) (v.fld0_0 (idx - 1))
          · rw [←j_eq_idx]
            have tmp := h1 i (j - 1)
            have tmp3 : j - 1 < right := by omega
            have tmp4 : 1 ≤ j := by omega
            simp [svec_slice_eq, map_slice, tmp1, i_lb, i_ub, tmp3, tmp4] at tmp
            grind
          · omega
        · simp [i_eq_idx, j_eq_idx]
          have tmp := h1 i j
          simp [svec_slice_eq, map_slice, tmp1, i_lb, tmp2, i_ub, j_ub] at tmp
          grind
    | inr idx_eq_right =>
      simp [svec_is_sorted_eq, svec_slice_eq, map_slice, SmtMap_store]
      intros i j i_lb i_ub j_lb j_ub
      have tmp1 : ¬ right < 0 := by omega
      simp [tmp1] at i_ub j_ub
      have tmp2 : 0 ≤ j := by omega
      have tmp3 : ¬ i = idx := by omega
      have tmp4 : ¬ j = idx := by omega
      simp [i_lb, i_ub, tmp2, j_ub, tmp3, tmp4]
      have tmp := h1 i j
      simp [svec_slice_eq, map_slice, tmp1, i_lb, i_ub, tmp2, j_ub] at tmp
      grind

theorem slice_append_left (v1 v2 v3 v4 : Adt0 Int) { l r : Int } { h1 : 0 ≤ l } { h2 : r ≤ v2.fld0_1 }: v1 = svec_svec_append v2 v3 → v4 = svec_svec_slice v2 l r → v4 = svec_svec_slice v1 l r := by
  intros h3 h4
  rw [h4]
  simp [svec_slice_eq, map_slice]
  funext x
  by_cases 0 ≤ x ∧ x < r - l
  · have tmp1 : x + l < v2.fld0_1 := by omega
    simp [*, svec_append_eq, map_append]
    grind
  · omega

theorem slice_slice (v1 : Adt0 Int) (l r l' r' : Int) (h1 : 0 ≤ l ∧ l ≤ l') (h2: r' ≤ r ∧ r ≤ v1.fld0_1) : svec_svec_slice v1 l' r' = svec_svec_slice (svec_svec_slice v1 l r) (l' - l) (r' - l) := by
  simp [svec_slice_eq, map_slice]
  and_intros
  · funext x
    by_cases 0 ≤ x ∧ x < r' - l'
    · have tmp : x < r' - l - (l' - l) := by omega
      have tmp' : 0 ≤ x + (l' - l) ∧ x + (l' - l) < r - l := by omega
      simp [*]
      grind
    · simp [*] ; omega
  · omega
