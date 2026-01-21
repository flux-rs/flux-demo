import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.InsertSorted
import LeanProofs.User.SharedTheorems

theorem push_sorted (v1 : SvecSVec Int) (e : Int) (h : v1.len ≥ 0) (h1 : svec_is_sorted v1) (h2 : v1.len = 0 ∨ v1.elems (v1.len - 1) ≤ e) : svec_is_sorted (SvecSVec.mkSvecSVec₀ (SmtMap_store v1.elems v1.len e) (v1.len + 1)) := by
  simp at *
  apply is_sorted_imp_map_vec_is_sorted
  simp ; omega
  unfold is_sorted SmtMap_store
  cases h2 with
  | inl v1_len0 =>
    intros
    simp [v1_len0] at * ; omega
  | inr h_le =>
    intros i j i_bounds j_bounds
    simp at *
    have h1' : is_sorted v1 := by
      apply map_vec_is_sorted_imp_is_sorted <;> assumption
    by_cases h : i = v1.len
    · have h' : j = v1.len := by grind
      simp [h, h']
    · simp [h]
      by_cases h' : j = v1.len <;> simp [h']
      · have at_i_lt_last : v1.elems i ≤ v1.elems (v1.len -1) := by
          apply_assumption <;> omega
        omega
      · apply_assumption <;> omega

theorem append_sorted (v1 v2 : SvecSVec Int) (h : v1.len ≥ 0) (h' : v2.len ≥ 0) (h1 : svec_is_sorted v1) (h2 : svec_is_sorted v2) (h3 : v1.len = 0 ∨ v2.len = 0 ∨ ( v1.len > 0 ∧ v2.len > 0 ∧ (v1.elems (v1.len - 1) ≤ v2.elems 0))) : svec_is_sorted (svec_svec_append v1 v2) := by
  simp at *
  have h1' : is_sorted v1 := by
    apply map_vec_is_sorted_imp_is_sorted <;> assumption
  have h2' : is_sorted v2 := by
    apply map_vec_is_sorted_imp_is_sorted <;> assumption
  clear h1 h2
  apply is_sorted_imp_map_vec_is_sorted
  simp ; omega
  intros i j i_bounds j_bounds
  have tmp1 : ¬ i < 0 := by omega
  have tmp2 : ¬ j < 0 := by omega
  simp [tmp1, tmp2, i_bounds, j_bounds]
  cases h3 with
  | inl v1_len0 =>
    simp [v1_len0, tmp1, tmp2, is_sorted] at *
    grind
  | inr h_rest =>
    cases h_rest with
    | inl v2_len0 =>
      by_cases h : j < v1.len
      · have tmp3 : i < v1.len := by omega
        simp [h, tmp3]
        apply_assumption <;> omega
      exfalso ; grind
    | inr nonempty_and_inc =>
      by_cases h : j < v1.len
      · have tmp3 : i < v1.len := by omega
        simp [h, tmp3]
        apply_assumption <;> omega
      by_cases h' : i < v1.len
      · simp [h, h']
        apply Int.le_trans
        · apply h1' i (v1.len - 1) <;> omega
        · apply Int.le_trans
          · apply nonempty_and_inc.right.right
          · apply_assumption <;> grind
      · simp [h, h']
        apply_assumption <;> grind

theorem slice_sorted (v1 : SvecSVec Int) (l r : Int) (h1 : l ≥ 0 ∧ l ≤ v1.len) (h2 : r ≥ l ∧ r ≤ v1.len) (h3 : svec_is_sorted v1) : svec_is_sorted (svec_svec_slice v1 l r) := by
  simp at *
  have h3' : is_sorted v1 := by
    apply map_vec_is_sorted_imp_is_sorted <;> omega
  clear h3
  apply is_sorted_imp_map_vec_is_sorted
  simp ; omega ; unfold is_sorted at *
  intros i j i_bounds j_bounds
  have rl : ¬ r - l < 0 := by omega
  have j_lb' : 0 ≤ j := by omega
  simp [rl] at *
  simp [i_bounds, j_bounds, j_lb']
  apply_assumption <;> omega

namespace InsertSortedCustomKvarSolutions

def k0 : Int → SmtMap Int Int → Int → Int → Prop := fun idx v_elems v_len elem_to_insert => 0 ≤ idx ∧ idx <= v_len ∧ (idx = 0 ∨ elem_to_insert > v_elems (idx - 1))

end InsertSortedCustomKvarSolutions

open InsertSortedCustomKvarSolutions

def InsertSorted_proof : InsertSorted := by
  unfold InsertSorted
  exists k0
  exists InsertSortedKVarSolutions.k1
  exists InsertSortedKVarSolutions.k2
  intros s₀ _ hsorted _ _
  and_intros <;> try omega
  intros i₀ _
  and_intros
  · intros ; unfold InsertSortedKVarSolutions.k1
    right ; simp at * ; unfold k0 at *
    and_intros <;> grind
  · intros ; unfold k0 at * ; and_intros
    · omega
    · intros ; grind [InsertSortedKVarSolutions.k2]
    · intros ; and_intros
      · intros ; grind [InsertSortedKVarSolutions.k1]
      · intros
        and_intros <;> grind [InsertSortedKVarSolutions.k2, SmtMap_select]
  · intros ; and_intros
    · intros ; unfold k0 at * ; and_intros
      · omega
      · omega
      · intros
        apply append_sorted
        · grind
        · simp ; grind
        · have h_len : (svec_svec_slice s₀ 0 i₀).len = i₀ := by
            simp ; grind
          conv => lhs ; arg 1 ; arg 1 ; arg 2 ; rw [← h_len]
          conv => lhs ; arg 1 ; arg 2 ; rw [← h_len]
          apply push_sorted
          · omega
          · apply slice_sorted <;> grind
          · by_cases idx_eq_0 : i₀ = 0 <;> rw [h_len]
            · left ; assumption
            · right ; simp ; grind
        · apply slice_sorted <;> omega
        · simp ; right ; right
          and_intros
          · omega
          · omega
          · simp [SmtMap_store, InsertSortedKVarSolutions.k1] at *
            have tmp : i₀ < s₀.len := by omega
            simp [tmp]
            grind [SmtMap_select]
    · intros
      unfold k0 at *
      apply push_sorted <;> grind
