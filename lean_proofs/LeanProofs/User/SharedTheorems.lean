import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec

def map_vec_is_sorted (v : SvecSVec Int) : Bool :=
  (List.range' 0 v.len.natAbs).all
    (fun i => (List.range' i (v.len.natAbs - i)).all
      (fun j => v.elems (Int.ofNat i) ≤ v.elems (Int.ofNat j))
    )

def is_sorted (v : SvecSVec Int) : Prop := ∀ (i j : Int), 0 ≤ i ∧ i < v.len → i ≤ j ∧ j < v.len → v.elems i ≤ v.elems j

theorem map_vec_is_sorted_iff (v : SvecSVec Int) { h_len : v.len ≥ 0 } :
  is_sorted v ↔ map_vec_is_sorted v = true :=
by
  apply Iff.intro
  · intro hsorted
    unfold is_sorted map_vec_is_sorted at *
    simp ; intros
    apply_assumption <;> grind
  · intro hsorted
    unfold is_sorted map_vec_is_sorted at *
    simp at *
    intros i j i_lb i_ub j_lb j_ub
    have j_ge_0 : 0 ≤ j := by omega
    have h : v.elems i.natAbs ≤ v.elems j.natAbs := by
      apply_assumption
      · grind
      · grind
      · rw [Nat.add_sub_cancel'] <;> grind
    conv at h => lhs ; rw [Int.natAbs_of_nonneg i_lb]
    conv at h => rhs ; rw [Int.natAbs_of_nonneg j_ge_0]
    assumption

def is_sorted_imp_map_vec_is_sorted (v : SvecSVec Int) { h_len : v.len ≥ 0} :
  is_sorted v → (map_vec_is_sorted v = true) := by
    apply (map_vec_is_sorted_iff v).mp
    assumption

def map_vec_is_sorted_imp_is_sorted (v : SvecSVec Int) { h_len : v.len ≥ 0} :
  (map_vec_is_sorted v = true) → is_sorted v := by
    apply (map_vec_is_sorted_iff v).mpr
    assumption
