import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaAppendEmptyRfl

namespace F

def LemmaAppendEmptyRfl_proof : LemmaAppendEmptyRfl := by
  unfold LemmaAppendEmptyRfl
  intro b₀ e₀
  intro h_slice_b
  intro h_b_len_nonneg
  intro _h_slice_e
  intro h_e_len_nonneg
  -- Goal: b₀ = svec_svec_append b₀ (svec_svec_slice e₀ 0 0)
  -- slice e₀ 0 0 has len = 0
  -- append b₀ (empty) should equal b₀
  simp only [svec_svec_append, svec_svec_slice, map_append, map_slice]
  -- Simplify the slice e₀ 0 0 part
  have h_zero_lt : ¬(0 < (0 : Int)) := by omega
  simp only [h_zero_lt, ↓reduceIte, Int.sub_zero, Int.add_zero]
  -- Now use the hypothesis about b₀
  simp only [svec_svec_slice, map_slice, Int.sub_zero, Int.add_zero] at h_slice_b
  have h_len_neg : ¬(b₀.len < 0) := by omega
  simp only [h_len_neg, ↓reduceIte] at h_slice_b
  -- h_slice_b : { elems := ..., len := b₀.len } = { elems := b₀.elems, len := b₀.len }
  -- Extract the elems equality
  have h_elems_eq : (fun x => if 0 ≤ x ∧ x < b₀.len then b₀.elems x else default) = b₀.elems := by
    exact congrArg SvecSVec.elems h_slice_b
  -- Now prove the goal
  ext
  · -- elems
    funext x
    by_cases hx_neg : x < 0
    · simp only [hx_neg, ↓reduceIte]
      have h_at_x := congrFun h_elems_eq x
      have h_cond : ¬(0 ≤ x ∧ x < b₀.len) := by omega
      simp only [h_cond, ↓reduceIte] at h_at_x
      exact h_at_x.symm
    · simp only [hx_neg, ↓reduceIte]
      by_cases hx_lt : x < b₀.len
      · simp only [hx_lt, ↓reduceIte]
      · simp only [hx_lt, ↓reduceIte]
        have h_at_x := congrFun h_elems_eq x
        have h_cond : ¬(0 ≤ x ∧ x < b₀.len) := by omega
        simp only [h_cond, ↓reduceIte] at h_at_x
        exact h_at_x.symm
  · -- len
    rfl

end F
