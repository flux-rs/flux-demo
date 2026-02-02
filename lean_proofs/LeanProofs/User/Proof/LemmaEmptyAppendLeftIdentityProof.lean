import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaEmptyAppendLeftIdentity

namespace F

def LemmaEmptyAppendLeftIdentity_proof : LemmaEmptyAppendLeftIdentity := by
  unfold LemmaEmptyAppendLeftIdentity
  intro v₀
  intro h_slice_v
  intro h_len_nonneg
  -- Goal: svec_svec_append (mkSvecSVec₀ svec_empty_seq 0) v₀ = v₀
  -- The empty vector has len = 0, so append gives:
  -- { elems := fun x => if x < 0 then default else if x < 0 then ... else if x < v₀.len then v₀.elems (x - 0) else default,
  --   len := 0 + v₀.len }
  simp only [svec_svec_append, map_append, Int.zero_add, Int.sub_zero]
  -- Extract info from slice hypothesis
  simp only [svec_svec_slice, map_slice, Int.sub_zero, Int.add_zero] at h_slice_v
  have h_len_not_neg : ¬(v₀.len < 0) := by omega
  simp only [h_len_not_neg, ↓reduceIte] at h_slice_v
  have h_elems_eq : (fun x => if 0 ≤ x ∧ x < v₀.len then v₀.elems x else default) = v₀.elems := by
    exact congrArg SvecSVec.elems h_slice_v
  -- Now prove the goal
  ext
  · -- elems
    funext x
    by_cases hx_neg : x < 0
    · simp only [hx_neg, ↓reduceIte]
      have h_at_x := congrFun h_elems_eq x
      have h_cond : ¬(0 ≤ x ∧ x < v₀.len) := by omega
      simp only [h_cond, ↓reduceIte] at h_at_x
      exact h_at_x
    · simp only [hx_neg, ↓reduceIte]
      -- x >= 0, so "if x < 0" is false
      -- Goal: (if x < v₀.len then v₀.elems x else default) = v₀.elems x
      by_cases hx_lt : x < v₀.len
      · simp only [hx_lt, ↓reduceIte]
      · simp only [hx_lt, ↓reduceIte]
        have h_at_x := congrFun h_elems_eq x
        have h_cond : ¬(0 ≤ x ∧ x < v₀.len) := by omega
        simp only [h_cond, ↓reduceIte] at h_at_x
        exact h_at_x
  · -- len
    rfl

end F
