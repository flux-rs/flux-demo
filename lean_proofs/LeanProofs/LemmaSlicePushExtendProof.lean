import LeanProofs.Lib
import LeanProofs.LemmaSlicePushExtend
import LeanProofs.SharedTheorems

def lemma_slice_push_extend_proof : lemma_slice_push_extend := by
  unfold lemma_slice_push_extend
  intros v l r _ l_ubound _ r_bounds _ h_v _ vlen_lbound _ l_lbound _ _
  unfold SmtMap_store SmtMap_select
  simp [svec_slice_eq, map_slice] at *
  and_intros
  · funext x
    by_cases h : x = r - l
    · grind
    · simp [h]
      by_cases h1 : 0 ≤ x ∧ x < r - l <;>
      (simp [h1] ; grind)
  · grind
