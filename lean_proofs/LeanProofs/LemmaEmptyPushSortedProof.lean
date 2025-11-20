import LeanProofs.Lib
import LeanProofs.LemmaEmptyPushSorted
import LeanProofs.SharedTheorems

def lemma_empty_push_sorted_proof : lemma_empty_push_sorted := by
  unfold lemma_empty_push_sorted
  intros
  simp [svec_is_sorted_eq, svec_slice_eq, SmtMap_store, map_slice] at *
  intros
  omega
