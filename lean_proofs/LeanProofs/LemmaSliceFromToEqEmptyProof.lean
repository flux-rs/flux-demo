import LeanProofs.Lib
import LeanProofs.LemmaSliceFromToEqEmpty
import LeanProofs.SharedTheorems

def lemma_slice_from_to_eq_empty_proof : lemma_slice_from_to_eq_empty := by
  unfold lemma_slice_from_to_eq_empty
  intros
  simp [svec_slice_eq, svec_empty_seq_eq, map_slice] at *
  funext
  grind
