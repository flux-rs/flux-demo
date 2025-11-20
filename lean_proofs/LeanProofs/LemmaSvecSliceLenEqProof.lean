import LeanProofs.Lib
import LeanProofs.LemmaSvecSliceLenEq
import LeanProofs.SharedTheorems

def lemma_svec_slice_len_eq_proof : lemma_svec_slice_len_eq := by
  unfold lemma_svec_slice_len_eq
  intros
  simp [svec_slice_eq, map_slice] at *
  grind
