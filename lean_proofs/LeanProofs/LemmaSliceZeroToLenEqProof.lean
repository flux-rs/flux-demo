import LeanProofs.Lib
import LeanProofs.LemmaSliceZeroToLenEq
def lemma_slice_zero_to_len_eq_proof : lemma_slice_zero_to_len_eq := by
  unfold lemma_slice_zero_to_len_eq
  intros v _ h _ vlen_nonneg
  apply_assumption
