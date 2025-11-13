import LeanProofs.Lib
import LeanProofs.Svec2LemmaGetSetEq
import LeanProofs.SharedTheorems

def svec2_lemma_get_set_eq_proof : svec2_lemma_get_set_eq := by
  unfold svec2_lemma_get_set_eq
  intros elems len pos elem _ pos_bounds _ lengths_match _ len_nonneg _ pos_nonneg
  rw [svec2_vseq_get_eq, svec2_vseq_set_eq] ; simp
  rw [svec2_vseq_len_eq] at lengths_match ; simp at lengths_match
  rw [lengths_match, List.getElem?_set] ; simp
  grind
