import LeanProofs.Lib
import LeanProofs.Svec2LemmaPopPushEq
import LeanProofs.SharedTheorems

def svec2_lemma_pop_push_eq_proof : svec2_lemma_pop_push_eq := by
  unfold svec2_lemma_pop_push_eq
  intros elems len val _ lengths_match _ len_nonneg
  rw [svec2_vseq_get_eq, svec2_vseq_push_eq] ; simp
  rw [svec2_vseq_len_eq] at lengths_match ; simp at lengths_match
  unfold flip ; simp ; rw [lengths_match]
  grind
