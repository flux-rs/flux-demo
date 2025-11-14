import LeanProofs.Lib
import LeanProofs.OpaqueSorts
import LeanProofs.OpaqueFuncs
def svec2_lemma_pop_push_eq := (∀ (reftgen_elems_0 : (VSeq Int)), (∀ (reftgen_len_1 : Int), (∀ (reftgen_e_2 : Int), (∀ (__ : Int), (((svec2_vseq_len reftgen_elems_0) = reftgen_len_1) -> (∀ (__ : Int), ((reftgen_len_1 ≥ 0) -> ((svec2_vseq_get (svec2_vseq_push reftgen_elems_0 reftgen_e_2) reftgen_len_1) = reftgen_e_2))))))))
