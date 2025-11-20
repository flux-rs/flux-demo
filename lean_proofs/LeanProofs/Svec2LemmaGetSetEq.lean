import LeanProofs.Lib
import LeanProofs.Defs
import LeanProofs.OpaqueSorts
import LeanProofs.OpaqueFuncs
def svec2_lemma_get_set_eq := (∀ (reftgen_elems_0 : (VSeq Int)), (∀ (reftgen_len_1 : Int), (∀ (reftgen_i_2 : Int), (∀ (reftgen_e_3 : Int), (∀ (__ : Int), (((0 ≤ reftgen_i_2) ∧ (reftgen_i_2 < reftgen_len_1)) -> (∀ (__ : Int), (((svec2_vseq_len (t0 := Int) reftgen_elems_0) = reftgen_len_1) -> (∀ (__ : Int), ((reftgen_len_1 ≥ 0) -> (∀ (__ : Int), ((reftgen_i_2 ≥ 0) -> ((svec2_vseq_get (t0 := Int) (svec2_vseq_set (t0 := Int) reftgen_elems_0 reftgen_i_2 reftgen_e_3) reftgen_i_2) = reftgen_e_3)))))))))))))
