import LeanProofs.Lib
import LeanProofs.Defs
import LeanProofs.OpaqueSorts
import LeanProofs.OpaqueFuncs
def lemma_svec_slice_len_eq := (∀ (reftgen_v_0 : (Adt0 Int)), (∀ (reftgen_l_1 : Int), (∀ (reftgen_r_2 : Int), (∀ (__ : Int), ((reftgen_l_1 ≤ (Adt0.fld0_1 reftgen_v_0)) -> (∀ (__ : Int), (((reftgen_l_1 ≤ reftgen_r_2) ∧ (reftgen_r_2 ≤ (Adt0.fld0_1 reftgen_v_0))) -> (∀ (__ : Int), (((svec_svec_slice (t0 := Int) (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0)) 0 (Adt0.fld0_1 reftgen_v_0)) = (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0))) -> (∀ (__ : Int), (((Adt0.fld0_1 reftgen_v_0) ≥ 0) -> (∀ (__ : Int), ((reftgen_l_1 ≥ 0) -> (∀ (__ : Int), ((reftgen_r_2 ≥ 0) -> ((Adt0.fld0_1 (svec_svec_slice (t0 := Int) reftgen_v_0 reftgen_l_1 reftgen_r_2)) = (reftgen_r_2 - reftgen_l_1)))))))))))))))))
