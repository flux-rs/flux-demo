import LeanProofs.Lib
import LeanProofs.Defs
import LeanProofs.OpaqueSorts
import LeanProofs.OpaqueFuncs
def lemma_slice_from_to_eq_empty := (∀ (reftgen_v_0 : (Adt0 Int)), (∀ (reftgen_idx_1 : Int), (∀ (__ : Int), ((reftgen_idx_1 ≤ (Adt0.fld0_1 reftgen_v_0)) -> (∀ (__ : Int), (((svec_svec_slice (t0 := Int) (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0)) 0 (Adt0.fld0_1 reftgen_v_0)) = (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0))) -> (∀ (__ : Int), (((Adt0.fld0_1 reftgen_v_0) ≥ 0) -> (∀ (__ : Int), ((reftgen_idx_1 ≥ 0) -> ((svec_svec_slice (t0 := Int) reftgen_v_0 reftgen_idx_1 reftgen_idx_1) = (Adt0.mkadt0_0 (svec_empty_seq (t0 := Int) ) 0))))))))))))
