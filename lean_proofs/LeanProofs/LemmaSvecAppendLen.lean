import LeanProofs.Lib
import LeanProofs.OpaqueSorts
import LeanProofs.OpaqueFuncs
def lemma_svec_append_len := (∀ (reftgen_v1_0 : (Adt0 Int)), (∀ (reftgen_v2_1 : (Adt0 Int)), (∀ (__ : Int), (((svec_svec_slice (t0 := Int) (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v2_1) (Adt0.fld0_1 reftgen_v2_1)) 0 (Adt0.fld0_1 reftgen_v2_1)) = (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v2_1) (Adt0.fld0_1 reftgen_v2_1))) -> (∀ (__ : Int), (((Adt0.fld0_1 reftgen_v2_1) ≥ 0) -> ((Adt0.fld0_1 (svec_svec_append (t0 := Int) reftgen_v1_0 reftgen_v2_1)) = ((Adt0.fld0_1 reftgen_v1_0) + (Adt0.fld0_1 reftgen_v2_1)))))))))
