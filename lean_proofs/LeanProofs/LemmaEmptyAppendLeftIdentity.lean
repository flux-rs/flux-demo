import LeanProofs.Lib
import LeanProofs.InferredInstance
def lemma_empty_append_left_identity := (∀ (reftgen_v_0 : (Adt0 Int)), (∀ (__ : Int), (((svec_svec_slice (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0)) 0 (Adt0.fld0_1 reftgen_v_0)) = (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0))) -> (∀ (__ : Int), (((Adt0.fld0_1 reftgen_v_0) ≥ 0) -> ((svec_svec_append (Adt0.mkadt0_0 (svec_empty_seq ) 0) reftgen_v_0) = reftgen_v_0))))))
