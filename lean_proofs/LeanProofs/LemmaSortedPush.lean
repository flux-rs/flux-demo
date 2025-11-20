import LeanProofs.Lib
import LeanProofs.Defs
import LeanProofs.OpaqueSorts
import LeanProofs.OpaqueFuncs
def lemma_sorted_push := (∀ (reftgen_v_0 : (Adt0 Int)), (∀ (reftgen_e_1 : Int), (∀ (__ : Int), (((svec_is_sorted reftgen_v_0) ∧ (reftgen_e_1 > (SmtMap_select (t0 := Int) (t1 := Int) (Adt0.fld0_0 reftgen_v_0) ((Adt0.fld0_1 reftgen_v_0) - 1)))) -> (∀ (__ : Int), (((svec_svec_slice (t0 := Int) (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0)) 0 (Adt0.fld0_1 reftgen_v_0)) = (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0))) -> (∀ (__ : Int), (((Adt0.fld0_1 reftgen_v_0) ≥ 0) -> (svec_is_sorted (Adt0.mkadt0_0 (SmtMap_store (t0 := Int) (t1 := Int) (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0) reftgen_e_1) ((Adt0.fld0_1 reftgen_v_0) + 1)))))))))))
