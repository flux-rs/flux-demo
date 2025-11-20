import LeanProofs.Lib
import LeanProofs.Defs
import LeanProofs.OpaqueSorts
import LeanProofs.OpaqueFuncs
def sorted := (∀ (reftgen_v_0 : (Adt0 Int)), (∀ (__ : Int), (((Adt0.fld0_1 reftgen_v_0) > 0) -> (∀ (__ : Int), (((svec_svec_slice (t0 := Int) (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0)) 0 (Adt0.fld0_1 reftgen_v_0)) = (Adt0.mkadt0_0 (Adt0.fld0_0 reftgen_v_0) (Adt0.fld0_1 reftgen_v_0))) -> (∀ (__ : Int), (((Adt0.fld0_1 reftgen_v_0) ≥ 0) -> (∀ (__ : Int), (((svec_svec_slice (t0 := Int) (Adt0.mkadt0_0 (svec_empty_seq (t0 := Int) ) 0) 0 0) = (Adt0.mkadt0_0 (svec_empty_seq (t0 := Int) ) 0)) -> (∀ (__ : Int), (∀ (__ : Int), ((svec_is_sorted (Adt0.mkadt0_0 (svec_empty_seq (t0 := Int) ) 0)) -> (0 < (Adt0.fld0_1 reftgen_v_0))))))))))))))
