import LeanProofs.Lib
import LeanProofs.OpaqueFluxDefs

def map_append { t0 : Type } [Inhabited t0] (v1 v2 : Adt0 t0) := Adt0.mkadt0_0 (fun x => if x < 0 then (inferInstance : Inhabited t0).default else if x < v1.fld0_1 then v1.fld0_0 x else if x < v1.fld0_1 + v2.fld0_1 then v2.fld0_0 (x - v1.fld0_1) else (inferInstance : Inhabited t0).default) (v1.fld0_1 + v2.fld0_1)

def map_slice { t0 : Type } [Inhabited t0] (v1 : Adt0 t0) (left right : Int) := Adt0.mkadt0_0 (fun x => if 0 <= x ∧ x < (right - left) then v1.fld0_0 (x + left) else default) (if right - left < 0 then 0 else right - left)

instance : FluxDefs where
  svec_default_elem := default
  svec_empty_seq { t0 : Type } [Inhabited t0] := fun _ => default
  svec_svec_append := map_append
  svec_svec_slice := map_slice
