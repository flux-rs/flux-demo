import LeanProofs.InferredInstance
import LeanProofs.Lib

theorem svec_empty_seq_eq { t0 : Type } [Inhabited t0] : svec_empty_seq = (fun _ => (inferInstance : Inhabited t0).default) := rfl
theorem svec_append_eq { t0 : Type } [Inhabited t0] : @svec_svec_append t0 = @map_append t0 := rfl
theorem svec_slice_eq { t0 : Type } [Inhabited t0] : @svec_svec_slice t0 = @map_slice t0 := rfl
