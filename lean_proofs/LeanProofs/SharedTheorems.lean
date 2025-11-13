import LeanProofs.OpaqueFuncs
import LeanProofs.Lib

theorem svec_empty_seq_eq { t0 : Type } [Inhabited t0] : svec_empty_seq = (fun _ => (inferInstance : Inhabited t0).default) := rfl
theorem svec_append_eq { t0 : Type } [Inhabited t0] : @svec_svec_append t0 = @map_append t0 := rfl
theorem svec_slice_eq { t0 : Type } [Inhabited t0] : @svec_svec_slice t0 = @map_slice t0 := rfl
theorem svec2_vseq_get_eq { t0 : Type } [i: Inhabited t0] : @svec2_vseq_get t0 i = fun l p => l.getD (l.length - p - 1).natAbs default := rfl
theorem svec2_vseq_set_eq { t0 : Type } [i: Inhabited t0] : @svec2_vseq_set t0 i = fun l p e => l.set (l.length - p - 1).natAbs e := rfl
theorem svec2_vseq_push_eq { t0 : Type } [i: Inhabited t0] : @svec2_vseq_push t0 i = flip List.cons := rfl
theorem svec2_vseq_len_eq { t0 : Type } [i: Inhabited t0] : @svec2_vseq_len t0 i = Int.ofNat ∘ List.length := rfl
