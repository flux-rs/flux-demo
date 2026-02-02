import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Svec2LemmaPopPushEq

namespace F

def Svec2LemmaPopPushEq_proof : Svec2LemmaPopPushEq := by
  unfold Svec2LemmaPopPushEq
  intro elems₀ len₀ e₀
  intro h_len_eq
  intro h_len_nonneg
  -- svec2_vseq_get (svec2_vseq_push elems₀ e₀) len₀ = e₀
  -- push prepends: e₀ :: elems₀
  -- get at position len₀: (e₀ :: elems₀).getD ((len₀ + 1) - len₀ - 1).natAbs default
  --                     = (e₀ :: elems₀).getD 0 default = e₀
  simp only [svec2_vseq_get, svec2_vseq_push, flip, svec2_vseq_len] at *
  simp only [List.length_cons]
  -- (e₀ :: elems₀).getD (↑(elems₀.length + 1) - len₀ - 1).natAbs default = e₀
  -- Since h_len_eq : ↑elems₀.length = len₀
  rw [← h_len_eq]
  -- (e₀ :: elems₀).getD (↑(elems₀.length + 1) - ↑elems₀.length - 1).natAbs default = e₀
  -- Simplify: (len + 1) - len - 1 = 0
  have h_idx : (↑(elems₀.length + 1) - ↑elems₀.length - 1 : Int).natAbs = 0 := by omega
  rw [h_idx]
  simp only [List.getD_cons_zero]

end F
