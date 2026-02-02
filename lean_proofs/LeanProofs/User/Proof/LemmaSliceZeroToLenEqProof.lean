import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSliceZeroToLenEq

namespace F

def LemmaSliceZeroToLenEq_proof : LemmaSliceZeroToLenEq := by
  unfold LemmaSliceZeroToLenEq
  intro v₀
  intro h_self_slice
  intro h_len_nonneg
  -- Goal: svec_svec_slice v₀ 0 v₀.len = v₀
  -- The hypothesis h_self_slice says:
  --   slice (mkSvecSVec₀ v₀.elems v₀.len) 0 v₀.len = mkSvecSVec₀ v₀.elems v₀.len
  -- Note that mkSvecSVec₀ v₀.elems v₀.len = v₀ by eta
  have h_eta : SvecSVec.mkSvecSVec₀ v₀.elems v₀.len = v₀ := by
    cases v₀
    rfl
  rw [← h_eta]
  exact h_self_slice

end F
