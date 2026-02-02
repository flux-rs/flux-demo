import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSvecAppendLen

namespace F

def LemmaSvecAppendLen_proof : LemmaSvecAppendLen := by
  unfold LemmaSvecAppendLen
  intro v1₀ v2₀
  intro _h_slice
  intro _h_len_nonneg
  -- Goal: (svec_svec_append v1₀ v2₀).len = v1₀.len + v2₀.len
  -- By definition of svec_svec_append/map_append, the len field is v1.len + v2.len
  simp only [svec_svec_append, map_append]

end F
