import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.LemmaSvecAppendGet

namespace F

def LemmaSvecAppendGet_proof : LemmaSvecAppendGet := by
  unfold LemmaSvecAppendGet
  intro v1₀ v2₀ pos₀
  intro h_bounds
  obtain ⟨h_pos_nonneg, h_pos_lt_len⟩ := h_bounds
  intro _h_slice
  intro _h_v2_len_nonneg
  intro h_pos_ge_0
  -- Goal: (svec_svec_append v1₀ v2₀).elems pos₀ =
  --       if pos₀ < v1₀.len then v1₀.elems pos₀ else v2₀.elems (pos₀ - v1₀.len)
  simp only [svec_svec_append, map_append, SmtMap_select]
  -- The append elems function: if x < 0 then default else if x < v1.len then v1.elems x
  --                            else if x < v1.len + v2.len then v2.elems (x - v1.len) else default
  -- Since pos₀ >= 0 (from h_pos_nonneg), the first branch is false
  have h_not_neg : ¬(pos₀ < 0) := by omega
  simp only [h_not_neg, ↓reduceIte]
  -- Now we have: if pos₀ < v1₀.len then v1₀.elems pos₀
  --              else if pos₀ < v1₀.len + v2₀.len then v2₀.elems (pos₀ - v1₀.len) else default
  -- vs goal: if pos₀ < v1₀.len then v1₀.elems pos₀ else v2₀.elems (pos₀ - v1₀.len)
  by_cases h_lt : pos₀ < v1₀.len
  · simp only [h_lt, ↓reduceIte]
  · simp only [h_lt, ↓reduceIte]
    -- pos₀ >= v1₀.len, but pos₀ < v1₀.len + v2₀.len (from h_pos_lt_len)
    simp only [svec_svec_append, map_append] at h_pos_lt_len
    have h_in_v2_range : pos₀ < v1₀.len + v2₀.len := h_pos_lt_len
    simp only [h_in_v2_range, ↓reduceIte]

end F
