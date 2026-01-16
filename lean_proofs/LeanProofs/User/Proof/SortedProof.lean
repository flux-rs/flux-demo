import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.Flux.VC.Sorted
import LeanProofs.User.SharedTheorems

def k0 : Int → SmtMap Int Int → Int → SmtMap Int Int → Int → Prop := fun idx elems len _v_elems _v_len => idx ≥ 0 ∧ (svec_is_sorted <| SvecSVec.mkSvecSVec₀ elems len)

def Sorted_proof : Sorted := by
  unfold Sorted
  exists k0
  exists SortedKVarSolutions.k1
  unfold k0 SortedKVarSolutions.k1 at *
  intros ; and_intros
  · omega
  · simp
    apply is_sorted_imp_map_vec_is_sorted
    · simp
    · grind [is_sorted]
  · intros i₀ res₀ h1 ; have h1' := h1.right ; and_intros
    · intros ; assumption
    · intros ; and_intros
      · omega
      · intros ; and_intros <;> grind
      · intros ; and_intros
        · assumption
        · intros ; and_intros
          · omega
          · assumption
