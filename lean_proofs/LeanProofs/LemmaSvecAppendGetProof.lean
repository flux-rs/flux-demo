import LeanProofs.Lib
import LeanProofs.LemmaSvecAppendGet
import LeanProofs.LemmaSvecAppendLenProof
import LeanProofs.SharedTheorems

theorem svec_append_len_simp (v1 v2 : Adt0 Int) (h1 : v2.fld0_1 ≥ 0) (h2 : svec_svec_slice v2 0 v2.fld0_1 = v2): (svec_svec_append v1 v2).fld0_1 = v1.fld0_1 + v2.fld0_1 := by
  apply lemma_svec_append_len_proof
  repeat (exact 0 ; assumption)

def lemma_svec_append_get_proof : lemma_svec_append_get := by
  unfold lemma_svec_append_get
  intros v1 v2 pos _ pos_in_bounds _ v2_len_nonneg _ h_v2 _ pos_nonneg
  rw [svec_append_eq] ; unfold map_append SmtMap_select
  rw [svec_append_len_simp] at pos_in_bounds
  simp [pos_in_bounds]
  · intros ; exfalso ; omega
  · assumption
  · assumption
