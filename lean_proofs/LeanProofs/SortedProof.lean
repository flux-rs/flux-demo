import LeanProofs.Lib
import LeanProofs.Sorted
import LeanProofs.SharedTheorems

def k0 : Int → SmtMap Int Int → Int → SmtMap Int Int → Int → Prop := fun idx elems len _v_elems _v_len => idx ≥ 0 ∧ (svec_is_sorted <| Adt0.mkadt0_0 elems len)
def k1 : SmtMap Int Int → Int → SmtMap Int Int → Int → Prop := fun _ _ _ _ => True
def k2 : Int → SmtMap Int Int → Int → Prop := fun _res_len _v_elems _v_len => True
def k3 : Int → SmtMap Int Int → Int → Int → SmtMap Int Int → Int → Prop := fun _ _ _ _ _ _ => True

def sorted_proof : sorted := by
  unfold sorted
  exists k0
  exists k1
  exists k2
  exists k3
  intros v _ h_v _ v_len_lb _ h_empty _
  and_intros
  · intros
    and_intros
    · omega
    · grind [svec_is_sorted_eq]
    · trivial
    · trivial
  · intros
    and_intros
    · intros
      simp [svec_is_sorted_eq, k0, *] at *
      grind
    · intros _ in_loop
      and_intros
      · grind [k0]
      · intros ; trivial
      · intros
        and_intros
        · simp [svec_is_sorted_eq, k0, *] at *
          grind
        · intros
          and_intros
          · grind [k0]
          · simp [svec_is_sorted_eq, k0, *] at *
            grind
          · trivial
          · trivial
