import LeanProofs.Lib
import LeanProofs.OpaqueSorts
import LeanProofs.Structs
import LeanProofs.OpaqueFuncs
-- FUNC DECLS --
mutual
def is_sorted_parts (a0 : (SmtMap Int Int)) (a1 : Int) : Prop :=
  (svec_is_sorted (Adt0.mkadt0_0 a0 a1))

end
