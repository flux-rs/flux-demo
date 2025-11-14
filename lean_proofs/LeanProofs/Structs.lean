import LeanProofs.Lib
import LeanProofs.OpaqueSorts
-- STRUCT DECLS --
mutual
@[ext]
structure Adt0 (t0 : Type) [Inhabited t0] where
  mkadt0_0::
  (fld0_0 : (SmtMap Int t0))
  (fld0_1 : Int)

end
