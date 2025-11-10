import LeanProofs.Lib
-- STRUCT DECLS --
mutual
@[ext]
structure Adt0 (t0 : Type) [Inhabited t0] where
  mkadt0_0::
  (fld0_0 : (SmtMap Int t0))
  (fld0_1 : Int)

end
-- OPAQUE DEFS --
class FluxDefs where
  svec_default_elem : {t0 : Type} -> [Inhabited t0] -> t0
  svec_empty_seq : {t0 : Type} -> [Inhabited t0] -> (SmtMap Int t0)
  svec_svec_append : {t0 : Type} -> [Inhabited t0] -> ((Adt0 t0) -> ((Adt0 t0) -> (Adt0 t0)))
  svec_svec_slice : {t0 : Type} -> [Inhabited t0] -> ((Adt0 t0) -> (Int -> (Int -> (Adt0 t0))))
