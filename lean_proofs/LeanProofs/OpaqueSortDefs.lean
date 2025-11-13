import LeanProofs.Lib
-- FLUX OPAQUE SORT DEFS --
class FluxOpaqueSorts where
  VSeq (t0 : Type) [Inhabited t0] : Type
