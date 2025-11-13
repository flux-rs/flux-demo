import LeanProofs.Lib
import LeanProofs.OpaqueSortDefs

instance : FluxOpaqueSorts where
  VSeq { t0 : Type } [Inhabited t0] := @List t0
