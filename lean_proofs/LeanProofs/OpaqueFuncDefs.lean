import LeanProofs.Lib
import LeanProofs.OpaqueSorts
import LeanProofs.Structs
-- OPAQUE DEFS --
class FluxOpaqueFuncs where
  svec_default_elem : {t0 : Type} -> [Inhabited t0] -> t0
  svec_empty_seq : {t0 : Type} -> [Inhabited t0] -> (SmtMap Int t0)
  svec_svec_append : {t0 : Type} -> [Inhabited t0] -> ((Adt0 t0) -> ((Adt0 t0) -> (Adt0 t0)))
  svec_svec_slice : {t0 : Type} -> [Inhabited t0] -> ((Adt0 t0) -> (Int -> (Int -> (Adt0 t0))))
  svec_is_sorted : ((Adt0 Int) -> Prop)
  svec2_vseq_empty : {t0 : Type} -> [Inhabited t0] -> (VSeq t0)
  svec2_vseq_push : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (t0 -> (VSeq t0)))
  svec2_vseq_pop : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (VSeq t0))
  svec2_vseq_get : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> t0))
  svec2_vseq_set : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> (t0 -> (VSeq t0))))
  svec2_vseq_len : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> Int)
  fib_fib : (Int -> Int)
