import LeanProofs.OpaqueFuncsInstance

def fluxOpaqueFuncs : FluxOpaqueFuncs := inferInstance

def svec_default_elem : {t0 : Type} -> [Inhabited t0] -> t0 := fluxOpaqueFuncs.svec_default_elem
def svec_empty_seq : {t0 : Type} -> [Inhabited t0] -> (SmtMap Int t0) := fluxOpaqueFuncs.svec_empty_seq
def svec_svec_append : {t0 : Type} -> [Inhabited t0] -> ((Adt0 t0) -> ((Adt0 t0) -> (Adt0 t0))) := fluxOpaqueFuncs.svec_svec_append
def svec_svec_slice : {t0 : Type} -> [Inhabited t0] -> ((Adt0 t0) -> (Int -> (Int -> (Adt0 t0)))) := fluxOpaqueFuncs.svec_svec_slice
def svec2_vseq_empty : {t0 : Type} -> [Inhabited t0] -> (VSeq t0) := fluxOpaqueFuncs.svec2_vseq_empty
def svec2_vseq_push : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (t0 -> (VSeq t0))) := fluxOpaqueFuncs.svec2_vseq_push
def svec2_vseq_pop : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (VSeq t0)) := fluxOpaqueFuncs.svec2_vseq_pop
def svec2_vseq_get : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> t0)) := fluxOpaqueFuncs.svec2_vseq_get
def svec2_vseq_set : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> (t0 -> (VSeq t0)))) := fluxOpaqueFuncs.svec2_vseq_set
def svec2_vseq_len : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> Int) := fluxOpaqueFuncs.svec2_vseq_len
def fib_fib : (Int -> Int) := fluxOpaqueFuncs.fib_fib
