import LeanProofs.Instance

def fluxDefsInstance : FluxDefs := inferInstance

def svec_default_elem : {t0 : Type} -> [Inhabited t0] -> t0 := fluxDefsInstance.svec_default_elem
def svec_empty_seq : {t0 : Type} -> [Inhabited t0] -> (SmtMap Int t0) := fluxDefsInstance.svec_empty_seq
def svec_svec_append : {t0 : Type} -> [Inhabited t0] -> ((Adt0 t0) -> ((Adt0 t0) -> (Adt0 t0))) := fluxDefsInstance.svec_svec_append
def svec_svec_slice : {t0 : Type} -> [Inhabited t0] -> ((Adt0 t0) -> (Int -> (Int -> (Adt0 t0)))) := fluxDefsInstance.svec_svec_slice
