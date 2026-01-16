import LeanProofs.Flux.Prelude

@[simp]
def svec_empty_seq : {t0 : Type} -> [Inhabited t0] -> (SmtMap Int t0) := fun _ => default
