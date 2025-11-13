import LeanProofs.OpaqueSortsInstance

def fluxOpaqueSorts : FluxOpaqueSorts := inferInstance

def VSeq := fluxOpaqueSorts.VSeq
