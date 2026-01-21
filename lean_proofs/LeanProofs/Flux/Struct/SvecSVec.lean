import LeanProofs.Flux.Prelude

namespace F

@[ext]
structure SvecSVec (t0 : Type) [Inhabited t0] where
  mkSvecSVec₀ ::
    elems : (SmtMap Int t0) 
    len : Int 


end F
