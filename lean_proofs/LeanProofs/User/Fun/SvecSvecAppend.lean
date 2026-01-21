import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.Flux.Struct.SvecSVec

namespace F

@[simp]
def map_append { t0 : Type } [Inhabited t0] (v1 v2 : SvecSVec t0) := SvecSVec.mkSvecSVec₀ (fun x => if x < 0 then (inferInstance : Inhabited t0).default else if x < v1.len then v1.elems x else if x < v1.len + v2.len then v2.elems (x - v1.len) else (inferInstance : Inhabited t0).default) (v1.len + v2.len)

@[simp]
def svec_svec_append : {t0 : Type} -> [Inhabited t0] -> (SvecSVec t0) -> (SvecSVec t0) -> (SvecSVec t0) := map_append

end F
