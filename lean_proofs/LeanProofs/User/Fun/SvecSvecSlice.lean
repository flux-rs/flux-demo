import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SvecSVec
import LeanProofs.Flux.Struct.SvecSVec

@[simp]
def map_slice { t0 : Type } [Inhabited t0] (v1 : SvecSVec t0) (left right : Int) := SvecSVec.mkSvecSVec₀ (fun x => if 0 <= x ∧ x < (right - left) then v1.elems (x + left) else default) (if right - left < 0 then 0 else right - left)

@[simp]
def svec_svec_slice : {t0 : Type} -> [Inhabited t0] -> (SvecSVec t0) -> Int -> Int -> (SvecSVec t0) := map_slice
