def BitVec_shiftLeft { n : Nat } (x s : BitVec n) : BitVec n := BitVec.shiftLeft x (s.toNat)
def BitVec_ushiftRight { n : Nat } (x s : BitVec n) : BitVec n := BitVec.ushiftRight x (s.toNat)
def BitVec_sshiftRight { n : Nat } (x s : BitVec n) : BitVec n := BitVec.sshiftRight x (s.toNat)
def BitVec_uge { n : Nat } (x y : BitVec n) := (BitVec.ult x y).not
def BitVec_sge { n : Nat } (x y : BitVec n) := (BitVec.slt x y).not
def BitVec_ugt { n : Nat } (x y : BitVec n) := (BitVec.ule x y).not
def BitVec_sgt { n : Nat } (x y : BitVec n) := (BitVec.sle x y).not
def SmtMap (Key Val : Type) [Inhabited Key] [BEq Key] [Inhabited Val] : Type := Key -> Val
def SmtMap_default { Key Val: Type } (v : Val) [Inhabited Key] [BEq Key] [Inhabited Val] : SmtMap Key Val := fun _ => v
def SmtMap_store { Key Val : Type } [Inhabited Key] [BEq Key] [Inhabited Val] (m : SmtMap Key Val) (k : Key) (v : Val) : SmtMap Key Val :=
  fun x => if x == k then v else m x
def SmtMap_select { Key Val : Type } [Inhabited Key] [BEq Key] [Inhabited Val] (m : SmtMap Key Val) (k : Key) := m k
