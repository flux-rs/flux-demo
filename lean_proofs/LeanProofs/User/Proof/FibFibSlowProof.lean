import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibSlow

namespace F

def FibFibSlow_proof : FibFibSlow := by
  unfold FibFibSlow
  intro n₀ h_nonneg
  constructor
  -- Case: !(n₀ ≤ 1), i.e., n₀ > 1
  · intro h_gt1
    have h_gt1' : ¬(n₀ ≤ 1) := by simp_all
    constructor
    -- n₀ - 1 ≥ 0
    · omega
    · intro _
      constructor
      -- n₀ - 2 ≥ 0
      · omega
      -- fib_fib (n₀ - 1) + fib_fib (n₀ - 2) = fib_fib n₀
      · intro _
        conv => rhs; unfold fib_fib
        rw [if_neg h_gt1']
  -- Case: n₀ ≤ 1
  · intro h_le1
    conv => rhs; unfold fib_fib
    rw [if_pos h_le1]

end F
