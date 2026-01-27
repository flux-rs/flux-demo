import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibFibFast

namespace F

def FibFibFast_proof : FibFibFast := by
  unfold FibFibFast
  -- Provide the loop invariant: prev = fib(i-1), curr = fib(i), 2 ≤ i ≤ n
  refine ⟨fun i prev curr n => prev = fib_fib (i - 1) ∧ curr = fib_fib i ∧ 2 ≤ i ∧ i ≤ n, ?_⟩
  intro n₀ h_nonneg
  constructor
  -- Case: n₀ > 1
  · intro h_gt1
    have h_gt1' : ¬(n₀ ≤ 1) := by simp_all
    constructor
    -- Initial state: k0 2 1 2 n₀
    · constructor
      -- prev = fib_fib(2-1) = fib_fib(1) = 1
      · conv => rhs; rw [fib_fib]
        simp
      constructor
      -- curr = fib_fib(2) = 2
      · conv => rhs; rw [fib_fib]
        simp [fib_fib]
      constructor
      -- 2 ≤ 2
      · omega
      -- 2 ≤ n₀
      · omega
    -- Loop body
    · intro i₀ prev₀ curr₀ h_inv
      obtain ⟨h_prev, h_curr, h_i_ge2, h_i_le_n⟩ := h_inv
      constructor
      -- Case: i₀ ≥ n₀ (loop exits)
      · intro h_exit
        have h_eq : i₀ = n₀ := by
          simp_all
          omega
        rw [h_eq] at h_curr
        exact h_curr
      -- Case: i₀ < n₀ (loop continues)
      · intro h_continue
        have h_continue' : i₀ < n₀ := by simp_all
        constructor
        -- new_prev = curr₀ = fib_fib(i₀) = fib_fib((i₀+1)-1)
        · have h1 : i₀ + 1 - 1 = i₀ := by omega
          rw [h1, h_curr]
        constructor
        -- new_curr = prev₀ + curr₀ = fib_fib(i₀-1) + fib_fib(i₀) = fib_fib(i₀+1)
        · have hi : ¬(i₀ + 1 ≤ 1) := by omega
          have h2 : i₀ + 1 - 1 = i₀ := by omega
          have h3 : i₀ + 1 - 2 = i₀ - 1 := by omega
          conv => rhs; rw [fib_fib]
          rw [if_neg hi, h2, h3, h_prev, h_curr]
          rw [Int.add_comm]
        constructor
        -- 2 ≤ i₀ + 1
        · omega
        -- i₀ + 1 ≤ n₀
        · omega
  -- Case: n₀ ≤ 1
  · intro h_le1
    conv => rhs; rw [fib_fib]
    rw [if_pos h_le1]

end F
