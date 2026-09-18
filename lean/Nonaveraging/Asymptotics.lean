import Nonaveraging.Bosznay

/-!
# Asymptotic glue for the lower bound

From `h_ge_sqrt_sqrt_sub_one` (`h n ≥ ⌊√⌊√n⌋⌋ − 1`) we derive the
`liminf ≥ 1/4` half of the sharp theorem, in the `∀ ε`-eventually form.
-/

open Finset Filter Real

namespace Nonaveraging

/-- `q(n) = ⌊√⌊√n⌋⌋` tends to infinity. -/
theorem tendsto_sqrt_sqrt_atTop : Tendsto (fun n : ℕ ↦ n.sqrt.sqrt) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  exact ⟨M ^ 4, fun n hn ↦ by
    rw [Nat.le_sqrt, Nat.le_sqrt]
    calc M * M * (M * M) = M ^ 4 := by ring
      _ ≤ n := hn⟩

/-- `n < (q(n) + 1)⁴`: the next quartic overshoots `n`. -/
theorem n_lt_quartic_succ (n : ℕ) : n < (n.sqrt.sqrt + 1) ^ 4 := by
  have h1 : n.sqrt < (n.sqrt.sqrt + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.lt_succ_sqrt _
  have h2 : n < (n.sqrt + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.lt_succ_sqrt _
  have h3 : n.sqrt + 1 ≤ (n.sqrt.sqrt + 1) ^ 2 := h1
  calc n < (n.sqrt + 1) ^ 2 := h2
    _ ≤ ((n.sqrt.sqrt + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h3 _
    _ = (n.sqrt.sqrt + 1) ^ 4 := by ring

/-- `log(h n)/log n ≥ 1/4 − ε` eventually: the lower bound assembled from
Bosznay's construction. -/
theorem log_h_div_log_lower : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, (1 / 4 : ℝ) - ε ≤ Real.log (h n) / Real.log n := by
  sorry

end Nonaveraging
