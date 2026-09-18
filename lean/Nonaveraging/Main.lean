import Nonaveraging.Asymptotics
import Nonaveraging.UpperBound

/-!
# Headline theorem — JSP-000179

`h(n)`, the largest size of a non-averaging subset of `[n]`, satisfies
`h(n) = n^{1/4 + o(1)}`, i.e. `log h(n) / log n → 1/4`.

Lower bound: `log_h_div_log_lower` (Bosznay's construction).
Upper bound: `log_h_div_log_upper` (Pham–Zakharov, via the CFP structure
theorem, the density-increment lemma, and irreducibility).
-/

open Filter
open scoped Topology

namespace Nonaveraging

/-- **Sharp bound for the Erdős–Straus non-averaging set problem**:
`log h(n) / log n → 1/4`, equivalently `h(n) = n^{1/4+o(1)}`. -/
theorem nonaveraging_max_size_sharp :
    Tendsto (fun n : ℕ ↦ Real.log (h n) / Real.log n) atTop (𝓝 (1 / 4 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (log_h_div_log_lower (ε / 2) (by linarith))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (log_h_div_log_upper (ε / 2) (by linarith))
  exact ⟨max N₁ N₂, fun n hn ↦ by
    have hl := hN₁ n (le_trans (le_max_left _ _) hn)
    have hu := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith⟩

/-- Equivalent `∀ ε ∃ n₀` two-sided squeeze form. -/
theorem nonaveraging_max_size_squeeze : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (n : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ h n ∧ (h n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

end Nonaveraging
