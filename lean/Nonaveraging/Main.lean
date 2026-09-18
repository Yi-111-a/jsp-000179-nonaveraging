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
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (log_h_div_log_lower ε hε)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (log_h_div_log_upper ε hε)
  refine ⟨max (max N₁ N₂) 2, fun n hn ↦ ?_⟩
  have hm : max N₁ N₂ ≤ n := le_trans (le_max_left _ _) hn
  have hN₁' := hN₁ n (le_trans (le_max_left _ _) hm)
  have hN₂' := hN₂ n (le_trans (le_max_right _ _) hm)
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hn2
  have hn0 : (0 : ℝ) < n := hn1.trans' (by norm_num)
  have hln : 0 < Real.log n := Real.log_pos hn1
  have hpos : (0 : ℝ) < (h n : ℝ) := by
    have hs : ({(1 : ℤ)} : Finset ℤ) ⊆ Finset.Icc 1 (n : ℤ) := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_Icc.mpr ⟨le_refl 1,
        by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hn2⟩
    have hc := card_le_h hs (nonAveraging_singleton (1 : ℤ))
    rw [Finset.card_singleton] at hc
    exact_mod_cast hc
  have hlo : (1 / 4 - ε) * Real.log n ≤ Real.log (h n) :=
    (le_div_iff₀ hln).mp hN₁'
  have hhi : Real.log (h n) ≤ (1 / 4 + ε) * Real.log n :=
    (div_le_iff₀ hln).mp hN₂'
  refine ⟨?_, ?_⟩
  · have hlog1 : Real.log ((n : ℝ) ^ ((1 : ℝ) / 4 - ε)) ≤ Real.log (h n) := by
      rw [Real.log_rpow hn0]
      exact hlo
    exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hn0 _) hpos).mp hlog1
  · have hlog2 : Real.log (h n) ≤ Real.log ((n : ℝ) ^ ((1 : ℝ) / 4 + ε)) := by
      rw [Real.log_rpow hn0]
      exact hhi
    exact (Real.log_le_log_iff hpos (Real.rpow_pos_of_pos hn0 _)).mp hlog2

end Nonaveraging
