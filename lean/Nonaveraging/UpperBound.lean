import Nonaveraging.Structure
import Nonaveraging.MaxSize

/-!
# The upper bound: `h(n) ≤ n^{1/4+o(1)}`

Paper references (arXiv:2410.14624v2, §4):

* **Theorem 2** (`nonaveraging_box_bound`) — a non-averaging subset of a box
  `B ⊆ ℤ^d` satisfies `|A| ≤ |B|^{α_d + o(1)}` where `α_d = (d−1)/(d+1)` for
  `d ≥ 2` and `α₁ = 1/4`.  Proved by the density-increment iteration:
  `irreduciblization` (Lemma 10) + `embedded_in_mu_convex_position`
  (Theorem 4) + `density_increment` (Lemma 1).
* `log_h_div_log_upper` — the `d = 1` case transported to `[n] ⊆ ℤ`.
-/

open Finset MeasureTheory Filter

namespace Nonaveraging

/-- The exponent `α_d` of Theorem 2: `(d−1)/(d+1)` for `d ≥ 2`, `1/4` for
`d = 1`. -/
noncomputable def alphaExp (d : ℕ) : ℝ :=
  if d = 1 then 1 / 4 else ((d : ℝ) - 1) / (d + 1)

/-- **Theorem 2.** For `d ≥ 1` and `ζ > 0`, no non-averaging
`A ⊆ B ⊆ ℤ^d` satisfies `|A| > |B|^{α_d + ζ}` once `|A|` is large enough. -/
theorem nonaveraging_box_bound (d : ℕ) (hd : 1 ≤ d) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ M : ℕ, ∀ (A : Finset (Fin d → ℤ)) (B : GAP.Box d),
      NonAveraging A → A ⊆ B.toFinset → M ≤ A.card →
      (A.card : ℝ) ≤ (B.card : ℝ) ^ (alphaExp d + ζ) := by
  sorry

/-- The `d = 1` consequence: `h n ≤ n^{1/4 + o(1)}` in logarithmic form. -/
theorem log_h_div_log_upper : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, Real.log (h n) / Real.log n ≤ (1 / 4 : ℝ) + ε := by
  sorry

end Nonaveraging
