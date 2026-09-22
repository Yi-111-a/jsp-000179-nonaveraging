import Nonaveraging.Defs

open Finset Asymptotics Filter

namespace Nonaveraging

theorem cor_bits (ℓ : ℕ) (c : ℝ) (hc : 0 < c) (C₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ m : ℝ, C ≤ m →
        16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
          (2 * (c / Real.log 2) + 1) ^ (2 * ℓ) < m) := by
  have hC₀pos : (0 : ℝ) < 16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
      (2 * (c / Real.log 2) + 1) ^ (2 * ℓ) + 1 := by
    have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨max C₁ (16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
      (2 * (c / Real.log 2) + 1) ^ (2 * ℓ) + 1),
    lt_of_lt_of_le hC₀pos (le_max_right _ _), fun m hCm ↦ ?_⟩
  exact lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one)
    (le_trans (le_max_right _ _) hCm)

end Nonaveraging
