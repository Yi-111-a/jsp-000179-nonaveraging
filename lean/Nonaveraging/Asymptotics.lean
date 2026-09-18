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
  intro ε hε
  -- Eventually `n^{1/4-ε} ≤ n^{1/4} - 2`: the gap `n^{1/4} - n^{1/4-ε}` grows.
  have key : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) - 2 := by
    rcases le_total ε (1 / 4 : ℝ) with hε4 | hε4
    swap
    · filter_upwards
        [((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
            tendsto_natCast_atTop_atTop).eventually_ge_atTop 3,
         eventually_ge_atTop 1] with n h3 hn1
      simp only [Function.comp_apply] at h3
      have hnn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      calc (n : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ (n : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hnn (by linarith)
        _ = 1 := Real.rpow_zero _
        _ ≤ (n : ℝ) ^ ((1 : ℝ) / 4) - 2 := by linarith
    · filter_upwards
        [((tendsto_rpow_atTop hε).comp
            tendsto_natCast_atTop_atTop).eventually_ge_atTop 3,
         eventually_gt_atTop 0] with n h3 hn0
      simp only [Function.comp_apply] at h3
      have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
      have hδ : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) := Real.rpow_nonneg hn0'.le _
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) :=
        Real.one_le_rpow (by exact_mod_cast hn0) (by linarith)
      have hrw : (n : ℝ) ^ ((1 : ℝ) / 4)
          = (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * (n : ℝ) ^ (ε : ℝ) := by
        rw [← Real.rpow_add hn0']
        congr 1
        ring
      rw [hrw]
      have hm : 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 4 - ε) * ((n : ℝ) ^ (ε : ℝ) - 1) := by
        have := mul_le_mul h1 (show (2 : ℝ) ≤ (n : ℝ) ^ (ε : ℝ) - 1 by linarith)
          (by norm_num) hδ
        linarith
      rw [mul_sub, mul_one] at hm
      linarith
  filter_upwards [key, tendsto_sqrt_sqrt_atTop.eventually_ge_atTop 2,
    eventually_ge_atTop 2] with n hkey hq2 hn2
  have hlt : (n : ℝ) < ((n.sqrt.sqrt + 1 : ℕ) : ℝ) ^ 4 := by
    exact_mod_cast n_lt_quartic_succ n
  have e : (((n.sqrt.sqrt + 1 : ℕ) : ℝ) ^ 4) ^ ((1 : ℝ) / 4)
      = ((n.sqrt.sqrt + 1 : ℕ) : ℝ) := by
    rw [show (1 : ℝ) / 4 = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  have hrp : (n : ℝ) ^ ((1 : ℝ) / 4) ≤ ((n.sqrt.sqrt + 1 : ℕ) : ℝ) := by
    rw [← e]
    exact ((Real.rpow_lt_rpow_iff (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 1 / 4)).mpr hlt).le
  have hnat : n.sqrt.sqrt - 1 ≤ h n := h_ge_sqrt_sqrt_sub_one n
  have hqcast : ((n.sqrt.sqrt - 1 : ℕ) : ℝ) = (n.sqrt.sqrt : ℝ) - 1 := by
    rw [Nat.cast_sub (le_trans (by norm_num : (1 : ℕ) ≤ 2) hq2), Nat.cast_one]
  have hge : ((n.sqrt.sqrt - 1 : ℕ) : ℝ) ≤ (h n : ℝ) := by exact_mod_cast hnat
  rw [hqcast] at hge
  have hh : (n : ℝ) ^ ((1 : ℝ) / 4) - 2 ≤ (h n : ℝ) := by
    push_cast at hrp
    linarith
  have hh' : (n : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ (h n : ℝ) := le_trans hkey hh
  have hpos : (0 : ℝ) < (h n : ℝ) := by
    have : (1 : ℕ) ≤ h n := le_trans (Nat.sub_le_sub_right hq2 1) hnat
    exact_mod_cast this
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
  have hlog : ((1 : ℝ) / 4 - ε) * Real.log n ≤ Real.log (h n) := by
    have h1 := (Real.log_le_log_iff (Real.rpow_pos_of_pos hn0 _) hpos).mpr hh'
    rwa [Real.log_rpow hn0] at h1
  exact (le_div_iff₀
    (Real.log_pos (by exact_mod_cast hn2 : (1 : ℝ) < n))).mpr hlog

end Nonaveraging
