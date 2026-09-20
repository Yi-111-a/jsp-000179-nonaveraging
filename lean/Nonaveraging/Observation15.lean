import Mathlib

set_option linter.unusedSimpArgs false

/-!
# Observation 15 of Pham–Zakharov (arXiv:2410.14624v2, §4)

A purely numerical lemma used in the Case-1 density increment of Theorem 2:
for `ζ ∈ (0,1)` there is `c(ζ) > 0` such that for all naturals `dh > d ≥ 1`
and all `0 ≤ ε ≤ 0.01·ζ`,

  `(αd dh + ζ) * (1/(αd d + ζ) - (1 - ε)·(dh - d)) ≤ 1 - c(ζ)`,

where `αd 1 = 1/4` and `αd d = (d-1)/(d+1)` for `d ≥ 2`.

Proof outline.  Write `a = αd dh`, `b = αd d`, `k = dh - d`.  For `ε ≤ 0.01ζ`
one has the algebraic bound

  `(a+ζ)(1/(b+ζ) - (1-ε)k) ≤ 1 - F/(b+ζ)`,
  `F = k(a+ζ)(b+ζ)(1 - 0.01ζ) - (a-b)`

(`obs15_aux`).  For `d ≥ 7`, `1/(b+ζ) ≤ 4/3` and `k ≥ 1` give
`LHS ≤ (1+ζ)(1/3 + 0.01ζ) < 1`.  For `d ≤ 6`, if the bracket is nonpositive
then `LHS ≤ 0`; otherwise `(1-ε)k < 1/b`, and since `1-ε ≥ 0.99`,
`b ≥ 1/3` gives `k ≤ 3` (for `d ≥ 2`) and `b = 1/4` gives `k ≤ 4` (for
`d = 1`).  The remaining finitely many pairs `(d, dh)` are checked by
`interval_cases` + `nlinarith`: in every case `F ≥ ζ/20`
(`obs15_case`).  Taking `c = min (1 - (1+ζ)(1/3+0.01ζ)) (ζ/20) / 2`
works.
-/

namespace Nonaveraging

/-- The coefficient `α_d` used in Observation 15 of arXiv:2410.14624. -/
noncomputable def αd (d : ℕ) : ℝ :=
  if d = 1 then 1 / 4 else ((d : ℝ) - 1) / ((d : ℝ) + 1)

lemma αd_one : αd 1 = 1 / 4 := ite_eq_left rfl

lemma αd_of_ne_one {d : ℕ} (h : d ≠ 1) : αd d = ((d : ℝ) - 1) / ((d : ℝ) + 1) :=
  ite_eq_right h

/-- Algebraic bound: for `ε ≤ 0.01 ζ`, the product is at most
`1 - F / (b + ζ)` where `F = k (a+ζ) (b+ζ) (1 - 0.01 ζ) - (a - b)`.
Equality up to the nonnegative defect `k (a+ζ) (b+ζ) (0.01 ζ - ε)`. -/
private lemma obs15_aux {a b k ζ ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hk : 0 ≤ k)
    (hζ : 0 < ζ) (hε : ε ≤ 0.01 * ζ) :
    (a + ζ) * (1 / (b + ζ) - (1 - ε) * k)
      ≤ 1 - (k * (a + ζ) * (b + ζ) * (1 - 0.01 * ζ) - (a - b)) / (b + ζ) := by
  have hbζ : 0 < b + ζ := by linarith
  have hbζ' : b + ζ ≠ 0 := hbζ.ne'
  have haζ : 0 ≤ a + ζ := by linarith
  have hε' : (0 : ℝ) ≤ 0.01 * ζ - ε := by linarith
  have hdiff : (0 : ℝ) ≤ k * (a + ζ) * (b + ζ) * (0.01 * ζ - ε) :=
    mul_nonneg (mul_nonneg (mul_nonneg hk haζ) hbζ.le) hε'
  have h2 : (1 - (a + ζ) * (1 / (b + ζ) - (1 - ε) * k)) * (b + ζ)
      = k * (a + ζ) * (b + ζ) * (1 - 0.01 * ζ) - (a - b)
        + k * (a + ζ) * (b + ζ) * (0.01 * ζ - ε) := by
    field_simp
    ring
  have h3 : (k * (a + ζ) * (b + ζ) * (1 - 0.01 * ζ) - (a - b)) / (b + ζ)
      ≤ 1 - (a + ζ) * (1 / (b + ζ) - (1 - ε) * k) := by
    rw [div_le_iff₀ hbζ]
    linarith [h2, hdiff]
  linarith [h3]

/-- A single finite case: for concrete `0 < b ≤ 1`, `0 ≤ a`, `0 ≤ k`
with `F ≥ ζ/20`, the product is at most `1 - min C0 (ζ/20) / 2`. -/
private lemma obs15_case {ζ ε a b k C0 : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ < 1) (hC0 : 0 < C0)
    (hb : 0 < b) (hb1 : b ≤ 1) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hε : ε ≤ 0.01 * ζ)
    (hF : ζ / 20 ≤ k * (a + ζ) * (b + ζ) * (1 - 0.01 * ζ) - (a - b)) :
    (a + ζ) * (1 / (b + ζ) - (1 - ε) * k) ≤ 1 - min C0 (ζ / 20) / 2 := by
  have hbζ : 0 < b + ζ := by linarith
  have hbound := obs15_aux ha hb hk hζ hε
  have hbζ2 : b + ζ ≤ 2 := by linarith
  have hmin : min C0 (ζ / 20) ≤ ζ / 20 := min_le_right _ _
  have hc : (0 : ℝ) ≤ min C0 (ζ / 20) / 2 := by
    have hm : (0 : ℝ) < min C0 (ζ / 20) := lt_min hC0 (by linarith)
    linarith
  have hfin : min C0 (ζ / 20) / 2
      ≤ (k * (a + ζ) * (b + ζ) * (1 - 0.01 * ζ) - (a - b)) / (b + ζ) := by
    rw [le_div_iff₀ hbζ]
    have h1 : min C0 (ζ / 20) / 2 * (b + ζ) ≤ min C0 (ζ / 20) / 2 * 2 :=
      mul_le_mul_of_nonneg_left hbζ2 hc
    have h2 : min C0 (ζ / 20) / 2 * 2 = min C0 (ζ / 20) := by ring
    linarith [h1, h2]
  linarith [hbound, hfin]

set_option maxHeartbeats 1600000 in
/-- **Observation 15** of Pham–Zakharov: for `ζ ∈ (0,1)` there exists
`c > 0` (here `c = min (1 - (1+ζ)(1/3 + 0.01ζ)) (ζ/20) / 2`) such that for all
naturals `dh > d ≥ 1` and `0 ≤ ε ≤ 0.01 ζ`,
`(αd dh + ζ) * (1/(αd d + ζ) - (1-ε)(dh - d)) ≤ 1 - c`. -/
theorem observation15 {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ dh d : ℕ, 1 ≤ d → d < dh → ∀ ε : ℝ, 0 ≤ ε →
      ε ≤ (0.01 : ℝ) * ζ →
      (αd dh + ζ) * (1 / (αd d + ζ) - (1 - ε) * ((dh : ℝ) - (d : ℝ))) ≤ 1 - c := by
  set C0 : ℝ := 1 - (1 + ζ) * (1 / 3 + 0.01 * ζ) with hC0def
  have hC0 : 0 < C0 := by
    have h1 : (0 : ℝ) < ζ * (1 - ζ) := mul_pos hζ (by linarith)
    nlinarith [hC0def, h1]
  have hmpos : (0 : ℝ) < min C0 (ζ / 20) := lt_min hC0 (by linarith)
  refine ⟨min C0 (ζ / 20) / 2, by linarith, ?_⟩
  intro dh d hd hdd ε hε hε2
  have hα1 : αd 1 = (1 / 4 : ℝ) := αd_one
  have hα2 : αd 2 = (1 / 3 : ℝ) := by norm_num [αd]
  have hα3 : αd 3 = (1 / 2 : ℝ) := by norm_num [αd]
  have hα4 : αd 4 = (3 / 5 : ℝ) := by norm_num [αd]
  have hα5 : αd 5 = (2 / 3 : ℝ) := by norm_num [αd]
  have hα6 : αd 6 = (5 / 7 : ℝ) := by norm_num [αd]
  have hα7 : αd 7 = (3 / 4 : ℝ) := by norm_num [αd]
  have hα8 : αd 8 = (7 / 9 : ℝ) := by norm_num [αd]
  have hα9 : αd 9 = (4 / 5 : ℝ) := by norm_num [αd]
  have hdh2 : 2 ≤ dh := by omega
  have hdh1 : dh ≠ 1 := by omega
  have hdhr : (2 : ℝ) ≤ (dh : ℝ) := by exact_mod_cast hdh2
  have ha : αd dh = ((dh : ℝ) - 1) / ((dh : ℝ) + 1) := αd_of_ne_one hdh1
  have ha0 : (0 : ℝ) ≤ αd dh := by
    rw [ha]
    exact div_nonneg (by linarith) (by linarith)
  have ha1 : αd dh ≤ 1 := by
    rw [ha, div_le_iff₀ (by linarith : (0 : ℝ) < (dh : ℝ) + 1)]
    linarith
  have hk1 : (1 : ℝ) ≤ (dh : ℝ) - (d : ℝ) := by
    have h : (d : ℝ) + 1 ≤ (dh : ℝ) := by exact_mod_cast hdd
    linarith
  have hε1 : (0 : ℝ) ≤ 1 - ε := by linarith
  have hε99 : (0.99 : ℝ) ≤ 1 - ε := by linarith
  have hζm : (0 : ℝ) ≤ 1 - ζ := by linarith
  have hζ2' : (0 : ℝ) ≤ ζ * (1 - ζ) := mul_nonneg hζ.le hζm
  have hζ3' : (0 : ℝ) ≤ ζ * ζ * (1 - ζ) := mul_nonneg (mul_nonneg hζ.le hζ.le) hζm
  by_cases hd7 : 7 ≤ d
  · -- `d ≥ 7`: uniform bound `LHS ≤ (1+ζ)(1/3 + 0.01ζ) = 1 - C0`.
    have hd1' : d ≠ 1 := by omega
    have hbd : αd d = ((d : ℝ) - 1) / ((d : ℝ) + 1) := αd_of_ne_one hd1'
    have hd' : (7 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd7
    have hbpos : (0 : ℝ) < ((d : ℝ) - 1) / ((d : ℝ) + 1) :=
      div_pos (by linarith) (by linarith)
    have hbinv1 : 1 / (((d : ℝ) - 1) / ((d : ℝ) + 1) + ζ)
        < 1 / (((d : ℝ) - 1) / ((d : ℝ) + 1)) :=
      one_div_lt_one_div_of_lt hbpos (by linarith)
    have hbinv2 : 1 / (((d : ℝ) - 1) / ((d : ℝ) + 1)) = ((d : ℝ) + 1) / ((d : ℝ) - 1) := by
      field_simp
    have hbinv3 : ((d : ℝ) + 1) / ((d : ℝ) - 1) ≤ 4 / 3 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (d : ℝ) - 1)]
      linarith
    have hbinv : 1 / (αd d + ζ) ≤ 4 / 3 := by
      rw [hbd]
      linarith [hbinv1, hbinv2, hbinv3]
    have hB : 1 / (αd d + ζ) - (1 - ε) * ((dh : ℝ) - (d : ℝ)) ≤ 1 / 3 + ε := by
      have hge : (1 - ε) * 1 ≤ (1 - ε) * ((dh : ℝ) - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hk1 hε1
      linarith [hbinv]
    have h1 : (αd dh + ζ) * (1 / (αd d + ζ) - (1 - ε) * ((dh : ℝ) - (d : ℝ)))
        ≤ (αd dh + ζ) * (1 / 3 + ε) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have h2 : (αd dh + ζ) * (1 / 3 + ε) ≤ (1 + ζ) * (1 / 3 + ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h3 : (1 + ζ) * (1 / 3 + ε) ≤ (1 + ζ) * (1 / 3 + 0.01 * ζ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h4 : (1 + ζ) * (1 / 3 + 0.01 * ζ) ≤ 1 - min C0 (ζ / 20) / 2 := by
      have hminC : min C0 (ζ / 20) ≤ C0 := min_le_left _ _
      linarith [hC0def]
    linarith [h1, h2, h3, h4]
  · push Not at hd7
    -- `d ≤ 6`.
    have hαd_pos : 0 < αd d := by
      by_cases h1 : d = 1
      · subst h1
        rw [hα1]
        norm_num
      · have hd2 : 2 ≤ d := by omega
        have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
        rw [αd_of_ne_one h1]
        exact div_pos (by linarith) (by linarith)
    have hbζ : 0 < αd d + ζ := by linarith
    by_cases hB : 1 / (αd d + ζ) - (1 - ε) * ((dh : ℝ) - (d : ℝ)) ≤ 0
    · -- Negative bracket: `LHS ≤ 0 ≤ 1 - c`.
      have h1 : (αd dh + ζ) * (1 / (αd d + ζ) - (1 - ε) * ((dh : ℝ) - (d : ℝ))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hB
      have hc1 : min C0 (ζ / 20) / 2 ≤ 1 := by
        have : min C0 (ζ / 20) ≤ ζ / 20 := min_le_right _ _
        linarith
      linarith
    · push Not at hB
      -- Positive bracket bounds `k = dh - d`: `(1-ε)·k < 1/(αd d)`.
      have hkinv : (1 - ε) * ((dh : ℝ) - (d : ℝ)) < 1 / (αd d + ζ) := by linarith
      have hinv : 1 / (αd d + ζ) < 1 / αd d :=
        one_div_lt_one_div_of_lt hαd_pos (by linarith)
      have hk99 : (0.99 : ℝ) * ((dh : ℝ) - (d : ℝ)) < 1 / αd d := by
        have h1 : (0.99 : ℝ) * ((dh : ℝ) - (d : ℝ))
            ≤ (1 - ε) * ((dh : ℝ) - (d : ℝ)) :=
          mul_le_mul_of_nonneg_right hε99 (by linarith)
        linarith
      by_cases hd1 : d = 1
      · subst hd1
        rw [hα1] at hk99
        norm_num at hk99
        have hk5 : dh ≤ 5 := by
          have h1 : (dh : ℝ) < 5.1 := by linarith [hk99]
          have h2 : dh < 6 := by exact_mod_cast (show (dh : ℝ) < 6 by linarith [h1])
          omega
        interval_cases dh <;>
          (simp only [hα1, hα2, hα3, hα4, hα5, hα6, hα7, hα8, hα9]
           refine obs15_case hζ hζ1 hC0 (by norm_num) (by norm_num) (by norm_num)
             (by norm_num) hε2 ?_
           nlinarith [hζ2', hζ3', sq_nonneg ζ, mul_nonneg hζ.le hζ.le])
      · have hd2 : 2 ≤ d := by omega
        have hbd : αd d = ((d : ℝ) - 1) / ((d : ℝ) + 1) := αd_of_ne_one hd1
        have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
        have hb3 : (1 / 3 : ℝ) ≤ αd d := by
          rw [hbd, le_div_iff₀ (by linarith : (0 : ℝ) < (d : ℝ) + 1)]
          linarith
        have hb13 : (1 : ℝ) / αd d ≤ 3 := by
          rw [div_le_iff₀ hαd_pos]
          linarith
        have hk3 : dh ≤ d + 3 := by
          have h1 : (dh : ℝ) - (d : ℝ) < 3.1 := by linarith [hk99, hb13]
          have h2 : (dh : ℝ) < (d : ℝ) + 4 := by linarith
          have h3 : dh < d + 4 := by exact_mod_cast h2
          omega
        interval_cases d <;>
          (have hbound9 : dh ≤ 9 := by omega
           interval_cases dh <;>
             first
             | omega
             | (simp only [hα1, hα2, hα3, hα4, hα5, hα6, hα7, hα8, hα9]
                refine obs15_case hζ hζ1 hC0 (by norm_num) (by norm_num) (by norm_num)
                  (by norm_num) hε2 ?_
                nlinarith [hζ2', hζ3', sq_nonneg ζ, mul_nonneg hζ.le hζ.le]))

end Nonaveraging
