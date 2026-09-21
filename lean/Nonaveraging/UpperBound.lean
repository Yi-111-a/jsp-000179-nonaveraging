import Nonaveraging.Structure
import Nonaveraging.Asymptotics
import Nonaveraging.Observation15
import Nonaveraging.Iteration

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

/-- `alphaExp` coincides with `αd` from `Observation15.lean`. -/
theorem alphaExp_eq_αd (d : ℕ) : alphaExp d = αd d := rfl

/-- `α_d ≥ 1/4` for `d ≥ 1` (with equality only at `d = 1`). -/
theorem one_quarter_le_alphaExp {d : ℕ} (hd : 1 ≤ d) :
    (1 / 4 : ℝ) ≤ alphaExp d := by
  rw [alphaExp_eq_αd]
  rcases eq_or_ne d 1 with rfl | h1
  · rw [αd_one]
  · have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
    rw [αd_of_ne_one h1, le_div_iff₀ (by linarith : (0 : ℝ) < (d : ℝ) + 1)]
    linarith

/-- `α_d ≥ 1/3` for `d ≥ 2`. -/
theorem one_third_le_alphaExp {d : ℕ} (hd : 2 ≤ d) :
    (1 / 3 : ℝ) ≤ alphaExp d := by
  rw [alphaExp_eq_αd]
  have h1 : d ≠ 1 := by omega
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [αd_of_ne_one h1, le_div_iff₀ (by linarith : (0 : ℝ) < (d : ℝ) + 1)]
  linarith

/-- `α_d < 1` for `d ≥ 1`. -/
theorem alphaExp_lt_one {d : ℕ} (hd : 1 ≤ d) : alphaExp d < 1 := by
  rw [alphaExp_eq_αd]
  rcases eq_or_ne d 1 with rfl | h1
  · rw [αd_one]; norm_num
  · have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
    rw [αd_of_ne_one h1, div_lt_one (by linarith : (0 : ℝ) < (d : ℝ) + 1)]
    linarith

/-- `α_d` is strictly increasing on `d ≥ 1`. -/
theorem alphaExp_strictMono {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    alphaExp a < alphaExp b := by
  have hb1 : b ≠ 1 := by omega
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 2 ≤ b)
  rw [alphaExp_eq_αd, alphaExp_eq_αd]
  rcases eq_or_ne a 1 with rfl | ha1
  · rw [αd_one, αd_of_ne_one hb1,
      lt_div_iff₀ (by linarith : (0 : ℝ) < (b : ℝ) + 1)]
    linarith
  · have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 2 ≤ a)
    rw [αd_of_ne_one ha1, αd_of_ne_one hb1,
      div_lt_div_iff₀ (by linarith : (0 : ℝ) < (a : ℝ) + 1)
        (by linarith : (0 : ℝ) < (b : ℝ) + 1)]
    suffices (↑a - 1) * (↑b + 1) - (↑b - 1) * (↑a + 1) < (0 : ℝ) by linarith
    have e : (↑a - 1) * (↑b + 1) - (↑b - 1) * (↑a + 1)
        = 2 * ((a : ℝ) - (b : ℝ)) := by ring
    rw [e]
    have h : (a : ℝ) < b := by exact_mod_cast hab
    linarith

/-- Quantitative gap of `alphaExp`: for `1 ≤ d' < d`,
`α_d − α_{d'} ≥ min (1/12) (2/(d(d+1)))`.  (The `1/12` is
`α₂ − α₁ = 1/3 − 1/4`.) -/
theorem alphaExp_sub_gap {d d' : ℕ} (hd' : 1 ≤ d') (hdd : d' < d) :
    min (1 / 12 : ℝ) (2 / ((d : ℝ) * ((d : ℝ) + 1)))
      ≤ alphaExp d - alphaExp d' := by
  rcases eq_or_ne d' 1 with rfl | h1
  · have h3 : (1 / 3 : ℝ) ≤ alphaExp d :=
      one_third_le_alphaExp (by omega : 2 ≤ d)
    rw [show alphaExp 1 = (1 / 4 : ℝ) by rw [alphaExp_eq_αd, αd_one]]
    exact le_trans (min_le_left _ _) (by linarith)
  · have hd2 : 2 ≤ d' := by omega
    have hd3 : 3 ≤ d := by omega
    have hd3r : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
    have hle : alphaExp d' ≤ alphaExp (d - 1) := by
      rcases eq_or_lt_of_le (by omega : d' ≤ d - 1) with h | h
      · rw [h]
      · exact (alphaExp_strictMono (by omega : 1 ≤ d') h).le
    have hdm1 : d - 1 ≠ 1 := by omega
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (show (1:ℕ) ≤ d by omega), Nat.cast_one]
    have hgap : alphaExp d - alphaExp (d - 1)
        = 2 / ((d : ℝ) * ((d : ℝ) + 1)) := by
      have hdne : (d : ℝ) ≠ 0 := by linarith
      have hd1ne : (d : ℝ) + 1 ≠ 0 := by linarith
      rw [alphaExp_eq_αd, alphaExp_eq_αd, αd_of_ne_one (by omega : d ≠ 1),
        αd_of_ne_one hdm1, hcast]
      rw [show (d : ℝ) - 1 + 1 = (d : ℝ) by ring]
      rw [div_sub_div _ _ hd1ne hdne,
        div_eq_div_iff (mul_ne_zero hd1ne hdne) (mul_ne_zero hdne hd1ne)]
      ring
    rw [← hgap]
    exact le_trans (min_le_right _ _) (by linarith)

/-- A nonempty `A ⊆ B` forces `0 < |B|`. -/
theorem GAP.Box.card_pos {ℓ : ℕ} {B : GAP.Box ℓ} {A : Finset (Fin ℓ → ℤ)}
    (hsub : A ⊆ B.toFinset) (hA : A.Nonempty) : 0 < B.card := by
  obtain ⟨a, ha⟩ := hA
  rw [← GAP.Box.card_toFinset]
  exact Finset.card_pos.mpr ⟨a, hsub ha⟩

/-- The counterexample hypothesis `|A| > |B|^{α_d+ζ}` makes `A` a
`(d, β)`-set with `β = 1/(α_d+ζ)` (here `1/(α_d+ζ) ≤ 4`). -/
theorem box_card_lt_of_counterexample {d : ℕ} (hd : 1 ≤ d) {ζ : ℝ} (hζ : 0 < ζ)
    {A : Finset (Fin d → ℤ)} {B : GAP.Box d}
    (hsub : A ⊆ B.toFinset) (hA : A.Nonempty)
    (hcex : (B.card : ℝ) ^ (alphaExp d + ζ) < (A.card : ℝ)) :
    (B.card : ℝ) < (A.card : ℝ) ^ ((alphaExp d + ζ)⁻¹) := by
  have hα : (0 : ℝ) < alphaExp d + ζ :=
    add_pos (lt_of_lt_of_le (by norm_num) (one_quarter_le_alphaExp hd)) hζ
  have hb : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast GAP.Box.card_pos hsub hA
  have hApos : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have key := Real.rpow_lt_rpow (Real.rpow_nonneg hb.le _) hcex
    (inv_pos.mpr hα)
  rwa [← Real.rpow_mul hb.le, mul_inv_cancel₀ hα.ne',
    Real.rpow_one] at key

/-- The *one-step density increment* whose iteration proves Theorem 2
(`nonaveraging_box_bound`): from a non-averaging `A ⊆ B ⊆ ℤ^d` with
`|B|^{α_d + ζ} < |A|` and `α_d + ζ < 1`, produce a derived non-averaging
`A' ⊆ B' ⊆ ℤ^{d'}` (in possibly different dimension `d'`) which is again a
counterexample at the increased slack `ζ + ι`, retaining a polynomial
fraction `|A'| ≥ |A|^q` of the size.

In the paper (arXiv:2410.14624v2, §4) this step is the composite of
`irreduciblization` (Lemma 10), the case split handled numerically by
`Thm2.case_up_pow` / `Thm2.case_down_pow` / `Thm2.case_shrink_pow`, and in
the `d̃ = d`, `ρ > |A|^{-σ}` case of `embedded_in_mu_convex_position`
(Theorem 4), `density_increment` (Lemma 1) and the *discrete John lemma*
(Lemma 6) which converts the convex body `Ω'` back into a `GAP.Box` of
size `O_d(vol Ω')`.

**Why it is not currently derivable.**  The formalized `irreduciblization`
is *vacuous*: its witness constant `ct` is existentially quantified inside
the `∀ A B`, so `ct = (log|A|)⁻¹` and the degenerate witness
`SubSumWitness.degenerate` (with `Â = ∅`, `dt = 0`) satisfy it, yielding no
large embedded image and no usable `|P̃|` bound.  Moreover `SubSumWitness`
alone bounds the new box only by `2^{|A|}` (`DerivedFrom.exists_box`),
whereas the polynomial `|P̃| ≲ |B|`-type bounds needed for the counterexample
propagation require the discrete John lemma (paper Lemmas 6–8), which has
no formalized counterpart. -/
def IterationStepProp (ζ₀ : ℝ) (ι : ℝ) (q : ℝ) (N : ℕ) : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ {ζ : ℝ}, ζ₀ ≤ ζ → alphaExp d + ζ < 1 →
    ∀ {A : Finset (Fin d → ℤ)} {B : GAP.Box d},
      B.IsInterval → NonAveraging A → A ⊆ B.toFinset →
      (B.card : ℝ) ^ (alphaExp d + ζ) < (A.card : ℝ) → N ≤ A.card →
      ∃ (d' : ℕ) (A' : Finset (Fin d' → ℤ)) (B' : GAP.Box d') (ζ' : ℝ),
        1 ≤ d' ∧ B'.IsInterval ∧ NonAveraging A' ∧ A' ⊆ B'.toFinset ∧
        ζ + ι ≤ ζ' ∧
        (B'.card : ℝ) ^ (alphaExp d' + ζ') < (A'.card : ℝ) ∧
        (A.card : ℝ) ^ q ≤ (A'.card : ℝ)

/-- **Theorem 2, modulo the iteration step.**  If `IterationStepProp` holds
at slack `ζ` with a uniform gain `ι > 0`, a size retention `0 < q ≤ 1` and
a threshold `N`, then `nonaveraging_box_bound` holds at `ζ`.

This is the `J = ⌈(1−ζ)/ι⌉` step iteration of §4: the slack grows
`ζ_j ≥ ζ + j·ι` while `|A_j| ≥ |A|^{q^j}` keeps `|A_j| ≥ N` once
`|A| ≥ N^{q^{-J}}`.  If ever `α_{d_j} + ζ_j ≥ 1` — in particular at
`j = J`, where `ζ_J ≥ 1` — the counterexample
`|B_j|^{α_{d_j} + ζ_j} < |A_j| ≤ |B_j|` is already contradictory.
(Note that `α_{d_j} + ζ_j < 1` forces `d_j ≤ 2/ζ`, so the dimensions stay
bounded automatically and a uniform `ι` is available in the real
argument.) -/
theorem nonaveraging_box_bound_of_iterationStep (d : ℕ) (hd : 1 ≤ d)
    {ζ : ℝ} (hζ : 0 < ζ) {ι : ℝ} (hι : 0 < ι) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≤ 1) {N : ℕ} (hN : 1 ≤ N)
    (hstep : IterationStepProp ζ ι q N) :
    ∃ M : ℕ, ∀ (A : Finset (Fin d → ℤ)) (B : GAP.Box d),
      B.IsInterval →
      NonAveraging A → A ⊆ B.toFinset → M ≤ A.card →
      (A.card : ℝ) ≤ (B.card : ℝ) ^ (alphaExp d + ζ) := by
  classical
  -- `J` steps suffice to push the slack past `1`.
  set J : ℕ := ⌈(1 - ζ) / ι⌉₊ with hJdef
  have hJι : (1 : ℝ) - ζ ≤ (J : ℝ) * ι := by
    rw [hJdef]
    have h := Nat.le_ceil ((1 - ζ) / ι)
    rwa [div_le_iff₀ hι] at h
  have hqJ : (0 : ℝ) < q ^ J := pow_pos hq0 J
  have hqJ1 : q ^ J ≤ 1 := pow_le_one₀ hq0.le hq1
  refine ⟨⌈(N : ℝ) ^ (q ^ J)⁻¹⌉₊, ?_⟩
  intro A B hBint hNA hsub hM
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := zero_le_one.trans hN1
  have hMA : (N : ℝ) ^ (q ^ J)⁻¹ ≤ (A.card : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hM)
  have hA1 : (1 : ℝ) ≤ (A.card : ℝ) :=
    (Real.one_le_rpow hN1 (inv_nonneg.mpr hqJ.le)).trans hMA
  -- `N ≤ |A|^{q^j}` for `j ≤ J`: every iterated set stays above `N`.
  have hNqj : ∀ j : ℕ, j ≤ J → (N : ℝ) ≤ (A.card : ℝ) ^ q ^ j := by
    intro j hj
    have hqjJ : q ^ J ≤ q ^ j := pow_le_pow_of_le_one hq0.le hq1 hj
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ = ((N : ℝ) ^ (q ^ J)⁻¹) ^ (q ^ J) := by
          rw [← Real.rpow_mul hN0, inv_mul_cancel₀ hqJ.ne']
      _ ≤ (A.card : ℝ) ^ (q ^ J) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hMA hqJ.le
      _ ≤ (A.card : ℝ) ^ (q ^ j) :=
          Real.rpow_le_rpow_of_exponent_le hA1 hqjJ
  -- A state with `α_{d_j} + ζ_j ≥ 1` is already contradictory.
  have contra_of_ge_one : ∀ {dj : ℕ} {Aj : Finset (Fin dj → ℤ)}
      {Bj : GAP.Box dj} {ζj : ℝ},
      Aj ⊆ Bj.toFinset → (Bj.card : ℝ) ^ (alphaExp dj + ζj) < (Aj.card : ℝ) →
      (N : ℝ) ≤ (Aj.card : ℝ) → 1 ≤ alphaExp dj + ζj → False := by
    intro dj Aj Bj ζj hsubj hcexj hNj h1
    have hAB : (Aj.card : ℝ) ≤ (Bj.card : ℝ) := by
      rw [← GAP.Box.card_toFinset]
      exact_mod_cast Finset.card_le_card hsubj
    have hB1 : (1 : ℝ) ≤ (Bj.card : ℝ) := hN1.trans (hNj.trans hAB)
    have hpow := Real.rpow_le_rpow_of_exponent_le hB1 h1
    rw [Real.rpow_one] at hpow
    linarith
  by_contra hneg
  push_neg at hneg
  -- Iterate: at stage `j` there is a counterexample at slack `≥ ζ + jι`.
  have iter : ∀ j : ℕ, j ≤ J →
      ∃ (dj : ℕ) (Aj : Finset (Fin dj → ℤ)) (Bj : GAP.Box dj) (ζj : ℝ),
        1 ≤ dj ∧ Bj.IsInterval ∧ NonAveraging Aj ∧ Aj ⊆ Bj.toFinset ∧
        (Bj.card : ℝ) ^ (alphaExp dj + ζj) < (Aj.card : ℝ) ∧
        ζ + (j : ℝ) * ι ≤ ζj ∧ (N : ℝ) ≤ (Aj.card : ℝ) ∧
        (A.card : ℝ) ^ q ^ j ≤ (Aj.card : ℝ) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨d, A, B, ζ, hd, hBint, hNA, hsub, ?_, ?_, ?_, ?_⟩
      · -- The initial `A` is a counterexample at `ζ` — shown below from
        -- `by_contra`.
        exact hneg
      · simp
      · calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (N : ℝ) ^ (q ^ J)⁻¹ :=
            Real.rpow_le_rpow_of_exponent_le hN1 ((one_le_inv₀ hqJ).mpr hqJ1)
          _ ≤ (A.card : ℝ) := hMA
      · simp
    | succ j ih =>
      intro hj
      obtain ⟨dj, Aj, Bj, ζj, hdj, hBi, hNAj, hsubj, hcexj, hζj, hNj, hlj⟩ :=
        ih (Nat.le_of_succ_le hj)
      by_cases hαj : alphaExp dj + ζj < 1
      · have hζle : ζ ≤ ζj := by
          have hnonneg : (0 : ℝ) ≤ (j : ℝ) * ι :=
            mul_nonneg (Nat.cast_nonneg _) hι.le
          linarith
        have hNjnat : N ≤ Aj.card := by exact_mod_cast hNj
        obtain ⟨d', A', B', ζ', hd', hBi', hNA', hsub', hζ', hcex', hl'⟩ :=
          hstep hdj hζle hαj hBi hNAj hsubj hcexj hNjnat
        have hbase : (0 : ℝ) ≤ (A.card : ℝ) ^ q ^ j :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hll : (A.card : ℝ) ^ q ^ (j + 1) ≤ (A'.card : ℝ) := by
          calc (A.card : ℝ) ^ q ^ (j + 1)
              = (A.card : ℝ) ^ (q ^ j * q) := by rw [pow_succ]
            _ = ((A.card : ℝ) ^ q ^ j) ^ q :=
                Real.rpow_mul (Nat.cast_nonneg _) _ _
            _ ≤ (Aj.card : ℝ) ^ q := Real.rpow_le_rpow hbase hlj hq0.le
            _ ≤ (A'.card : ℝ) := hl'
        refine ⟨d', A', B', ζ', hd', hBi', hNA', hsub', hcex', ?_, ?_, ?_⟩
        · have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
          rw [hcast]
          have e : ζ + ((j : ℝ) + 1) * ι = ζ + (j : ℝ) * ι + ι := by ring
          rw [e]
          linarith
        · exact (hNqj (j + 1) hj).trans hll
        · exact hll
      · push_neg at hαj
        exact (contra_of_ge_one hsubj hcexj hNj hαj).elim
  obtain ⟨dJ, AJ, BJ, ζJ, hdJ, -, -, hsubJ, hcexJ, hζJ, hNJ, -⟩ :=
    iter J le_rfl
  -- At `j = J` the slack satisfies `ζ_J ≥ 1`, so `α_{d_J} + ζ_J ≥ 1`.
  have hα0 : (0 : ℝ) ≤ alphaExp dJ :=
    (by norm_num : (0 : ℝ) ≤ 1 / 4).trans (one_quarter_le_alphaExp hdJ)
  have h1 : (1 : ℝ) ≤ alphaExp dJ + ζJ := by linarith
  exact contra_of_ge_one hsubJ hcexJ hNJ h1

/-- **Theorem 2.** For `d ≥ 1` and `ζ > 0`, no non-averaging
`A ⊆ B ⊆ ℤ^d` satisfies `|A| > |B|^{α_d + ζ}` once `|A|` is large enough.

**Gap.**  By `nonaveraging_box_bound_of_iterationStep` this reduces to
`IterationStepProp ζ ι q N`, i.e. to the content of §4's iteration step:
`irreduciblization` (Lemma 10) + `embedded_in_mu_convex_position`
(Theorem 4) + `density_increment` (Lemma 1) + the discrete John lemma
(Lemma 6).  The step is not currently derivable because
`irreduciblization`'s statement is vacuously satisfiable (its proof uses
`SubSumWitness.degenerate`, producing `Â = ∅`, `dt = 0`), the `|P̃|` bounds
need Lemmas 6–8 (`SubSumWitness` alone gives only `2^{|A|}`, cf.
`DerivedFrom.exists_box`), and the `d̃ = d` non-shrink case additionally
needs a convex-body-to-box conversion (discrete John) that is absent. -/
theorem nonaveraging_box_bound (d : ℕ) (hd : 1 ≤ d) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ M : ℕ, ∀ (A : Finset (Fin d → ℤ)) (B : GAP.Box d),
      B.IsInterval →
      NonAveraging A → A ⊆ B.toFinset → M ≤ A.card →
      (A.card : ℝ) ≤ (B.card : ℝ) ^ (alphaExp d + ζ) := by
  sorry

/-- The `d = 1` consequence: `h n ≤ n^{1/4 + o(1)}` in logarithmic form. -/
theorem log_h_div_log_upper : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, Real.log (h n) / Real.log n ≤ (1 / 4 : ℝ) + ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := nonaveraging_box_bound 1 le_rfl (half_pos hε)
  have hMev : ∀ᶠ n : ℕ in atTop, M ≤ h n := by
    filter_upwards [tendsto_sqrt_sqrt_atTop.eventually_ge_atTop (M + 1)]
      with n hn
    exact le_trans (Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn))
      (h_ge_sqrt_sqrt_sub_one n)
  filter_upwards [hMev, eventually_ge_atTop 2] with n hMn hn2
  classical
  obtain ⟨A, hAsub, hANA, hAcard⟩ := exists_nonAveraging_card_eq n
  let e : ℤ →+ (Fin 1 → ℤ) :=
    { toFun := fun x _ ↦ x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have he_inj : Function.Injective e := fun _ _ h ↦ congrFun h 0
  set A' := A.image e with hA'def
  have hANA' : NonAveraging A' := hANA.image e he_inj
  have hcard' : A'.card = h n := by
    rw [hA'def, Finset.card_image_of_injective _ he_inj, hAcard]
  let B : GAP.Box 1 := fun _ ↦ Finset.Icc 1 (n : ℤ)
  have hBint : B.IsInterval := fun i ↦ ⟨1, (n : ℤ), rfl⟩
  have hAsub' : A' ⊆ B.toFinset := by
    intro x hx
    rw [hA'def, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [GAP.Box.toFinset, Fintype.mem_piFinset]
    intro i
    exact hAsub hy
  have hBcard : B.card = n := by
    have h1 : B.card = (Finset.Icc 1 (n : ℤ)).card := Fin.prod_univ_one _
    rw [h1, Int.card_Icc]
    simp
  have hbox := hM A' B hBint hANA' hAsub' (by rw [hcard']; exact hMn)
  rw [hcard', hBcard] at hbox
  have hα : alphaExp 1 = 1 / 4 := by unfold alphaExp; norm_num
  rw [hα] at hbox
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
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
  have hln : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast hn2 : (1 : ℝ) < n)
  have hlog : Real.log (h n) ≤ (1 / 4 + ε / 2) * Real.log n := by
    have h1 := (Real.log_le_log_iff hpos
      (Real.rpow_pos_of_pos hn0 _)).mpr hbox
    rwa [Real.log_rpow hn0] at h1
  calc Real.log (h n) / Real.log n ≤ 1 / 4 + ε / 2 :=
        (div_le_iff₀ hln).mpr hlog
    _ ≤ 1 / 4 + ε := by linarith

end Nonaveraging
