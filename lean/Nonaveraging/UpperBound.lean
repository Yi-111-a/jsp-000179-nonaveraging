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

/-- **Bookkeeping-enriched §4 step property** — the form of the §4
step the paper's closing iteration paragraph (arXiv:2410.14624v2, §4)
actually uses.  As in `Thm2.StepProp`, every large counterexample
`A ⊆ B` at slack `ζ` produces a derived counterexample `A' ⊆ B'` at
slack `≥ ζ + min ι (θ |A|)` with `|A'| ≤ |A|`, `|A|^q ≤ |A'|` and a
retention factor `ρ` (`ρ·|A| ≤ |A'|`).  The two extra fields are
exactly the data tracked in the paper's final bookkeeping:

* `d' ≠ d → ζ + ι ≤ ζ'` — steps that *change* the ambient dimension
  (the paper's `d̃ > d` and `d̃ < d` cases) gain a *uniform* increment
  (the paper's `θ(ζ,d)`, i.e. `min` of the Observation-15 gain
  `c(ζ)` and the gap `α_d − α_{d̃} − ε`, both bounded below uniformly
  on `ζ ∈ [ζ₀, 1)`).  Hence at most `⌈(1−ζ)/ι⌉` dimension changes can
  occur before the slack reaches `1`.
* `d' = d → |B'| ≤ ρ^κ·|B|` — steps that keep the dimension come from
  the `d̃ = d` case, where the new box satisfies
  `|B̃| ≪ η·ρ^K·|B|` (`η ≤ 1`, `K ≥ 100`; `ρ ≤ μ^{c(d)}` absorbs the
  constant into `κ = K/2` for large `|A|`).  Since `|B_j| ≥ 1`
  throughout, telescoping `|B_j|` bounds `∏ ρ_j` over these steps by
  `|A|^{-O(1/κ)}`. -/
def StepPropB (ζ₀ : ℝ) (ι q κ : ℝ) (θ : ℝ → ℝ) (N : ℕ) : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ {ζ : ℝ}, ζ₀ ≤ ζ → alphaExp d + ζ < 1 →
    ∀ {A : Finset (Fin d → ℤ)} {B : GAP.Box d},
      B.IsInterval → NonAveraging A → A ⊆ B.toFinset →
      (B.card : ℝ) ^ (alphaExp d + ζ) < (A.card : ℝ) → N ≤ A.card →
      ∃ (d' : ℕ) (A' : Finset (Fin d' → ℤ)) (B' : GAP.Box d') (ζ' ρ : ℝ),
        1 ≤ d' ∧ B'.IsInterval ∧ NonAveraging A' ∧ A' ⊆ B'.toFinset ∧
        A'.card ≤ A.card ∧ (A.card : ℝ) ^ q ≤ (A'.card : ℝ) ∧
        ρ * (A.card : ℝ) ≤ (A'.card : ℝ) ∧ 0 < ρ ∧ ρ ≤ 1 ∧
        ζ + min ι (θ (A.card : ℝ)) ≤ ζ' ∧
        (B'.card : ℝ) ^ (alphaExp d' + ζ') < (A'.card : ℝ) ∧
        (d' ≠ d → ζ + ι ≤ ζ') ∧
        (d' = d → (B'.card : ℝ) ≤ ρ ^ κ * (B.card : ℝ))

/-- **Finite-iteration bookkeeping**: iterating the §4 step
`StepPropB` gives Theorem 2.

Why the enrichment over `Thm2.StepProp` is *needed*: the step's
per-instance increment `min ι (θ |A_j|)` with `θ x = ι / log x`
antitone means the uniform `J = ⌈(1−ζ)/ι⌉` count of
`nonaveraging_box_bound_of_iterationStep` does not apply, and the bare
polynomial retention `|A_j| ≥ |A|^{q^j}` collapses to `|A|^{o(1)}`
after the `≍ log |A|` steps the `1/log`-scale increments force.  The
paper's actual argument (§4, final paragraph): dimension-changing
steps are `O_{ζ,d}(1)` many (uniform increment), and same-dimension
steps satisfy `|B_{j+1}| ≲ ρ_j^K|B_j|`, so the box sizes telescope
against `|B_j| ≥ 1` to give `∏ ρ_j ≥ |A|^{-o(1)}` — hence
`|A_j| ≥ |A|^{1-c}` throughout.

With `U = ⌈(1−ζ)/ι⌉` bounding the number of dimension changes and
`κ` the box-shrinkage exponent, the tracked invariant is

  `|A_j| ≥ |A|^{1+(q−1)D_j}·P_j`,  `P_j^κ ≥ |B_j|·|A|^{−4(D_j+1)}`

(`D_j` the number of dimension changes so far, `P_j` the product of
the `ρ` over same-dimension steps), which yields
`|A_j| ≥ |A|^{1−(1−q)U−4(U+1)/κ} ≥ |A|^{1/2} ≥ N` under the stated
parameter constraint.  Meanwhile each step gains
`≥ τ := min ι (θ|A|)`, so after `J = ⌈(1−ζ)/τ⌉` stages the slack
exceeds `1` and `|A_J| ≤ |B_J|` contradicts the counterexample. -/
theorem nonaveraging_box_bound_of_step (d : ℕ) (hd : 1 ≤ d) {ζ : ℝ}
    (hζ : 0 < ζ)
    (hstep : ∃ (ι q κ : ℝ) (θ : ℝ → ℝ) (N : ℕ),
      0 < ι ∧ 0 < q ∧ q ≤ 1 ∧ 0 < κ ∧ 2 ≤ N ∧
      (∀ x : ℝ, 2 ≤ x → 0 < θ x) ∧ AntitoneOn θ (Set.Ici (2 : ℝ)) ∧
      (1 - q) * (⌈(1 - ζ) / ι⌉₊ : ℝ) + 4 * ((⌈(1 - ζ) / ι⌉₊ : ℝ) + 1) / κ
        ≤ 1 / 2 ∧
      StepPropB ζ ι q κ θ N) :
    ∃ M : ℕ, ∀ (A : Finset (Fin d → ℤ)) (B : GAP.Box d),
      B.IsInterval →
      NonAveraging A → A ⊆ B.toFinset → M ≤ A.card →
      (A.card : ℝ) ≤ (B.card : ℝ) ^ (alphaExp d + ζ) := by
  classical
  obtain ⟨ι, q, κ, θ, N, hι, hq0, hq1, hκ, hN, hθpos, hθanti, hnum,
    hstepB⟩ := hstep
  refine ⟨N ^ 2, ?_⟩
  intro A B hBint hNA hsub hM
  have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hNa : (N : ℝ) ^ 2 ≤ (A.card : ℝ) := by
    have h : ((N ^ 2 : ℕ) : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hM
    rwa [Nat.cast_pow] at h
  have ha2 : (2 : ℝ) ≤ (A.card : ℝ) := by nlinarith
  have ha1 : (1 : ℝ) ≤ (A.card : ℝ) := by linarith
  have ha0 : (0 : ℝ) < (A.card : ℝ) := by linarith
  set τ : ℝ := min ι (θ (A.card : ℝ)) with hτ_def
  have hτ : 0 < τ := lt_min hι (hθpos _ ha2)
  set J : ℕ := ⌈(1 - ζ) / τ⌉₊ with hJ_def
  have hJτ : (1 : ℝ) - ζ ≤ (J : ℝ) * τ := by
    rw [hJ_def]
    have h := Nat.le_ceil ((1 - ζ) / τ)
    rwa [div_le_iff₀ hτ] at h
  set U : ℕ := ⌈(1 - ζ) / ι⌉₊ with hU_def
  have hUge : (1 - ζ) / ι ≤ (U : ℝ) := by rw [hU_def]; exact Nat.le_ceil _
  -- A counterexample `|B'|^{α'+ζ'} < |A'|` with `ζ' ≥ ζ` and
  -- `|A'| ≤ |A|` has `|B'| ≤ |A|⁴` (as `α' + ζ' ≥ 1/4`).
  have hbox4 : ∀ {dj : ℕ} (hdj : 1 ≤ dj) {Aj : Finset (Fin dj → ℤ)}
      {Bj : GAP.Box dj} {ζj : ℝ}, ζ ≤ ζj →
      (Bj.card : ℝ) ^ (alphaExp dj + ζj) < (Aj.card : ℝ) →
      (1 : ℝ) ≤ (Aj.card : ℝ) → (Aj.card : ℝ) ≤ (A.card : ℝ) →
      (Bj.card : ℝ) ≤ (A.card : ℝ) ^ (4 : ℝ) := by
    intro dj hdj Aj Bj ζj hζj hcexj hAj1 hAja
    have hαq : (1 / 4 : ℝ) ≤ alphaExp dj + ζj :=
      (one_quarter_le_alphaExp hdj).trans (by linarith)
    have he : (0 : ℝ) < alphaExp dj + ζj := by linarith
    have hAjpos : 0 < Aj.card := by exact_mod_cast hAj1
    have h1 := (Thm2.card_lt_rpow_of_rpow_lt he hAjpos hcexj).le
    have hinv : (alphaExp dj + ζj)⁻¹ ≤ 4 := by
      calc (alphaExp dj + ζj)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ :=
            inv_anti₀ (by norm_num) hαq
        _ = 4 := by norm_num
    calc (Bj.card : ℝ) ≤ (Aj.card : ℝ) ^ (alphaExp dj + ζj)⁻¹ := h1
      _ ≤ (Aj.card : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hAj1 hinv
      _ ≤ (A.card : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hAja (by norm_num)
  -- The tracked lower bound `|A_j| ≥ |A|^{1+(q−1)D_j}·P_j` with
  -- `P_j^κ ≥ |B_j|·|A|^{-4(D_j+1)}` and `D_j ≤ U` gives `|A_j| ≥ N`.
  have size_lb : ∀ {dj : ℕ} {Aj : Finset (Fin dj → ℤ)} {Bj : GAP.Box dj}
      {Dj : ℕ} {Pj : ℝ}, Dj ≤ U →
      Aj ⊆ Bj.toFinset →
      (A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) * Pj ≤ (Aj.card : ℝ) →
      (0 : ℝ) < Pj →
      (Bj.card : ℝ) * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1))) ≤ Pj ^ κ →
      (N : ℝ) ≤ (Aj.card : ℝ) := by
    intro dj Aj Bj Dj Pj hDU hsubj hsz hP0 hPB
    have hAjpos : (0 : ℝ) < (Aj.card : ℝ) :=
      lt_of_lt_of_le
        (mul_pos (Real.rpow_pos_of_pos ha0 _) hP0) hsz
    have hAj1 : (1 : ℝ) ≤ (Aj.card : ℝ) := by
      exact_mod_cast Nat.cast_pos.mp hAjpos
    have hAB : (Aj.card : ℝ) ≤ (Bj.card : ℝ) := by
      rw [← GAP.Box.card_toFinset]
      exact_mod_cast Finset.card_le_card hsubj
    have hB1 : (1 : ℝ) ≤ (Bj.card : ℝ) := hAj1.trans hAB
    -- `P_j^κ ≥ |A|^{-4(D_j+1)}` hence `P_j ≥ |A|^{-4(D_j+1)/κ}`.
    have hPow : (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1))) ≤ Pj ^ κ :=
      calc (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1)))
          = 1 * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1))) := (one_mul _).symm
        _ ≤ (Bj.card : ℝ) * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_right hB1
              (Real.rpow_nonneg ha0.le _)
        _ ≤ Pj ^ κ := hPB
    have hPge : (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1)) / κ) ≤ Pj := by
      have hκ' : (0 : ℝ) < κ⁻¹ := inv_pos.mpr hκ
      have step1 := Real.rpow_le_rpow
        (Real.rpow_nonneg ha0.le _) hPow hκ'.le
      rwa [← Real.rpow_mul ha0.le, ← Real.rpow_mul hP0.le,
        mul_inv_cancel₀ hκ.ne', Real.rpow_one] at step1
    -- the exponent is `≥ 1/2` by the parameter constraint
    have hDc : (Dj : ℝ) ≤ (U : ℝ) := by exact_mod_cast hDU
    have hexp : (1 : ℝ) / 2 ≤
        1 + (q - 1) * (Dj : ℝ) + -(4 * ((Dj : ℝ) + 1)) / κ := by
      have h1q : (0 : ℝ) ≤ 1 - q := by linarith
      have hDl : (1 - q) * (Dj : ℝ) ≤ (1 - q) * (U : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ h1q; exact hDc
      have hDr : 4 * ((Dj : ℝ) + 1) / κ ≤ 4 * ((U : ℝ) + 1) / κ :=
        (div_le_div_iff_of_pos_right hκ).mpr (by linarith)
      linarith [hnum]
    have hNsq : (N : ℝ) = ((N : ℝ) ^ 2) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_mul hN0]
      norm_num
    calc (N : ℝ) = ((N : ℝ) ^ 2) ^ (1 / 2 : ℝ) := hNsq
      _ ≤ (A.card : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (sq_nonneg _) hNa (by norm_num)
      _ ≤ (A.card : ℝ)
            ^ (1 + (q - 1) * (Dj : ℝ) + -(4 * ((Dj : ℝ) + 1)) / κ) :=
          Real.rpow_le_rpow_of_exponent_le ha1 hexp
      _ = (A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) *
            (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1)) / κ) :=
          (Real.rpow_add ha0 _ _)
      _ ≤ (A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) * Pj :=
          mul_le_mul_of_nonneg_left hPge (Real.rpow_nonneg ha0.le _)
      _ ≤ (Aj.card : ℝ) := hsz
  -- A state with `α_{d_j} + ζ_j ≥ 1` is already contradictory.
  have contra_of_ge_one : ∀ {dj : ℕ} {Aj : Finset (Fin dj → ℤ)}
      {Bj : GAP.Box dj} {ζj : ℝ},
      Aj ⊆ Bj.toFinset →
      (Bj.card : ℝ) ^ (alphaExp dj + ζj) < (Aj.card : ℝ) →
      (N : ℝ) ≤ (Aj.card : ℝ) → 1 ≤ alphaExp dj + ζj → False := by
    intro dj Aj Bj ζj hsubj hcexj hNj h1
    have hAB : (Aj.card : ℝ) ≤ (Bj.card : ℝ) := by
      rw [← GAP.Box.card_toFinset]
      exact_mod_cast Finset.card_le_card hsubj
    have hB1 : (1 : ℝ) ≤ (Bj.card : ℝ) := hN1r.trans (hNj.trans hAB)
    have hpow := Real.rpow_le_rpow_of_exponent_le hB1 h1
    rw [Real.rpow_one] at hpow
    linarith
  by_contra hneg
  push_neg at hneg
  -- Iterate the step.  The state at stage `j` additionally tracks the
  -- dimension-change count `Dj` and the same-dimension `ρ`-product `Pj`.
  have iter : ∀ j : ℕ, j ≤ J →
      ∃ (dj : ℕ) (Aj : Finset (Fin dj → ℤ)) (Bj : GAP.Box dj) (ζj : ℝ)
        (Dj : ℕ) (Pj : ℝ),
        1 ≤ dj ∧ Bj.IsInterval ∧ NonAveraging Aj ∧ Aj ⊆ Bj.toFinset ∧
        (Bj.card : ℝ) ^ (alphaExp dj + ζj) < (Aj.card : ℝ) ∧
        ζ + (j : ℝ) * τ ≤ ζj ∧ ζ + (Dj : ℝ) * ι ≤ ζj ∧
        (Aj.card : ℝ) ≤ (A.card : ℝ) ∧ (N : ℝ) ≤ (Aj.card : ℝ) ∧
        (A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) * Pj ≤ (Aj.card : ℝ) ∧
        0 < Pj ∧ Pj ≤ 1 ∧
        (Bj.card : ℝ) * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1)))
          ≤ Pj ^ κ := by
    intro j
    induction j with
    | zero =>
      intro _
      have hB4 : (B.card : ℝ) ≤ (A.card : ℝ) ^ (4 : ℝ) :=
        hbox4 hd le_rfl hneg ha1 le_rfl
      refine ⟨d, A, B, ζ, 0, 1, hd, hBint, hNA, hsub, hneg, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · exact le_refl _
      · exact hN1r.trans (by nlinarith [hNa])
      · -- `|A|^{1+(q−1)·0}·1 = |A|`
        simp [Real.rpow_one]
      · norm_num
      · norm_num
      · -- `|B|·|A|^{-4} ≤ 1^κ = 1` from `|B| ≤ |A|⁴`
        rw [Real.one_rpow]
        have h4 : (4 : ℝ) = 4 * ((0 : ℝ) + 1) := by norm_num
        rw [show (-(4 * ((0 : ℕ) + 1 : ℝ))) = (-4 : ℝ) by norm_num,
          Real.rpow_neg ha0.le, ← div_eq_mul_inv,
          div_le_one (Real.rpow_pos_of_pos ha0 _)]
        simpa using hB4
    | succ j ih =>
      intro hj
      obtain ⟨dj, Aj, Bj, ζj, Dj, Pj, hdj, hBi, hNAj, hsubj, hcexj, hτj,
        hDjι, hAle, hNj, hsz, hP0, hP1, hPB⟩ := ih (Nat.le_of_succ_le hj)
      by_cases hαj : alphaExp dj + ζj < 1
      · -- running: `ζj < 1` bounds `Dj < U`; apply the step.
        have hζj1 : ζj < 1 := by
          have h14 := one_quarter_le_alphaExp hdj
          linarith
        have hDjU : Dj < U := by
          have h1 : (Dj : ℝ) * ι < 1 - ζ := by linarith
          have h2 : (Dj : ℝ) < (1 - ζ) / ι := (lt_div_iff₀ hι).mpr h1
          exact_mod_cast h2.trans_le hUge
        have hζle : ζ ≤ ζj := by
          have hnn : (0 : ℝ) ≤ (j : ℝ) * τ :=
            mul_nonneg (Nat.cast_nonneg _) hτ.le
          linarith
        have hNjnat : N ≤ Aj.card := by exact_mod_cast hNj
        obtain ⟨d', A', B', ζ', ρ, hd', hBi', hNA', hsub', hAle', hqA',
          hρA', hρ0, hρ1, hζ', hcex', hunif, hbox⟩ :=
          hstepB hdj hζle hαj hBi hNAj hsubj hcexj hNjnat
        have hAj2 : (2 : ℝ) ≤ (Aj.card : ℝ) := hN2r.trans hNj
        have hθge : θ (A.card : ℝ) ≤ θ (Aj.card : ℝ) :=
          hθanti (Set.mem_Ici.mpr hAj2) (Set.mem_Ici.mpr ha2) hAle
        have hincr : τ ≤ min ι (θ (Aj.card : ℝ)) := by
          rw [hτ_def]
          exact le_min (min_le_left _ _) ((min_le_right _ _).trans hθge)
        have hζ'st : ζj + τ ≤ ζ' := by
          linarith [hincr]
        have hζjle' : ζj ≤ ζ' := by linarith
        have hτj' : ζ + ((j : ℝ) + 1) * τ ≤ ζ' := by
          have e : ζ + ((j : ℝ) + 1) * τ = ζ + (j : ℝ) * τ + τ := by ring
          rw [e]; linarith
        have hAle'' : (A'.card : ℝ) ≤ (A.card : ℝ) :=
          le_trans (by exact_mod_cast hAle') hAle
        have hA'pos : (0 : ℝ) < (A'.card : ℝ) :=
          lt_of_lt_of_le (mul_pos hρ0 (by linarith)) hρA'
        have hA'1 : (1 : ℝ) ≤ (A'.card : ℝ) := by
          exact_mod_cast Nat.cast_pos.mp hA'pos
        have hζle' : ζ ≤ ζ' := hζle.trans hζjle'
        have hcastj : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        by_cases hdd : d' = dj
        · -- same dimension: keep `Dj`, multiply `Pj` by `ρ`.
          have hbox' := hbox hdd
          have hBpos : (0 : ℝ) < (Bj.card : ℝ) := by
            have hAB : (Aj.card : ℝ) ≤ (Bj.card : ℝ) := by
              rw [← GAP.Box.card_toFinset]
              exact_mod_cast Finset.card_le_card hsubj
            linarith
          have hρκ : (B'.card : ℝ) / (Bj.card : ℝ) ≤ ρ ^ κ :=
            (div_le_iff₀ hBpos).mpr hbox'
          refine ⟨d', A', B', ζ', Dj, Pj * ρ, hd', hBi', hNA', hsub',
            hcex', ?_, ?_, hAle'', ?_, ?_, ?_, ?_, ?_⟩
          · rw [hcastj]; exact hτj'
          · linarith
          · exact size_lb (Nat.le_of_lt hDjU) hsub' (by
              calc (A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) * (Pj * ρ)
                  = ρ * ((A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) * Pj) :=
                    by ring
                _ ≤ ρ * (Aj.card : ℝ) :=
                    mul_le_mul_of_nonneg_left hsz hρ0.le
                _ ≤ (A'.card : ℝ) := hρA') (mul_pos hP0 hρ0) (by
              calc (B'.card : ℝ)
                    * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1)))
                  = (Bj.card : ℝ)
                      * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1)))
                      * ((B'.card : ℝ) / (Bj.card : ℝ)) := by
                    field_simp
                _ ≤ Pj ^ κ * ρ ^ κ :=
                    mul_le_mul hPB hρκ (div_nonneg (Nat.cast_nonneg _)
                      hBpos.le) (Real.rpow_nonneg hP0.le _)
                _ = (Pj * ρ) ^ κ :=
                    (Real.mul_rpow hP0.le hρ0.le).symm)
          · calc (A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) * (Pj * ρ)
                = ρ * ((A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) * Pj) :=
                  by ring
              _ ≤ ρ * (Aj.card : ℝ) :=
                  mul_le_mul_of_nonneg_left hsz hρ0.le
              _ ≤ (A'.card : ℝ) := hρA'
          · exact mul_pos hP0 hρ0
          · calc Pj * ρ ≤ 1 * ρ :=
                mul_le_mul_of_nonneg_right hP1 hρ0.le
              _ = ρ := one_mul _
              _ ≤ 1 := hρ1
          · calc (B'.card : ℝ)
                  * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1)))
                = (Bj.card : ℝ)
                    * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1)))
                    * ((B'.card : ℝ) / (Bj.card : ℝ)) := by
                  field_simp
              _ ≤ Pj ^ κ * ρ ^ κ :=
                  mul_le_mul hPB hρκ (div_nonneg (Nat.cast_nonneg _)
                    hBpos.le) (Real.rpow_nonneg hP0.le _)
              _ = (Pj * ρ) ^ κ := (Real.mul_rpow hP0.le hρ0.le).symm
        · -- dimension change: `Dj ↦ Dj+1`, keep `Pj`, uniform `ι` gain.
          have hbox4' : (B'.card : ℝ) ≤ (A.card : ℝ) ^ (4 : ℝ) :=
            hbox4 hd' hζle' hcex' hA'1 hAle''
          have hcastD : ((Dj + 1 : ℕ) : ℝ) = (Dj : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
          have hBj1 : (1 : ℝ) ≤ (Bj.card : ℝ) := by
            have hAB : (Aj.card : ℝ) ≤ (Bj.card : ℝ) := by
              rw [← GAP.Box.card_toFinset]
              exact_mod_cast Finset.card_le_card hsubj
            exact hN1r.trans (hNj.trans hAB)
          have hPowj : (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1))) ≤ Pj ^ κ :=
            calc (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1)))
                = 1 * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1))) :=
                  (one_mul _).symm
              _ ≤ (Bj.card : ℝ)
                    * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1))) :=
                  mul_le_mul_of_nonneg_right hBj1
                    (Real.rpow_nonneg ha0.le _)
              _ ≤ Pj ^ κ := hPB
          refine ⟨d', A', B', ζ', Dj + 1, Pj, hd', hBi', hNA', hsub',
            hcex', ?_, ?_, hAle'', ?_, ?_, hP0, hP1, ?_⟩
          · rw [hcastj]; exact hτj'
          · -- `ζ + (Dj+1)·ι ≤ ζ'` from the uniform increment
            have hu := hunif hdd
            rw [hcastD]
            have e : ζ + ((Dj : ℝ) + 1) * ι = ζ + (Dj : ℝ) * ι + ι := by
              ring
            rw [e]; linarith
          · -- `N ≤ |A'|` via `size_lb` at `Dj+1 ≤ U`
            apply size_lb (Nat.succ_le_of_lt hDjU) hsub' _ hP0 _
            · -- `|A|^{1+(q−1)(Dj+1)}·Pj ≤ |A_j|^q ≤ |A'|`
              have hPq : Pj ≤ Pj ^ q := by
                rw [← Real.rpow_one Pj]
                exact Real.rpow_le_rpow_of_exponent_ge hP0 hP1 hq1
              have hexp : 1 + (q - 1) * ((Dj : ℝ) + 1)
                  ≤ q * (1 + (q - 1) * (Dj : ℝ)) := by
                nlinarith [mul_nonneg (sq_nonneg (q - 1))
                  (Nat.cast_nonneg Dj : (0:ℝ) ≤ (Dj:ℝ))]
              calc (A.card : ℝ) ^ (1 + (q - 1) * ((Dj : ℝ) + 1)) * Pj
                  ≤ (A.card : ℝ)
                      ^ (q * (1 + (q - 1) * (Dj : ℝ))) * Pj :=
                    mul_le_mul_of_nonneg_right
                      (Real.rpow_le_rpow_of_exponent_le ha1 hexp) hP0.le
                _ ≤ (A.card : ℝ)
                      ^ (q * (1 + (q - 1) * (Dj : ℝ))) * Pj ^ q :=
                    mul_le_mul_of_nonneg_left hPq
                      (Real.rpow_nonneg ha0.le _)
                _ = ((A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ))) ^ q
                      * Pj ^ q := by
                    rw [← Real.rpow_mul ha0.le]; ring_nf
                _ = ((A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) * Pj) ^ q :=
                    (Real.mul_rpow (Real.rpow_nonneg ha0.le _)
                      hP0.le).symm
                _ ≤ (Aj.card : ℝ) ^ q :=
                    Real.rpow_le_rpow
                      (mul_nonneg (Real.rpow_nonneg ha0.le _) hP0.le)
                      hsz hq0.le
                _ ≤ (A'.card : ℝ) := hqA'
            · -- `(B'.card)·|A|^{-4(Dj+2)} ≤ Pj^κ` from `|B'| ≤ |A|⁴`
              rw [hcastD]
              calc (B'.card : ℝ)
                    * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1 + 1)))
                  ≤ (A.card : ℝ) ^ (4 : ℝ)
                      * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1 + 1))) :=
                    mul_le_mul_of_nonneg_right hbox4'
                      (Real.rpow_nonneg ha0.le _)
                _ = (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1))) := by
                    rw [← Real.rpow_add ha0]; congr 1; ring
                _ ≤ Pj ^ κ := hPowj
          · -- `|A|^{1+(q−1)(Dj+1)}·Pj ≤ |A'|` (same as above)
            have hPq : Pj ≤ Pj ^ q := by
              rw [← Real.rpow_one Pj]
              exact Real.rpow_le_rpow_of_exponent_ge hP0 hP1 hq1
            have hexp : 1 + (q - 1) * ((Dj : ℝ) + 1)
                ≤ q * (1 + (q - 1) * (Dj : ℝ)) := by
              nlinarith [mul_nonneg (sq_nonneg (q - 1))
                (Nat.cast_nonneg Dj : (0:ℝ) ≤ (Dj:ℝ))]
            calc (A.card : ℝ) ^ (1 + (q - 1) * ((Dj + 1 : ℕ) : ℝ)) * Pj
                = (A.card : ℝ) ^ (1 + (q - 1) * ((Dj : ℝ) + 1)) * Pj := by
                  rw [hcastD]
              _ ≤ (A.card : ℝ)
                    ^ (q * (1 + (q - 1) * (Dj : ℝ))) * Pj :=
                  mul_le_mul_of_nonneg_right
                    (Real.rpow_le_rpow_of_exponent_le ha1 hexp) hP0.le
              _ ≤ (A.card : ℝ)
                    ^ (q * (1 + (q - 1) * (Dj : ℝ))) * Pj ^ q :=
                  mul_le_mul_of_nonneg_left hPq
                    (Real.rpow_nonneg ha0.le _)
              _ = ((A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ))) ^ q
                    * Pj ^ q := by
                  rw [← Real.rpow_mul ha0.le]; ring_nf
              _ = ((A.card : ℝ) ^ (1 + (q - 1) * (Dj : ℝ)) * Pj) ^ q :=
                  (Real.mul_rpow (Real.rpow_nonneg ha0.le _)
                    hP0.le).symm
              _ ≤ (Aj.card : ℝ) ^ q :=
                  Real.rpow_le_rpow
                    (mul_nonneg (Real.rpow_nonneg ha0.le _) hP0.le)
                    hsz hq0.le
              _ ≤ (A'.card : ℝ) := hqA'
          · -- `(B'.card)·|A|^{-4(Dj+2)} ≤ Pj^κ`
            rw [hcastD]
            calc (B'.card : ℝ)
                  * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1 + 1)))
                ≤ (A.card : ℝ) ^ (4 : ℝ)
                    * (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1 + 1))) :=
                  mul_le_mul_of_nonneg_right hbox4'
                    (Real.rpow_nonneg ha0.le _)
              _ = (A.card : ℝ) ^ (-(4 * ((Dj : ℝ) + 1))) := by
                  rw [← Real.rpow_add ha0]; congr 1; ring
              _ ≤ Pj ^ κ := hPowj
      · push_neg at hαj
        exact (contra_of_ge_one hsubj hcexj hNj hαj).elim
  obtain ⟨dJ, AJ, BJ, ζJ, DJ, PJ, hdJ, -, -, hsubJ, hcexJ, hζJ, -, -,
    hNJ, -, -, -, -⟩ := iter J le_rfl
  -- At `j = J` the slack satisfies `ζ_J ≥ 1`, so `α_{d_J} + ζ_J ≥ 1`.
  have hα0 : (0 : ℝ) ≤ alphaExp dJ :=
    (by norm_num : (0 : ℝ) ≤ 1 / 4).trans (one_quarter_le_alphaExp hdJ)
  have h1 : (1 : ℝ) ≤ alphaExp dJ + ζJ := by linarith
  exact contra_of_ge_one hsubJ hcexJ hNJ h1

/-- The bookkeeping-enriched step conclusion: as `Thm2.StepConclusion`
(the produced derived counterexample `A' ⊆ B' ⊆ ℤ^{d'}` at slack
`ζ + incr`, with `|A'| ≤ |A|`, polynomial retention `|A|^q ≤ |A'|` and
multiplicative retention `ρ·|A| ≤ |A'|`) but additionally reporting
`ρ ≤ 1`, the *uniform* off-diagonal increment `d' ≠ d → ζ + ι ≤ ζ'`,
and the diagonal box-shrinkage `d' = d → |B'| ≤ ρ^κ·|B|` — the
conjunction `StepPropB` tracks per step.  `incr` is the per-instance
increment `min ι (θ |A|)`.  Packaged as an `abbrev` so the existential
is transparent at use sites. -/
abbrev StepConclusionB {d : ℕ} (A : Finset (Fin d → ℤ)) (B : GAP.Box d)
    (ζ incr ι q κ : ℝ) : Prop :=
  ∃ (d' : ℕ) (A' : Finset (Fin d' → ℤ)) (B' : GAP.Box d') (ζ' ρ : ℝ),
    1 ≤ d' ∧ B'.IsInterval ∧ NonAveraging A' ∧ A' ⊆ B'.toFinset ∧
    A'.card ≤ A.card ∧ (A.card : ℝ) ^ q ≤ (A'.card : ℝ) ∧
    ρ * (A.card : ℝ) ≤ (A'.card : ℝ) ∧ 0 < ρ ∧ ρ ≤ 1 ∧
    ζ + incr ≤ ζ' ∧
    (B'.card : ℝ) ^ (alphaExp d' + ζ') < (A'.card : ℝ) ∧
    (d' ≠ d → ζ + ι ≤ ζ') ∧
    (d' = d → (B'.card : ℝ) ≤ ρ ^ κ * (B.card : ℝ))

/-- **Case-1 assembly, bookkeeping form** (`d̃ > d`, genuine,
gap-free).  As `Thm2.step_up` — the embedded image `Ā = ϕ_{P̃}(Â)`
inside `B' = coeffBox P̃` is a non-averaging counterexample — but the
increment used is the *uniform* `ι` itself (admissible since
`ι ≤ c₀/16` and `α_{d̃} + ζ + ι ≤ 1` are hypotheses here rather than
`incr ≤ c₀/16` and `α_{d̃} + ζ + incr ≤ 1`).  Reporting `ζ' = ζ + ι`
then makes the off-diagonal clause `d' ≠ d → ζ + ι ≤ ζ'` hold with
equality and the diagonal clause vacuous (`d' = d̃ > d`), while
`ζ + incr ≤ ζ'` follows from `incr ≤ ι`.  The retained factor is
`ρ = |A|^{-ε}/2 ≤ 1`. -/
theorem step_up_bookkeeping {d n dt : ℕ} {A : Finset (Fin d → ℤ)}
    {B : GAP.Box d} {At : Finset (Fin n → ℤ)} {ct : ℝ}
    (Wt : SubSumWitness At ct dt)
    {δ ζ incr ι ε C c₀ q κ : ℝ} (hder : DerivedFrom A δ At)
    (hd : 1 ≤ d) (hdt : d < dt) (hζ : 0 < ζ)
    (hNA : NonAveraging A)
    (hι : 0 < ι) (hιc : ι ≤ c₀ / 16)
    (hαe' : αd dt + ζ + ι ≤ 1)
    (hobs15 : (αd dt + ζ) *
        ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) ≤ 1 - c₀)
    (_hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hε : 0 < ε) (hεc : ε ≤ c₀ / 8)
    (ha : (1 : ℝ) < A.card)
    (hba : (B.card : ℝ) ≤ (A.card : ℝ) ^ (αd d + ζ)⁻¹)
    (hp : (Wt.P.coeffBox.card : ℝ) ≤
      C * (A.card : ℝ) ^ (-(1 - ε) * ((dt : ℝ) - (d : ℝ))) * B.card)
    (hAt : (A.card : ℝ) ^ (1 - ε) ≤ At.card)
    (hAh : (At.card : ℝ) / 2 ≤ Wt.imageAh.card)
    (hC : 1 ≤ C) (hCa : 2 * C ≤ (A.card : ℝ) ^ (c₀ / 8))
    (_hq0 : 0 < q) (hq : q ≤ 1 - 2 * ε)
    (hεpow : (2 : ℝ) ≤ (A.card : ℝ) ^ ε)
    (hincr : incr ≤ ι) :
    StepConclusionB A B ζ incr ι q κ := by
  set a : ℝ := (A.card : ℝ)
  have ha1 : (1 : ℝ) ≤ a := ha.le
  have ha0 : (0 : ℝ) < a := by linarith
  have he4 : (1 / 4 : ℝ) ≤ αd d + ζ :=
    (Thm2.αd_quarter_le hd).trans (by linarith)
  have hinv4 : (αd d + ζ)⁻¹ ≤ 4 := by
    calc (αd d + ζ)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he4
      _ = 4 := by norm_num
  have hk : (0 : ℝ) < (dt : ℝ) - (d : ℝ) :=
    sub_pos.mpr (by exact_mod_cast hdt)
  have he' : (0 : ℝ) < αd dt + (ζ + ι) := by
    have h1dt : 1 ≤ dt := by omega
    linarith [Thm2.αd_quarter_le h1dt, hι]
  -- the Observation-15 bound at slack `ζ + ι` (the bracket is `≤ 4`,
  -- absorbing the extra `ι·X ≤ c₀/4` via `ι ≤ c₀/16`).
  have hXnn : (0 : ℝ) ≤ (1 - ε) * ((dt : ℝ) - (d : ℝ)) :=
    mul_nonneg (by linarith) hk.le
  have hX : ι * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)))
      ≤ c₀ / 4 := by
    have hle : (αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)) ≤ 4 := by
      linarith
    calc ι * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)))
        ≤ ι * 4 := mul_le_mul_of_nonneg_left hle hι.le
      _ ≤ c₀ / 4 := by linarith
  have hobs : (αd dt + (ζ + ι)) *
      ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) ≤ 1 - c₀ / 2 := by
    have hde : (αd dt + (ζ + ι)) *
        ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) =
        (αd dt + ζ) * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) +
        ι * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) := by ring
    rw [hde]
    linarith
  have hεc' : ε ≤ c₀ / 2 / 4 := by
    have h : (c₀ / 2 : ℝ) / 4 = c₀ / 8 := by ring
    rwa [h]
  have hCa' : 2 * C ≤ a ^ (c₀ / 2 / 2) := by
    have h : (c₀ / 2 : ℝ) / 2 = c₀ / 4 := by ring
    rw [h]
    calc 2 * C ≤ a ^ (c₀ / 8) := hCa
      _ ≤ a ^ (c₀ / 4) :=
        Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
  have hmain := Thm2.case_up_pow (a := a) (b := (B.card : ℝ))
    (p := (Wt.P.coeffBox.card : ℝ)) (C := C) (e := αd d + ζ)
    (e' := αd dt + (ζ + ι)) (k := (dt : ℝ) - (d : ℝ)) (ε := ε)
    (c := c₀ / 2) ha (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC he'
    (by linarith : αd dt + (ζ + ι) ≤ 1) hk.le (by linarith) hε.le
    hεc' hobs hp hba hCa'
  -- assemble `StepConclusionB` with `A' = ϕ(Â)`, `B' = coeffBox P̃`,
  -- `ζ' = ζ + ι`, `ρ = a^{-ε}/2`.
  refine ⟨dt, Wt.imageAh, Wt.P.coeffBox, ζ + ι, a ^ (-ε) / 2,
    by omega, Thm2.coeffBox_isInterval _, ?_, Wt.imageAh_subset_coeffBox,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- non-averaging: `DerivedFrom` moves preserve it, `Â ⊆ Ã` inherits,
    -- and `ϕ` transports it.
    exact GAP.nonAveraging_ptCoeffImage _
      (fun _ ha ↦ Wt.hsub (Finset.mem_union_left _ ha))
      (NonAveraging.mono Wt.hAh (hder.nonAveraging hNA))
  · -- `|A'| ≤ |A|`
    rw [Wt.card_imageAh]
    exact (Finset.card_le_card Wt.hAh).trans hder.card_le
  · -- `|A|^q ≤ |A'|` via `q ≤ 1 - 2ε` and `2 ≤ |A|^ε`
    calc a ^ q ≤ a ^ (1 - 2 * ε) := Real.rpow_le_rpow_of_exponent_le ha1 hq
      _ = a ^ (1 - ε) / a ^ ε := by
          rw [show (1 - 2 * ε : ℝ) = (1 - ε) - ε by ring,
            Real.rpow_sub ha0]
      _ ≤ a ^ (1 - ε) / 2 :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg ha0.le _)
            (by norm_num) hεpow
      _ ≤ (At.card : ℝ) / 2 := by linarith
      _ ≤ (Wt.imageAh.card : ℝ) := hAh
  · -- `ρ·|A| = |A|^{1-ε}/2 ≤ |A'|`
    have hρa : a ^ (-ε) / 2 * a = a ^ (1 - ε) / 2 := by
      have h := Real.rpow_add ha0 (-ε) 1
      rw [Real.rpow_one, show (-ε : ℝ) + 1 = 1 - ε by ring] at h
      rw [div_mul_eq_mul_div, ← h]
    calc a ^ (-ε) / 2 * a = a ^ (1 - ε) / 2 := hρa
      _ ≤ (At.card : ℝ) / 2 := by linarith
      _ ≤ (Wt.imageAh.card : ℝ) := hAh
  · exact div_pos (Real.rpow_pos_of_pos ha0 _) (by norm_num)
  · -- `ρ = a^{-ε}/2 ≤ 1`
    have hρle : a ^ (-ε) ≤ (1 : ℝ) :=
      Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith)
    linarith
  · -- `ζ + incr ≤ ζ + ι` from `incr ≤ ι`
    linarith
  · -- `(B'.card)^{α_{d'} + ζ'} < |A'|` (`alphaExp dt ≡ αd dt`)
    show (Wt.P.coeffBox.card : ℝ) ^ (αd dt + (ζ + ι))
        < (Wt.imageAh.card : ℝ)
    calc (Wt.P.coeffBox.card : ℝ) ^ (αd dt + (ζ + ι))
        < a ^ (1 - ε) / 2 := hmain
      _ ≤ (At.card : ℝ) / 2 := by linarith
      _ ≤ (Wt.imageAh.card : ℝ) := hAh
  · intro _
    exact le_refl _
  · -- `d' = d̃ > d`: the diagonal clause is vacuous
    intro heq
    omega

/-- **Residual §4 leaf, bookkeeping form.**  As `Thm2.residual_step`
(produce the step conclusion in every case where the clean up-move is
unavailable: `d̃ < d`, `d̃ = d`, or `d̃ > d` with `α_{d̃} + ζ + ι ≥ 1`),
but reporting the `StepConclusionB` fields.  The two extra hypotheses
relative to `Thm2.residual_step` are exactly the parameter relations
the strengthened conclusion needs in the paper's bookkeeping:

* `2 * κ ≤ K` — the `d̃ = d` shrink bound `|P̃| ≤ C(|Ã|/|A|)^K|B|` with
  `ρ ≈ |Ã|/(2|A|)` absorbs `C·2^κ` into `ρ^{κ−K}` once `K ≥ 2κ` (the
  paper's `κ = K/2`);
* `ι ≤ g / 2` and `ε ≤ g / 2` — the `d̃ < d` increment
  `α_d − α_{d̃} − ε ≥ g − g/2 ≥ ι` is uniform (`g` is the
  `min (1/12) (2/(D(D+1)))` gap floor for `d ≤ D`).

**Missing residual facts** (what a proof of this leaf still needs, on
top of `Thm2.residual_step`): in the `d̃ = d` non-shrink sub-case the
box `B̃` comes from `embedded_in_mu_convex_position` (Theorem 4) +
`density_increment` (Lemma 1) + the *discrete John lemma* (Lemma 7,
unformalized), and the paper's bound `|B̃| ≪ η·ρ^K|B|` (`η ≤ 1`,
`ρ ≤ μ^{c(d)}` absorbing constants into `ρ^{K/2}`) must be transported
to `|B'| ≤ ρ^κ|B|`; in the `d̃ > d` degenerate sub-case
(`α_{d̃} + ζ + ι ≥ 1`) a dimension-changing derived counterexample at
slack `≥ ζ + ι` must be produced without the `α_{d̃} + ζ + ι ≤ 1`
margin (the slack is already `> 1 − ι` at dimension `d̃`, so the
uniform gain is realized by reporting `ζ'` at the boundary). -/
theorem residual_step_bookkeeping
    {d : ℕ} {A : Finset (Fin d → ℤ)} {B : GAP.Box d}
    {ζ incr q ε K ι κ g : ℝ} {N : ℕ}
    (hd : 1 ≤ d) (hζ : 0 < ζ) (hαζ : alphaExp d + ζ < 1)
    (hBint : B.IsInterval) (hNA : NonAveraging A)
    (hsub : A ⊆ B.toFinset)
    (hcex : (B.card : ℝ) ^ (alphaExp d + ζ) < (A.card : ℝ))
    (hN : N ≤ A.card)
    (hε : 0 < ε) (hε1 : ε < 1) (hεg : ε ≤ g / 2)
    (hK : 100 ≤ K) (hKκ : 2 * κ ≤ K)
    (hq0 : 0 < q) (hq : q ≤ 1 - ε) (hι : 0 < ι) (hκ : 0 < κ) (hg : 0 < g)
    (hιg : ι ≤ g / 2)
    (hincr : 0 < incr) (hincrι : incr ≤ ι) (hincrg : incr ≤ g)
    (hincrθ : incr ≤ ι / Real.log (A.card : ℝ))
    (hdata : Thm2.Lemma10Data A B ε K) :
    StepConclusionB A B ζ incr ι q κ := sorry

/-- **Bookkeeping-strengthened §4 step** (leaf).  The same parameter
package as `Thm2.thm2_step`, but the step conclusion additionally
reports the two facts the paper's final bookkeeping paragraph needs:

* a *uniform* slack increment `ι` on every dimension-changing step
  (`d̃ ≠ d`: the paper's `θ(ζ,d)` — `step_up`/`case_down_pow` give
  `c(ζ)` resp. `α_d − α_{d̃} − ε`, bounded below uniformly for
  `ζ ∈ [ζ₀, 1)`), and
* the box-shrinkage bound `|B'| ≤ ρ^κ·|B|` on every same-dimension
  step (`d̃ = d`: `|B̃| ≪ η·ρ^K·|B|` with `η ≤ 1`, and `ρ ≤ μ^{c(d)}`
  absorbs the implied constant into `κ = K/2` for large `|A|` —
  the `hsame` bound `|P̃| ≤ C(|Ã|/|A|)^K·|B|` of `Lemma10Data`).

The numeric side condition is the paper's choice of `ε` small in
`ζ, d` (so `1 − q` is small against `⌈(1−ζ)/ι⌉`) and `K` large
(so `4(U+1)/κ ≤ 1/4`).  Discharging this leaf = replay
`Thm2.thm2_step` with `StepConclusion` extended by the two fields;
`residual_step` would then need to report them. -/
theorem thm2_step_bookkeeping (ζ₀ : ℝ) (hζ₀ : 0 < ζ₀) :
    ∃ (ι q κ : ℝ) (θ : ℝ → ℝ) (N : ℕ),
      0 < ι ∧ 0 < q ∧ q ≤ 1 ∧ 0 < κ ∧ 2 ≤ N ∧
      (∀ x : ℝ, 2 ≤ x → 0 < θ x) ∧ AntitoneOn θ (Set.Ici (2 : ℝ)) ∧
      (1 - q) * (⌈(1 - ζ₀) / ι⌉₊ : ℝ)
        + 4 * ((⌈(1 - ζ₀) / ι⌉₊ : ℝ) + 1) / κ ≤ 1 / 2 ∧
      StepPropB ζ₀ ι q κ θ N := by
  rcases lt_or_ge ζ₀ 1 with hζ1 | hζ1
  · obtain ⟨c₀, hc₀, hc₀1, hobs15⟩ := Thm2.observation15_ge hζ₀ hζ1
    -- parameters: `D` the dimension bound, `g` the down-move gap floor,
    -- `ι = min (c₀/16, g/2)` the uniform increment (the `g/2` slack is
    -- what the `d̃ < d` uniform gain `g − ε ≥ g/2 ≥ ι` needs),
    -- `U = ⌈(1−ζ₀)/ι⌉` the dimension-change budget,
    -- `ε ≤ 0.01ζ₀, c₀/8, g/2, 1/(8U)` small,
    -- `κ = 16(U+1)` so `4(U+1)/κ = 1/4`, `K = max 100 (2κ)`,
    -- `q = 1 − 2ε`, `θ x = ι / log x`.
    have hD0 : (0 : ℝ) < ((⌈2 / ζ₀⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr (div_pos two_pos hζ₀)
    set D : ℝ := ((⌈2 / ζ₀⌉₊ : ℕ) : ℝ) with hD_def
    set g := min (1 / 12 : ℝ) (2 / (D * (D + 1))) with hg_def
    have hg : 0 < g := by
      rw [hg_def]
      exact lt_min (by norm_num)
        (div_pos two_pos (mul_pos hD0 (by linarith)))
    set ι := min (c₀ / 16) (g / 2) with hι_def
    have hι : 0 < ι := by
      rw [hι_def]
      exact lt_min (by linarith) (by linarith)
    have hιc : ι ≤ c₀ / 16 := by rw [hι_def]; exact min_le_left _ _
    have hιg2 : ι ≤ g / 2 := by rw [hι_def]; exact min_le_right _ _
    have hιg : ι ≤ g := hιg2.trans (by linarith)
    set U : ℕ := ⌈(1 - ζ₀) / ι⌉₊ with hU_def
    have hUpos : 0 < U := Nat.ceil_pos.mpr (div_pos (by linarith) hι)
    have hUr0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hUpos
    have hUne : (U : ℝ) ≠ 0 := hUr0.ne'
    set ε := min (0.01 * ζ₀)
      (min (c₀ / 8) (min (g / 2) (1 / (8 * (U : ℝ))))) with hε_def
    have hε : 0 < ε := by
      rw [hε_def]
      exact lt_min (mul_pos (by norm_num) hζ₀)
        (lt_min (by linarith)
          (lt_min (by linarith)
            (div_pos one_pos (mul_pos (by norm_num) hUr0))))
    have hεle : ε ≤ 0.01 * ζ₀ := by rw [hε_def]; exact min_le_left _ _
    have hεc : ε ≤ c₀ / 8 := by
      rw [hε_def]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hεg : ε ≤ g / 2 := by
      rw [hε_def]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    have hεU : ε ≤ 1 / (8 * (U : ℝ)) := by
      rw [hε_def]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    have hε1 : ε < 1 := by
      have h1 : 0.01 * ζ₀ < (0.01 : ℝ) :=
        mul_lt_of_lt_one_right (by norm_num) hζ1
      linarith
    have hε3 : ε < 1 / 3 := by linarith
    set κ : ℝ := 16 * ((U : ℝ) + 1) with hκ_def
    have hκ : 0 < κ := by rw [hκ_def]; positivity
    set K : ℝ := max 100 (2 * κ) with hK_def
    have hK : 100 ≤ K := by rw [hK_def]; exact le_max_left _ _
    have hKκ : 2 * κ ≤ K := by rw [hK_def]; exact le_max_right _ _
    have hK0 : 0 < K := by linarith
    obtain ⟨N₀, hl10⟩ := Thm2.lemma10_data (ε := ε) (K := K) hε hε3 hK0
      ⌈2 / ζ₀⌉₊
    set q := 1 - 2 * ε with hq_def
    have hq0 : 0 < q := by rw [hq_def]; linarith
    have hq1 : q ≤ 1 := by rw [hq_def]; linarith
    have hqε : q ≤ 1 - ε := by rw [hq_def]; linarith
    set θ : ℝ → ℝ := fun x ↦ ι / Real.log x with hθ_def
    have hθpos : ∀ x : ℝ, 2 ≤ x → 0 < θ x := by
      intro x hx
      simp only [hθ_def]
      exact div_pos hι (Real.log_pos (by linarith))
    have hθanti : AntitoneOn θ (Set.Ici (2 : ℝ)) := by
      intro x hx y _ hxy
      have hx2 : (2 : ℝ) ≤ x := hx
      simp only [hθ_def]
      exact div_le_div_of_nonneg_left hι.le
        (Real.log_pos (by linarith))
        (Real.log_le_log (by linarith) hxy)
    -- the bookkeeping numeric side condition:
    -- `(1−q)·U = 2εU ≤ 1/4` and `4(U+1)/κ = 1/4`.
    have hnum : (1 - q) * (U : ℝ) + 4 * ((U : ℝ) + 1) / κ ≤ 1 / 2 := by
      have h1q : (1 : ℝ) - q = 2 * ε := by rw [hq_def]; ring
      have hU1p : (0 : ℝ) < (U : ℝ) + 1 := by linarith
      have hterm1 : (1 - q) * (U : ℝ) ≤ 1 / 4 := by
        rw [h1q]
        calc (2 * ε) * (U : ℝ)
            ≤ (2 * (1 / (8 * (U : ℝ)))) * (U : ℝ) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hεU (by norm_num)) hUr0.le
          _ = 1 / 4 := by
              have h8Une : (8 : ℝ) * (U : ℝ) ≠ 0 :=
                ne_of_gt (mul_pos (by norm_num) hUr0)
              field_simp
              ring
      have hterm2 : 4 * ((U : ℝ) + 1) / κ = 1 / 4 := by
        rw [hκ_def]
        have h16 : (16 : ℝ) * ((U : ℝ) + 1) ≠ 0 :=
          mul_ne_zero (by norm_num) (ne_of_gt hU1p)
        rw [div_eq_iff h16]
        ring
      linarith
    -- global threshold: `N` dominates Lemma-10's `N₀`, `3` (so
    -- `log |A| > 0` and `N ≥ 2`), and `2^{1/ε}` (so `2 ≤ |A|^ε`).
    refine ⟨ι, q, κ, θ, max N₀ (max 3 (Nat.ceil ((2 : ℝ) ^ (1 / ε)))),
      hι, hq0, hq1, hκ, ?_, hθpos, hθanti, ?_, ?_⟩
    · exact le_trans (by norm_num : (2 : ℕ) ≤ 3)
        ((le_max_left _ _).trans (le_max_right _ _))
    · rw [← hU_def]
      exact hnum
    · intro d hd ζ hζ hαζ A B hBint hNA hsub hcex hN
      have h2a : (2 : ℝ) ≤ (A.card : ℝ) := by
        exact_mod_cast (le_trans (by omega : 2 ≤
          max N₀ (max 3 (Nat.ceil ((2 : ℝ) ^ (1 / ε))))) hN)
      have ha1 : (1 : ℝ) < (A.card : ℝ) := by linarith
      have ha0 : (0 : ℝ) < (A.card : ℝ) := by linarith
      have he : 0 < alphaExp d + ζ :=
        add_pos
          (lt_of_lt_of_le (by norm_num) (one_quarter_le_alphaExp hd))
          (hζ₀.trans_le hζ)
      have hba : (B.card : ℝ) ≤ (A.card : ℝ) ^ (alphaExp d + ζ)⁻¹ :=
        (Thm2.card_lt_rpow_of_rpow_lt he (by omega) hcex).le
      -- `|B| ≤ |A|^4` for the Lemma-10 input (`(α_d+ζ)⁻¹ ≤ 4`).
      have hbox4 : (B.card : ℝ) ≤ (A.card : ℝ) ^ (4 : ℝ) := by
        have he4 : (1 / 4 : ℝ) ≤ alphaExp d + ζ :=
          (one_quarter_le_alphaExp hd).trans (by linarith)
        have hinv : (alphaExp d + ζ)⁻¹ ≤ 4 := by
          calc (alphaExp d + ζ)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ :=
                inv_anti₀ (by norm_num) he4
            _ = 4 := by norm_num
        exact hba.trans (Real.rpow_le_rpow_of_exponent_le ha1.le hinv)
      have hN0 : N₀ ≤ A.card := le_trans (by omega) hN
      -- `α_d + ζ < 1` bounds the ambient dimension by `⌈2/ζ₀⌉`.
      have hdD : d ≤ ⌈2 / ζ₀⌉₊ := by
        have hlt : (d : ℝ) < 2 / ζ :=
          Thm2.dim_lt_of_slack hd (hζ₀.trans_le hζ) hαζ
        have hle : (2 : ℝ) / ζ ≤ 2 / ζ₀ :=
          div_le_div_of_nonneg_left (by norm_num) hζ₀ hζ
        have hlt' : (d : ℝ) < (⌈2 / ζ₀⌉₊ : ℝ) :=
          (hlt.trans_le hle).trans_le (Nat.le_ceil _)
        exact le_of_lt (by exact_mod_cast hlt')
      obtain ⟨n, dt, At, ct, Wt, c', δ, γ, C, hδ, hδ4, hγ, hγδ, hγa,
        hder, hC, hCaA, hAt, hAh, hirr, hup, hsame, hdown⟩ :=
        hl10 hdD hBint hNA hsub hbox4 hN0
      -- the per-instance increment `incr = min ι (θ |A|)`
      set incr := min ι (θ (A.card : ℝ)) with hincr_def
      have hincr : 0 < incr := by
        rw [hincr_def]
        exact lt_min hι (hθpos _ h2a)
      have hincrι : incr ≤ ι := by rw [hincr_def]; exact min_le_left _ _
      have hincrg : incr ≤ g := hincrι.trans hιg
      have hincrθ : incr ≤ ι / Real.log (A.card : ℝ) := by
        rw [hincr_def]
        simp only [hθ_def]
        exact min_le_right _ _
      have hεpow : (2 : ℝ) ≤ (A.card : ℝ) ^ ε := by
        have h2ε : (2 : ℝ) ^ (1 / ε : ℝ) ≤ (A.card : ℝ) := by
          calc (2 : ℝ) ^ (1 / ε : ℝ)
              ≤ ((⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
            _ ≤ (A.card : ℝ) := by
                exact_mod_cast (le_trans (by omega : ⌈(2 : ℝ) ^ (1 / ε)⌉₊
                  ≤ max N₀ (max 3 (Nat.ceil ((2 : ℝ) ^ (1 / ε))))) hN)
        have h2 : ((2 : ℝ) ^ (1 / ε : ℝ)) ^ ε = 2 := by
          rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
          rw [show (1 / ε : ℝ) * ε = 1 from div_mul_cancel₀ _ hε.ne']
          exact Real.rpow_one _
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε : ℝ)) ^ ε := h2.symm
          _ ≤ (A.card : ℝ) ^ ε :=
            Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h2ε hε.le
      by_cases hcase : d < dt ∧ αd dt + ζ + ι ≤ 1 ∧
        2 * C ≤ (A.card : ℝ) ^ (c₀ / 8)
      · -- **Case 1** (`d̃ > d`): genuine up-move, uniform increment `ι`.
        obtain ⟨hdt, hαe', hCa⟩ := hcase
        have hobs15' : (αd dt + ζ) *
            ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)))
            ≤ 1 - c₀ := by
          have hlem := hobs15 dt d ζ hd hdt hζ ε hε.le hεle
          simpa [one_div] using hlem
        exact step_up_bookkeeping Wt hder hd hdt (hζ₀.trans_le hζ) hNA
          hι hιc hαe' hobs15' hc₀ hc₀1 hε hεc ha1 hba (hup hdt) hAt hAh hC
          hCa hq0 (le_of_eq hq_def) hεpow hincrι
      · -- **Residual cases** (`d̃ < d`, `d̃ = d`, degenerate `d̃ > d`):
        -- the leaf.
        clear hcase
        exact residual_step_bookkeeping hd (hζ₀.trans_le hζ) hαζ hBint
          hNA hsub hcex hN hε hε1 hεg hK hKκ hq0 hqε hι hκ hg hιg2 hincr
          hincrι hincrg hincrθ
          ⟨n, dt, At, ct, Wt, c', δ, γ, C, hδ, hδ4, hγ, hγδ, hγa, hder,
            hC, hCaA, hAt, hAh, hirr, hup, hsame, hdown⟩
  · -- `ζ₀ ≥ 1`: `α_d + ζ < 1` is impossible since `α_d ≥ 1/4`, so the
    -- step property is vacuous; `⌈(1−ζ₀)/1⌉₊ = 0` makes the numeric
    -- side condition `4/8 ≤ 1/2`.
    refine ⟨1, 1, 8, fun _ => 1, 2, one_pos, one_pos, le_rfl,
      by norm_num, le_rfl, ?_, ?_, ?_, ?_⟩
    · intro x _; exact one_pos
    · intro x _ y _ _; exact le_refl _
    · have hU0 : ⌈(1 - ζ₀) / (1 : ℝ)⌉₊ = 0 :=
        Nat.ceil_eq_zero.mpr (by rw [div_one]; linarith)
      rw [hU0]
      norm_num
    · intro d hd ζ hζ hαζ A B _ _ _ _ _
      exfalso
      have h14 : (1 / 4 : ℝ) ≤ alphaExp d := one_quarter_le_alphaExp hd
      linarith

/-- **Theorem 2.** For `d ≥ 1` and `ζ > 0`, no non-averaging
`A ⊆ B ⊆ ℤ^d` satisfies `|A| > |B|^{α_d + ζ}` once `|A|` is large enough.

**Assembly.** `nonaveraging_box_bound_of_step` applied to
`thm2_step_bookkeeping` — the `StepPropB`-strengthened version of
`Thm2.thm2_step`, whose `d̃ > d` branch is genuinely proved
(`Thm2.step_up`, via the Observation-15 bound `observation15_ge` and the
power estimate `Thm2.case_up_pow`) and whose residual branches
(`d̃ < d`, `d̃ = d`, degenerate `d̃ > d`) are the leaf
`Thm2.residual_step`; the Lemma-10 input is the leaf `Thm2.lemma10_data`
— the existing `irreduciblization` cannot supply it, being vacuous
(`SubSumWitness.degenerate` gives `Â = ∅`, `d̃ = 0`); see
`irreduciblization_statement_is_false`.  The `d̃ = d` case additionally
needs `density_increment` (Lemma 1), `embedded_in_mu_convex_position`
(Theorem 4) and a discrete-John conversion of convex bodies to boxes.
The `StepPropB` strengthening over `Thm2.StepProp` is precisely the
uniform off-diagonal increment and the diagonal box-shrinkage bound
`|B'| ≤ ρ^κ|B|` that `residual_step`'s `hsame` data supplies — see the
docstrings of `StepPropB` and `thm2_step_bookkeeping`. -/
theorem nonaveraging_box_bound (d : ℕ) (hd : 1 ≤ d) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ M : ℕ, ∀ (A : Finset (Fin d → ℤ)) (B : GAP.Box d),
      B.IsInterval →
      NonAveraging A → A ⊆ B.toFinset → M ≤ A.card →
      (A.card : ℝ) ≤ (B.card : ℝ) ^ (alphaExp d + ζ) :=
  nonaveraging_box_bound_of_step d hd hζ (thm2_step_bookkeeping ζ hζ)

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
