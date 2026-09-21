import Nonaveraging.Structure
import Nonaveraging.Observation15

/-!
# Iteration machinery for Theorem 2 (`nonaveraging_box_bound`)

Helpers for the density-increment iteration of Pham–Zakharov
(arXiv:2410.14624v2, §4), building on the `DerivedFrom` /
`SubSumWitness` / `coeffBox` API of `Structure.lean`.

* `witness_proper` — the witness GAP `P` is proper (its dilation
  `k • P` is, and properness is dilation-invariant), so
  `|P.coeffBox| = ∏ᵢ widthᵢ = |P.toFinset|` and the `|P̃|` bounds
  produced by `irreduciblization` apply verbatim to `coeffBox`.
* `half_le_Ah_card` — `|Â| ≥ |A|/2` once `log |A| ≥ 2c⁻¹`.  (The
  scaffold's `irreduciblization` produces the witness constant `ct`
  existentially and *unbounded*; this lemma makes explicit the extra
  largeness condition `2·ct⁻¹ ≤ log |Ã|` that the paper gets for free
  from Corollary 5's fixed constant.)
* `αd` numerics (ports of the `alphaExp` API of `UpperBound.lean` to
  `αd`, so this file stays below `UpperBound.lean` in the import
  hierarchy) and a *uniform* version `observation15_ge` of Observation
  15: the left side is nonincreasing in `ζ`, so the constant `c` at the
  initial `ζ` works at every later `ζ_j ≥ ζ`.  This is the paper's
  `inf_{ζ'∈[ζ,0.9]} c(ζ') > 0` argument, avoiding continuity of `c(ζ)`.
* The numerical step lemmas for the `d̃ ≠ d` cases of Lemma 10
  (`case_up_pow`, `case_down_pow`) and for the `d̃ = d ∧ ρ ≤ |A|^{-σ}`
  shrink sub-case (`case_shrink_pow`): from
  `|P̃| ≤ C·|A|^{-(1-ε)(d̃-d)}·|B|` resp. `≤ C|B|` resp. `≤ Cρ^K|B|` to
  `|B'|^{e'} < |A'|` at the increased slack.

The remaining `d̃ = d ∧ ρ > |A|^{-σ}` case needs Theorem 4
(`embedded_in_mu_convex_position`), Lemma 1 (`density_increment`) and —
crucially — the *discrete John lemma* (Lemma 7 of the paper), which has
no formalized counterpart here: it converts the convex `Ω' ⊆ conv B̄`
produced by `density_increment` back into a `GAP.Box` of size
`O_d(vol Ω')`.  See `thm2_report.md` for the precise gap statement.
-/

open Finset MeasureTheory Filter

namespace Nonaveraging

/- All declarations of this file live in `Thm2` to avoid collisions
with the concurrently-developed `Structure.lean` API. -/
namespace Thm2

/-!
## Witness properness
-/

/-- `k • P` proper implies `P` proper (the coefficient sets coincide and
`eval` commutes with `•`). -/
theorem proper_of_smul_proper {ℓ d : ℕ} (P : GAP ℓ d) {k : ℕ}
    (h : (k • P).Proper) : P.Proper := by
  have hev : ∀ n : Fin d → ℕ, (k • P).eval n = (k : ℤ) • P.eval n := by
    intro n
    show (k : ℤ) • P.base + ∑ i, (n i : ℤ) • ((k : ℤ) • P.step i)
        = (k : ℤ) • (P.base + ∑ i, (n i : ℤ) • P.step i)
    rw [smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [← mul_smul, ← mul_smul, mul_comm]
  intro n hn m hm hnm
  apply h hn hm
  rw [hev, hev, hnm]

/-- The witness GAP `P` is proper: `k • P` is proper and `k ≥ 1`. -/
theorem witness_proper {ℓ : ℕ} {c : ℝ} {A : Finset (Fin ℓ → ℤ)} {d : ℕ}
    (W : SubSumWitness A c d) : W.P.Proper :=
  proper_of_smul_proper _ W.hproper

/-- `|W.P.coeffBox| = |W.P.toFinset|`: the `|P̃|` bounds of
`irreduciblization` apply verbatim to the new box. -/
theorem witness_card_coeffBox {ℓ : ℕ} {c : ℝ} {A : Finset (Fin ℓ → ℤ)}
    {d : ℕ} (W : SubSumWitness A c d) :
    W.P.coeffBox.card = W.P.toFinset.card := by
  rw [GAP.coeffBox_card, ← GAP.card_toFinset_of_proper _ (witness_proper W)]

/-- `|Â| ≥ |A|/2` once `log |A| ≥ 2c⁻¹`. -/
theorem half_le_Ah_card {ℓ : ℕ} {c : ℝ} {A : Finset (Fin ℓ → ℤ)} {d : ℕ}
    (W : SubSumWitness A c d)
    (hlog : 2 * c⁻¹ ≤ Real.log (A.card : ℝ)) :
    (A.card : ℝ) / 2 ≤ (W.Ah.card : ℝ) := by
  have hpos : (0 : ℝ) < A.card := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2)
      W.two_le_card
  have hone : (1 : ℝ) < A.card := by
    exact_mod_cast lt_of_lt_of_le one_lt_two W.two_le_card
  have hlogpos : (0 : ℝ) < Real.log (A.card : ℝ) := Real.log_pos hone
  have h1 := W.hAhcard
  have h2 : c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ)
      ≤ (A.card : ℝ) / 2 := by
    rw [div_le_iff₀ hlogpos]
    calc c⁻¹ * (A.card : ℝ)
        = (2 * c⁻¹) * (A.card : ℝ) / 2 := by ring
      _ ≤ Real.log (A.card : ℝ) * (A.card : ℝ) / 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hlog hpos.le)
            (by norm_num : (0 : ℝ) ≤ 2)
      _ = (A.card : ℝ) / 2 * Real.log (A.card : ℝ) := by ring
  linarith

/-!
## `αd` numerics
-/

theorem αd_quarter_le {d : ℕ} (hd : 1 ≤ d) : (1 / 4 : ℝ) ≤ αd d := by
  rcases eq_or_ne d 1 with rfl | h1
  · rw [αd_one]
  · have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
    rw [αd_of_ne_one h1, le_div_iff₀ (by linarith : (0 : ℝ) < (d : ℝ) + 1)]
    linarith

theorem αd_pos {d : ℕ} (hd : 1 ≤ d) : (0 : ℝ) < αd d :=
  lt_of_lt_of_le (by norm_num) (αd_quarter_le hd)

theorem αd_lt_one {d : ℕ} (hd : 1 ≤ d) : αd d < 1 := by
  rcases eq_or_ne d 1 with rfl | h1
  · rw [αd_one]; norm_num
  · have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
    rw [αd_of_ne_one h1, div_lt_one (by linarith : (0 : ℝ) < (d : ℝ) + 1)]
    linarith

theorem αd_strictMono {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    αd a < αd b := by
  have hb1 : b ≠ 1 := by omega
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 2 ≤ b)
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

/-- Quantitative gap of `αd`: for `1 ≤ d' < d`,
`αd d − αd d' ≥ min (1/12) (2/(d(d+1)))`. -/
theorem αd_sub_gap {d d' : ℕ} (hd' : 1 ≤ d') (hdd : d' < d) :
    min (1 / 12 : ℝ) (2 / ((d : ℝ) * ((d : ℝ) + 1)))
      ≤ αd d - αd d' := by
  rcases eq_or_ne d' 1 with rfl | h1
  · have h3 : (1 / 3 : ℝ) ≤ αd d := by
      have hdn1 : d ≠ 1 := by omega
      have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
      rw [αd_of_ne_one hdn1, le_div_iff₀ (by linarith : (0 : ℝ) < (d : ℝ) + 1)]
      linarith
    rw [αd_one]
    exact le_trans (min_le_left _ _) (by linarith)
  · have hd2 : 2 ≤ d' := by omega
    have hle : αd d' ≤ αd (d - 1) := by
      rcases eq_or_lt_of_le (by omega : d' ≤ d - 1) with h | h
      · rw [h]
      · exact (αd_strictMono (by omega : 1 ≤ d') h).le
    have hdm1 : d - 1 ≠ 1 := by omega
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (show (1 : ℕ) ≤ d by omega), Nat.cast_one]
    have hgap : αd d - αd (d - 1)
        = 2 / ((d : ℝ) * ((d : ℝ) + 1)) := by
      have hdne : (d : ℝ) ≠ 0 := by linarith
      have hd1ne : (d : ℝ) + 1 ≠ 0 := by linarith
      rw [αd_of_ne_one (by omega : d ≠ 1), αd_of_ne_one hdm1, hcast]
      rw [show (d : ℝ) - 1 + 1 = (d : ℝ) by ring]
      rw [div_sub_div _ _ hd1ne hdne,
        div_eq_div_iff (mul_ne_zero hd1ne hdne) (mul_ne_zero hdne hd1ne)]
      ring
    rw [← hgap]
    exact le_trans (min_le_right _ _) (by linarith)

/-!
## Uniform Observation 15

`observation15` produces `c(ζ)` per `ζ ∈ (0,1)`.  Since the left side is
nonincreasing in `ζ` (for `d < d̂`), the constant `c(ζ)` works for all
`ζ' ≥ ζ` — this replaces the paper's `inf_{ζ'∈[ζ,0.9]} c(ζ') > 0`.
-/

/-- The Obs-15 left side is nonincreasing in `ζ` for `d < d̂`. -/
theorem obs15_mono {d dh : ℕ} (hd : 1 ≤ d) (hdh : d < dh) {ε : ℝ}
    (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {ζ ζ' : ℝ} (hζ : 0 < ζ) (hzz : ζ ≤ ζ') :
    (αd dh + ζ') * (1 / (αd d + ζ') - (1 - ε) * ((dh : ℝ) - (d : ℝ)))
      ≤ (αd dh + ζ) * (1 / (αd d + ζ) - (1 - ε) * ((dh : ℝ) - (d : ℝ))) := by
  have hαpos : (0 : ℝ) < αd d := αd_pos hd
  have hαlt : αd d < αd dh := αd_strictMono hd hdh
  have hζ' : (0 : ℝ) < ζ' := lt_of_lt_of_le hζ hzz
  have hden : (0 : ℝ) < αd d + ζ := by linarith
  have hden' : (0 : ℝ) < αd d + ζ' := by linarith
  have hk : (0 : ℝ) ≤ (dh : ℝ) - (d : ℝ) := by
    have : (d : ℝ) + 1 ≤ (dh : ℝ) := by exact_mod_cast hdh
    linarith
  have h1ε : (0 : ℝ) ≤ 1 - ε := by linarith
  -- The ratio `(αdh + ζ)/(αd + ζ)` is nonincreasing in `ζ`.
  have hratio : (αd dh + ζ') / (αd d + ζ') ≤ (αd dh + ζ) / (αd d + ζ) := by
    rw [div_le_div_iff₀ hden' hden]
    have key : (αd dh + ζ') * (αd d + ζ) - (αd dh + ζ) * (αd d + ζ')
        = (ζ' - ζ) * (αd d - αd dh) := by ring
    have hle : (ζ' - ζ) * (αd d - αd dh) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  have hprod : (1 - ε) * ((dh : ℝ) - (d : ℝ)) * (αd dh + ζ)
      ≤ (1 - ε) * ((dh : ℝ) - (d : ℝ)) * (αd dh + ζ') :=
    mul_le_mul_of_nonneg_left
      (by linarith : (αd dh : ℝ) + ζ ≤ αd dh + ζ')
      (mul_nonneg h1ε hk)
  have e : ∀ x : ℝ, (αd dh + x) * (1 / (αd d + x)
      - (1 - ε) * ((dh : ℝ) - (d : ℝ)))
      = (αd dh + x) / (αd d + x)
        - (1 - ε) * ((dh : ℝ) - (d : ℝ)) * (αd dh + x) := by
    intro x
    rcases eq_or_ne (αd d + x) 0 with hx | hx
    · rw [hx]
      simp only [div_zero]
      ring
    · simp only [mul_sub, div_eq_mul_inv, one_mul]
      ring
  rw [e ζ', e ζ]
  linarith

/-- **Uniform Observation 15**: one constant `c > 0` works for all
`ζ' ≥ ζ` simultaneously. -/
theorem observation15_ge {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (dh d : ℕ) (ζ' : ℝ), 1 ≤ d → d < dh →
      ζ ≤ ζ' → ∀ ε : ℝ, 0 ≤ ε → ε ≤ (0.01 : ℝ) * ζ →
      (αd dh + ζ') * (1 / (αd d + ζ') - (1 - ε) * ((dh : ℝ) - (d : ℝ)))
        ≤ 1 - c := by
  obtain ⟨c, hc, hcobs⟩ := observation15 hζ hζ1
  refine ⟨min c 1, lt_min hc zero_lt_one, min_le_right _ _, ?_⟩
  intro dh d ζ' hd hdh hζ' ε hε hεζ
  have hε1 : ε ≤ 1 := by linarith [hζ1, hεζ]
  refine (obs15_mono hd hdh hε hε1 hζ hζ').trans ?_
  refine (hcobs dh d hd hdh ε hε hεζ).trans ?_
  exact sub_le_sub_left (min_le_left _ _) _

/-!
## Real bookkeeping for the box bound
-/

/-- From `|B|^e < |A|` with `e > 0`, deduce `|B| < |A|^{1/e}`. -/
theorem card_lt_rpow_of_rpow_lt {m n : ℕ} {e : ℝ} (he : 0 < e) (_hn : 0 < n)
    (h : (m : ℝ) ^ e < (n : ℝ)) : (m : ℝ) < (n : ℝ) ^ e⁻¹ := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have key := Real.rpow_lt_rpow (Real.rpow_nonneg hm e) h (inv_pos.mpr he)
  rwa [← Real.rpow_mul hm, mul_inv_cancel₀ he.ne', Real.rpow_one] at key

/-- **Case 1** (`d̃ > d`) numerical core.  Given `1 < a`, `0 ≤ b`,
`0 ≤ p`, `1 ≤ C`, exponents `0 < e' ≤ 1`, `0 ≤ k`, `0 < c`, `0 ≤ ε`
with

* `e' · (e⁻¹ − (1−ε)·k) ≤ 1 − c`   (Observation 15 bookkeeping),
* `p ≤ C · a^{-(1-ε)k} · b`, `b ≤ a^{1/e}`   (`irreduciblization`),
* `ε ≤ c/4`, `2C ≤ a^{c/2}`   (largeness, absorbing `C`),

conclude `p^{e'} < a^{1-ε}/2` — i.e. the new set of size `≥ a^{1-ε}/2`
in a box of size `p` is still a counterexample at exponent `e'`. -/
theorem case_up_pow {a b p C c ε k e e' : ℝ}
    (ha : 1 < a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hC : 1 ≤ C)
    (he' : 0 < e') (he1 : e' ≤ 1) (_hk : 0 ≤ k)
    (hc : 0 < c) (_hε : 0 ≤ ε) (hεc : ε ≤ c / 4)
    (hobs : e' * (e⁻¹ - (1 - ε) * k) ≤ 1 - c)
    (hpb : p ≤ C * a ^ (-(1 - ε) * k) * b) (hba : b ≤ a ^ e⁻¹)
    (hCa : 2 * C ≤ a ^ (c / 2)) :
    p ^ e' < a ^ (1 - ε) / 2 := by
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha.le
  have hapos : (0 : ℝ) < a := zero_lt_one.trans ha
  have hu : (0 : ℝ) ≤ a ^ (-(1 - ε) * k) := Real.rpow_nonneg ha0 _
  have hCe : C ^ e' ≤ C := by
    calc C ^ e' ≤ C ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC he1
      _ = C := Real.rpow_one C
  have hstep : p ^ e' ≤ C ^ e' * a ^ (-(1 - ε) * k * e') * a ^ (e⁻¹ * e') := by
    calc p ^ e' ≤ (C * a ^ (-(1 - ε) * k) * b) ^ e' :=
        Real.rpow_le_rpow hp hpb he'.le
      _ = C ^ e' * (a ^ (-(1 - ε) * k)) ^ e' * b ^ e' := by
        rw [Real.mul_rpow (mul_nonneg (by linarith : (0 : ℝ) ≤ C) hu) hb,
          Real.mul_rpow (by linarith : (0 : ℝ) ≤ C) hu]
      _ = C ^ e' * a ^ (-(1 - ε) * k * e') * b ^ e' := by
        rw [← Real.rpow_mul ha0]
      _ ≤ C ^ e' * a ^ (-(1 - ε) * k * e') * (a ^ e⁻¹) ^ e' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb hba he'.le)
          (mul_nonneg (Real.rpow_nonneg (by linarith) _)
            (Real.rpow_nonneg ha0 _))
      _ = C ^ e' * a ^ (-(1 - ε) * k * e') * a ^ (e⁻¹ * e') := by
        rw [← Real.rpow_mul ha0]
  have hcomb : a ^ (-(1 - ε) * k * e') * a ^ (e⁻¹ * e')
      = a ^ (e' * (e⁻¹ - (1 - ε) * k)) := by
    rw [← Real.rpow_add hapos]
    congr 1
    ring
  calc p ^ e' ≤ C ^ e' * a ^ (-(1 - ε) * k * e') * a ^ (e⁻¹ * e') := hstep
    _ = C ^ e' * (a ^ (-(1 - ε) * k * e') * a ^ (e⁻¹ * e')) :=
        mul_assoc _ _ _
    _ = C ^ e' * a ^ (e' * (e⁻¹ - (1 - ε) * k)) := by rw [hcomb]
    _ ≤ C * a ^ (e' * (e⁻¹ - (1 - ε) * k)) :=
        mul_le_mul_of_nonneg_right hCe (Real.rpow_nonneg ha0 _)
    _ ≤ C * a ^ (1 - c) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le ha.le hobs) (by linarith)
    _ ≤ a ^ (c / 2) / 2 * a ^ (1 - c) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ha0 _)
        linarith
    _ = a ^ (1 - c / 2) / 2 := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hapos,
          show c / 2 + (1 - c) = 1 - c / 2 by ring]
    _ < a ^ (1 - ε) / 2 := by
        have hpow : a ^ (1 - c / 2) < a ^ (1 - ε) :=
          Real.rpow_lt_rpow_of_exponent_lt ha (by linarith)
        linarith

/-- **Case 2** (`d̃ < d`) numerical core.  Given `1 < a`, `0 ≤ b`,
`0 ≤ p`, `1 ≤ C`, `0 < e' ≤ 1`, `0 < ε'` with

* `e' · e⁻¹ ≤ 1 − ε − ε'`   (the `αd`-gap supplies the slack),
* `p ≤ C · b`, `b ≤ a^{1/e}`,
* `2C ≤ a^{ε'/2}`   (largeness),

conclude `p^{e'} < a^{1-ε}/2`. -/
theorem case_down_pow {a b p C ε ε' e e' : ℝ}
    (ha : 1 < a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hC : 1 ≤ C)
    (he' : 0 < e') (he1 : e' ≤ 1)
    (_hε : 0 ≤ ε) (hε' : 0 < ε')
    (hsplit : e' * e⁻¹ ≤ 1 - ε - ε')
    (hpb : p ≤ C * b) (hba : b ≤ a ^ e⁻¹)
    (hCa : 2 * C ≤ a ^ (ε' / 2)) :
    p ^ e' < a ^ (1 - ε) / 2 := by
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha.le
  have hapos : (0 : ℝ) < a := zero_lt_one.trans ha
  have hCe : C ^ e' ≤ C := by
    calc C ^ e' ≤ C ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC he1
      _ = C := Real.rpow_one C
  calc p ^ e' ≤ (C * b) ^ e' := Real.rpow_le_rpow hp hpb he'.le
    _ = C ^ e' * b ^ e' := Real.mul_rpow (by linarith) hb
    _ ≤ C ^ e' * (a ^ e⁻¹) ^ e' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb hba he'.le)
          (Real.rpow_nonneg (by linarith) _)
    _ = C ^ e' * a ^ (e⁻¹ * e') := by rw [Real.rpow_mul ha0]
    _ ≤ C * a ^ (e⁻¹ * e') :=
        mul_le_mul_of_nonneg_right hCe (Real.rpow_nonneg ha0 _)
    _ ≤ C * a ^ (1 - ε - ε') := by
        apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ C)
        exact Real.rpow_le_rpow_of_exponent_le ha.le
          (by linarith [hsplit])
    _ ≤ a ^ (ε' / 2) / 2 * a ^ (1 - ε - ε') := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ha0 _)
        linarith
    _ = a ^ (1 - ε - ε' / 2) / 2 := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hapos,
          show ε' / 2 + (1 - ε - ε') = 1 - ε - ε' / 2 by ring]
    _ < a ^ (1 - ε) / 2 := by
        have hpow : a ^ (1 - ε - ε' / 2) < a ^ (1 - ε) :=
          Real.rpow_lt_rpow_of_exponent_lt ha (by linarith)
        linarith

/-- **Case 3, shrink sub-case** (`d̃ = d`, `ρ := |Ã|/|A| ≤ a^{-σ}`).
Given `1 < a`, `0 ≤ b`, `0 ≤ p`, `1 ≤ C`, `0 < ρ`, exponents
`0 < e' ≤ 1` with `e' · e⁻¹ ≤ 1 + t` (a *small* increment `θ = e' − e`
gives `t = θ·e⁻¹`), `K` with `K·e' − 1 ≥ K/5` (e.g. `K ≥ 100`,
`e' ≥ 1/4`), `ρ ≤ a^{-σ}` and `2C < a^{σK/10}` with `t ≤ σK/10`:

`p ≤ C·ρ^K·b`, `b ≤ a^{1/e}` imply `p^{e'} < ρ·a/2` — i.e. the new set
of size `≥ ρ·a/2` is a counterexample at the increased exponent. -/
theorem case_shrink_pow {a b p C ρ K σ t e e' : ℝ}
    (ha : 1 < a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hC : 1 ≤ C)
    (hρ : 0 < ρ) (he' : 0 < e') (he1 : e' ≤ 1)
    (hK0 : 0 ≤ K) (hK : K / 5 ≤ K * e' - 1)
    (ht : e' * e⁻¹ ≤ 1 + t)
    (hρσ : ρ ≤ a ^ (-σ)) (hσ : 0 < σ)
    (hpb : p ≤ C * ρ ^ K * b) (hba : b ≤ a ^ e⁻¹)
    (hCa : 2 * C < a ^ (σ * K / 10)) (htt : t ≤ σ * K / 10) :
    p ^ e' < ρ * a / 2 := by
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha.le
  have hapos : (0 : ℝ) < a := zero_lt_one.trans ha
  have hρK : (0 : ℝ) ≤ ρ ^ K := Real.rpow_nonneg hρ.le _
  have hCe : C ^ e' ≤ C := by
    calc C ^ e' ≤ C ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC he1
      _ = C := Real.rpow_one C
  have hKpos : (0 : ℝ) < K := by
    have hKe : K * e' ≤ K * 1 := mul_le_mul_of_nonneg_left he1 hK0
    linarith
  have hK1 : (0 : ℝ) ≤ K * e' - 1 := by linarith [hK, hKpos]
  have hρpow : ρ ^ (K * e' - 1) ≤ a ^ (-σ * (K * e' - 1)) := by
    calc ρ ^ (K * e' - 1) ≤ (a ^ (-σ)) ^ (K * e' - 1) :=
        Real.rpow_le_rpow hρ.le hρσ hK1
      _ = a ^ (-σ * (K * e' - 1)) := (Real.rpow_mul ha0 _ _).symm
  have hρsplit : ρ ^ (K * e') = ρ ^ (K * e' - 1) * ρ := by
    have h : ρ ^ (K * e') = ρ ^ ((K * e' - 1) + 1) := by
      congr 1
      ring
    rw [h, Real.rpow_add hρ, Real.rpow_one]
  have hstep : p ^ e' ≤ C ^ e' * (ρ ^ (K * e') * a ^ (e⁻¹ * e')) := by
    calc p ^ e' ≤ (C * ρ ^ K * b) ^ e' := Real.rpow_le_rpow hp hpb he'.le
      _ = C ^ e' * (ρ ^ K) ^ e' * b ^ e' := by
        rw [Real.mul_rpow (mul_nonneg (by linarith : (0 : ℝ) ≤ C) hρK) hb,
          Real.mul_rpow (by linarith : (0 : ℝ) ≤ C) hρK]
      _ = C ^ e' * (ρ ^ (K * e') * b ^ e') := by
        rw [Real.rpow_mul hρ.le, mul_assoc]
      _ ≤ C ^ e' * (ρ ^ (K * e') * (a ^ e⁻¹) ^ e') :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb hba he'.le)
            (Real.rpow_nonneg hρ.le _))
          (Real.rpow_nonneg (by linarith) _)
      _ = C ^ e' * (ρ ^ (K * e') * a ^ (e⁻¹ * e')) := by
        rw [Real.rpow_mul ha0]
  have hbound : ρ ^ (K * e') * a ^ (e⁻¹ * e')
      ≤ a ^ (-σ * (K * e' - 1)) * ρ * a ^ (1 + t) := by
    have h1 : ρ ^ (K * e') ≤ a ^ (-σ * (K * e' - 1)) * ρ := by
      rw [hρsplit]
      exact mul_le_mul_of_nonneg_right hρpow hρ.le
    have h2 : a ^ (e⁻¹ * e') ≤ a ^ (1 + t) :=
      Real.rpow_le_rpow_of_exponent_le ha.le (by rwa [mul_comm])
    exact mul_le_mul h1 h2 (Real.rpow_nonneg ha0 _)
      (mul_nonneg (Real.rpow_nonneg ha0 _) hρ.le)
  have hKbound : σ * K / 5 ≤ σ * (K * e' - 1) := by
    linarith [mul_le_mul_of_nonneg_left hK hσ.le]
  have hub : -σ * (K * e' - 1) + (1 + t) ≤ 1 - σ * K / 10 := by
    linarith [hKbound, htt]
  calc p ^ e' ≤ C ^ e' * (ρ ^ (K * e') * a ^ (e⁻¹ * e')) := hstep
    _ ≤ C * (ρ ^ (K * e') * a ^ (e⁻¹ * e')) :=
        mul_le_mul_of_nonneg_right hCe
          (mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.rpow_nonneg ha0 _))
    _ ≤ C * (a ^ (-σ * (K * e' - 1)) * ρ * a ^ (1 + t)) :=
        mul_le_mul_of_nonneg_left hbound (by linarith)
    _ = ρ * (C * a ^ (-σ * (K * e' - 1) + (1 + t))) := by
        rw [show a ^ (-σ * (K * e' - 1)) * ρ * a ^ (1 + t)
            = ρ * (a ^ (-σ * (K * e' - 1)) * a ^ (1 + t)) by ring]
        rw [← Real.rpow_add hapos]
        ring
    _ < ρ * (a ^ (σ * K / 10) / 2 * a ^ (-σ * (K * e' - 1) + (1 + t))) := by
        apply mul_lt_mul_of_pos_left _ hρ
        apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos hapos _)
        linarith
    _ = ρ * (a ^ (σ * K / 10 + (-σ * (K * e' - 1) + (1 + t))) / 2) := by
        congr 1
        rw [div_mul_eq_mul_div, ← Real.rpow_add hapos]
    _ ≤ ρ * (a ^ (1 : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_left _ hρ.le
        have hpow : a ^ (σ * K / 10 + (-σ * (K * e' - 1) + (1 + t)))
            ≤ a ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ha.le (by linarith [hub])
        linarith
    _ = ρ * a / 2 := by rw [Real.rpow_one, mul_div_assoc]

end Thm2

end Nonaveraging
