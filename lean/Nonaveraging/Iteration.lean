import Nonaveraging.Structure
import Nonaveraging.Observation15
import Nonaveraging.Irreducibility

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

/-- **`d̃ > d` numerical core, high-exponent variant.**  Same algebra as
`case_up_pow` but for `0 < e' ≤ 2` — i.e. it also covers the degenerate
regime `α_{d̃} + ζ + incr > 1` — at the price of absorbing `C²` (rather
than `C`) into the largeness hypothesis `2·C·C ≤ a^{c/2}`.

`p ≤ C·a^{−(1−ε)k}·b`, `b ≤ a^{1/e}` imply
`p^{e'} ≤ C^{e'}·a^{e'X} ≤ C²·a^{1−c} ≤ a^{c/2}·a^{1−c}/2 = a^{1−c/2}/2
< a^{1−ε}/2`. -/
theorem case_up_pow_hi {a b p C c ε k e e' : ℝ}
    (ha : 1 < a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hC : 1 ≤ C)
    (he' : 0 < e') (he2 : e' ≤ 2) (_hk : 0 ≤ k)
    (hc : 0 < c) (_hε : 0 ≤ ε) (hεc : ε ≤ c / 4)
    (hobs : e' * (e⁻¹ - (1 - ε) * k) ≤ 1 - c)
    (hpb : p ≤ C * a ^ (-(1 - ε) * k) * b) (hba : b ≤ a ^ e⁻¹)
    (hCa : 2 * C * C ≤ a ^ (c / 2)) :
    p ^ e' < a ^ (1 - ε) / 2 := by
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha.le
  have hapos : (0 : ℝ) < a := zero_lt_one.trans ha
  have hu : (0 : ℝ) ≤ a ^ (-(1 - ε) * k) := Real.rpow_nonneg ha0 _
  have hCe : C ^ e' ≤ C * C := by
    have h := Real.rpow_le_rpow_of_exponent_le hC he2
    have e2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [e2, Real.rpow_natCast, pow_two] at h
    exact h
  have hstep : p ^ e' ≤ C ^ e' * a ^ (-(1 - ε) * k * e')
      * a ^ (e⁻¹ * e') := by
    calc p ^ e' ≤ (C * a ^ (-(1 - ε) * k) * b) ^ e' :=
        Real.rpow_le_rpow hp hpb he'.le
      _ = C ^ e' * (a ^ (-(1 - ε) * k)) ^ e' * b ^ e' := by
        rw [Real.mul_rpow (mul_nonneg (by linarith : (0 : ℝ) ≤ C) hu) hb,
          Real.mul_rpow (by linarith : (0 : ℝ) ≤ C) hu]
      _ ≤ C ^ e' * (a ^ (-(1 - ε) * k)) ^ e' * (a ^ e⁻¹) ^ e' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb hba he'.le)
          (mul_nonneg (Real.rpow_nonneg (by linarith) _)
            (Real.rpow_nonneg (Real.rpow_nonneg ha0 _) _))
      _ = C ^ e' * a ^ (-(1 - ε) * k * e') * a ^ (e⁻¹ * e') := by
        rw [← Real.rpow_mul ha0, ← Real.rpow_mul ha0]
  have hcomb : a ^ (-(1 - ε) * k * e') * a ^ (e⁻¹ * e')
      = a ^ (e' * (e⁻¹ - (1 - ε) * k)) := by
    rw [← Real.rpow_add hapos]
    congr 1
    ring
  calc p ^ e' ≤ C ^ e' * a ^ (-(1 - ε) * k * e') * a ^ (e⁻¹ * e') :=
      hstep
    _ = C ^ e' * (a ^ (-(1 - ε) * k * e') * a ^ (e⁻¹ * e')) :=
      mul_assoc _ _ _
    _ = C ^ e' * a ^ (e' * (e⁻¹ - (1 - ε) * k)) := by rw [hcomb]
    _ ≤ (C * C) * a ^ (1 - c) :=
      mul_le_mul hCe
        (Real.rpow_le_rpow_of_exponent_le ha.le hobs)
        (Real.rpow_nonneg ha0 _)
        (by nlinarith [hC] : (0 : ℝ) ≤ C * C)
    _ ≤ (a ^ (c / 2) / 2) * a ^ (1 - c) :=
      mul_le_mul_of_nonneg_right (by linarith : C * C ≤ a ^ (c / 2) / 2)
        (Real.rpow_nonneg ha0 _)
    _ = a ^ (1 - c / 2) / 2 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hapos,
        show c / 2 + (1 - c) = 1 - c / 2 by ring]
    _ < a ^ (1 - ε) / 2 := by
      have hpow : a ^ (1 - c / 2) < a ^ (1 - ε) :=
        Real.rpow_lt_rpow_of_exponent_lt ha (by linarith)
      linarith

/-- **Case 3, shrink sub-case, high-exponent variant.**  Same algebra as
`case_shrink_pow` but for `0 < e' ≤ 2` (the actual `d̃ = d` regime has
`e' = α_d + ζ + incr` which may exceed `1`), absorbing `C²` via the
stronger largeness `2·C·C < a^{σK/10}`. -/
theorem case_shrink_pow_sq {a b p C ρ K σ t e e' : ℝ}
    (ha : 1 < a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hC : 1 ≤ C)
    (hρ : 0 < ρ) (he' : 0 < e') (he2 : e' ≤ 2)
    (hK0 : 0 ≤ K) (hK : K / 5 ≤ K * e' - 1)
    (ht : e' * e⁻¹ ≤ 1 + t)
    (hρσ : ρ ≤ a ^ (-σ)) (hσ : 0 < σ)
    (hpb : p ≤ C * ρ ^ K * b) (hba : b ≤ a ^ e⁻¹)
    (hCa : 2 * C * C < a ^ (σ * K / 10)) (htt : t ≤ σ * K / 10) :
    p ^ e' < ρ * a / 2 := by
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha.le
  have hapos : (0 : ℝ) < a := zero_lt_one.trans ha
  have hρK : (0 : ℝ) ≤ ρ ^ K := Real.rpow_nonneg hρ.le _
  have hCe : C ^ e' ≤ C * C := by
    have h := Real.rpow_le_rpow_of_exponent_le hC he2
    have e2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [e2, Real.rpow_natCast, pow_two] at h
    exact h
  have hKpos : (0 : ℝ) < K := by
    have hKe : K * e' ≤ K * 2 := mul_le_mul_of_nonneg_left he2 hK0
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
    _ ≤ (C * C) * (ρ ^ (K * e') * a ^ (e⁻¹ * e')) :=
        mul_le_mul_of_nonneg_right hCe
          (mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.rpow_nonneg ha0 _))
    _ ≤ (C * C) * (a ^ (-σ * (K * e' - 1)) * ρ * a ^ (1 + t)) :=
        mul_le_mul_of_nonneg_left hbound (by nlinarith [hC])
    _ = ρ * ((C * C) * a ^ (-σ * (K * e' - 1) + (1 + t))) := by
        rw [show a ^ (-σ * (K * e' - 1)) * ρ * a ^ (1 + t)
            = ρ * (a ^ (-σ * (K * e' - 1)) * a ^ (1 + t)) by ring]
        rw [← Real.rpow_add hapos]
        ring
    _ < ρ * ((a ^ (σ * K / 10) / 2) *
        a ^ (-σ * (K * e' - 1) + (1 + t))) := by
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

/-! ### The §4 step: leaf interface

The remaining content of Theorem 2 is a single iteration step: from a
non-averaging counterexample `A ⊆ B ⊆ ℤ^d` at exponent `α_d + ζ`, produce
a new one at a strictly larger slack.  The numerics for the three cases
(`d̃ > d`, `d̃ < d`, `d̃ = d` with `|Ã| ≤ |A|^{1-σ}`) are `case_up_pow`,
`case_down_pow`, `case_shrink_pow` above.  This section packages the data
the unresolved paper lemmas supply, at exactly the granularity those case
lemmas consume it.

* `coeffBox_isInterval`, `dim_lt_of_slack`: small geometric/numeric
  helpers needed by the assembly.
* `Lemma10Data`: the faithful output of Lemma 10 (compare
  `Nonaveraging/Structure.lean`'s `irreduciblization`).  The two
  strengthenings relative to the current gap-statement are the `d̃`
  index of the ambient dimension and, crucially, a *usable* lower bound
  `|Ã|/2 ≤ |ϕ(Â)|` on the embedded image — the present
  `SubSumWitness.hAhcard` only gives `|Â| ≥ |Ã| − ct⁻¹|Ã|/log|Ã|` with an
  uncontrolled `ct`, which is precisely what `irreduciblization`'s
  vacuous `SubSumWitness.degenerate` exploit (`Â = ∅`, `d̃ = 0`)
  fails to provide.  The intended discharge is
  `Nonaveraging/Irreducibility.lean`'s `irreduciblization_faithful`.
* `lemma10_data`: existence of the bundle for every large non-averaging
  `A ⊆ B` with `|B| ≤ |A|⁴` and `d ≤ D₀` (the `|A|^{-1/3} ≤ γ` largeness
  side condition of `irreduciblization` is folded into the existential
  `γ`, and the dimension bound `D₀` accommodates the dimension-dependent
  constants of `irreduciblization_faithful`, from which the bundle is
  now discharged).
* `residual_step`: the cases the up-move numerics do not cover —
  `d̃ < d` (whose increment `α_d − α_{d̃} − ε` is uniform but whose
  counterexample verification has margin `ε(1−e)/e`, degenerating as the
  exponent `e → 1`), `d̃ = d` (the shrink sub-case is
  `case_shrink_pow`; the non-shrink sub-case is where
  `embedded_in_mu_convex_position` (Theorem 4), `density_increment`
  (Lemma 1) and the discrete John lemma (Lemma 7, currently absent)
  plug in), and `d̃ > d` with `α_{d̃} + ζ` already `≥ 1 − incr`.

  Important subtlety documented in `round3_thm2_report.md`: in the
  `d̃ = d` case the paper's increment is `θ'(ζ,d,|A|)`, which decays like
  `log log log |A| / log |A|` — it is *not* bounded below by a constant.
  Hence the step is stated for an arbitrary `incr ≤ min ι (θ |A|)` with
  `θ |A|` of the paper's scale `≍ 1/log |A|`, and the fixed-slack
  `IterationStepProp` of `UpperBound.lean` is replaced there by
  `IterationStepPropD`. -/

/-- The canonical coefficient box of a GAP is an interval box:
`Ico 0 w = Icc 0 (w − 1)` in `ℤ` coordinatewise. -/
theorem coeffBox_isInterval {ℓ d : ℕ} (P : GAP ℓ d) :
    P.coeffBox.IsInterval := by
  intro i
  refine ⟨0, (P.width i : ℤ) - 1, ?_⟩
  ext x
  simp only [GAP.coeffBox, Finset.mem_Ico, Finset.mem_Icc]
  omega

/-- Slack `ζ > 0` bounds the ambient dimension of a counterexample:
`α_d + ζ < 1` forces `d < 2/ζ`. -/
theorem dim_lt_of_slack {d : ℕ} (hd : 1 ≤ d) {ζ : ℝ} (hζ : 0 < ζ)
    (h : αd d + ζ < 1) : (d : ℝ) < 2 / ζ := by
  rcases eq_or_ne d 1 with rfl | hd1
  · rw [αd_one] at h
    rw [lt_div_iff₀ hζ, Nat.cast_one, one_mul]
    linarith
  · rw [αd_of_ne_one hd1] at h
    have hdp : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    have h' : ((d : ℝ) - 1) / ((d : ℝ) + 1) < 1 - ζ := by linarith
    rw [div_lt_iff₀ hdp] at h'
    have h2 : (d : ℝ) * ζ < 2 := by nlinarith [h']
    rwa [lt_div_iff₀ hζ]

/-- The conclusion of one §4 iteration step: a new non-averaging
counterexample `A' ⊆ B' ⊆ ℤ^{d'}` at exponent `α_{d'} + ζ'` with the slack
incremented by `incr`, with `|A'| ≤ |A|` (moves never grow the set), the
polynomial retention `|A|^q ≤ |A'|`, and a reported multiplicative
retention factor `ρ` (`ρ·|A| ≤ |A'|`, `ρ > 0`) — the quantity the paper's
final bookkeeping paragraph tracks (`∏ ρⱼ ≥ |A|^{-c/2}`).  Packaged as an
`abbrev` so the existential is transparent at use sites. -/
abbrev StepConclusion {d : ℕ} (A : Finset (Fin d → ℤ))
    (ζ incr q : ℝ) : Prop :=
  ∃ (d' : ℕ) (A' : Finset (Fin d' → ℤ)) (B' : GAP.Box d') (ζ' ρ : ℝ),
    1 ≤ d' ∧ B'.IsInterval ∧ NonAveraging A' ∧ A' ⊆ B'.toFinset ∧
    A'.card ≤ A.card ∧ ζ + incr ≤ ζ' ∧
    (B'.card : ℝ) ^ (αd d' + ζ') < (A'.card : ℝ) ∧
    (A.card : ℝ) ^ q ≤ (A'.card : ℝ) ∧ ρ * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
    0 < ρ

/-- The conclusion of the non-shrink `d̃ = d` density-increment step
(`residual_density_step`): a `StepConclusion` whose witness stays in the
*same* ambient dimension `d`, and which additionally reports `ρ ≤ 1`
and the diagonal box-shrinkage `|B'| ≤ ρ^κ·|B|` — the two extra fields
the bookkeeping-enriched step `StepPropB` (UpperBound.lean) tracks for
`d' = d` steps.  Faithfully, the §4 pipeline (Theorem 4 → Lemma 1 →
Lemma 7) produces `A' ⊆ B̃ ⊆ ℤ^d` with `|B̃| ≪ η·ρ̃^K·|B|`, `η ≤ 1`; the
slack `2κ ≤ K` and largeness absorb the implied constant, giving
`|B̃| ≤ ρ^κ·|B|` for `ρ` the reported retention factor.  Packaged as an
`abbrev` so the existential is transparent at use sites. -/
abbrev StepConclusionD {d : ℕ} (A : Finset (Fin d → ℤ)) (B : GAP.Box d)
    (ζ incr q κ : ℝ) : Prop :=
  ∃ (A' : Finset (Fin d → ℤ)) (B' : GAP.Box d) (ζ' ρ : ℝ),
    B'.IsInterval ∧ NonAveraging A' ∧ A' ⊆ B'.toFinset ∧
    A'.card ≤ A.card ∧ ζ + incr ≤ ζ' ∧
    (B'.card : ℝ) ^ (αd d + ζ') < (A'.card : ℝ) ∧
    (A.card : ℝ) ^ q ≤ (A'.card : ℝ) ∧ ρ * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
    0 < ρ ∧ ρ ≤ 1 ∧ (B'.card : ℝ) ≤ ρ ^ κ * (B.card : ℝ)

/-- **Lemma-10 output bundle** (faithful form).  For the parameters
`ε K`, a non-averaging `A ⊆ B ⊆ ℤ^d` with `|B| ≤ |A|⁴` produces a derived
`Ã ⊆ ℤⁿ` with canonical witness `Wt` of dimension `d̃` such that:

* `Ã` is obtained from `A` by `DerivedFrom`-moves (hence is
  non-averaging and `|Ã| ≤ |A|`),
* `|Ã| ≥ |A|^{1-ε}` and `|ϕ(Â)| ≥ |Ã|/2`,
* `Wt` is `(δ,γ)`-irreducible for the existential `δ, γ` with
  `γ ≤ δ^K`, `4δ < 1` and `|A|^{-1/3} ≤ γ`,
* `|A|^{ε/4} ≥ 2C` (the `C`-absorption the step lemmas need, folded
  into the largeness threshold), and
* `P̃ = P(Ã)` satisfies the three bounds of Lemma 10.

Note `n` (the ambient dimension of `Ã`) and `d̃` (the GAP dimension of the
witness) are *separately* existentially quantified, matching
`irreduciblization_faithful`; the step lemmas only ever use the
coefficient-space data `Wt.imageAh ⊆ ℤ^{d̃}` and `Wt.P.coeffBox`. -/
def Lemma10Data {d : ℕ} (A : Finset (Fin d → ℤ)) (B : GAP.Box d)
    (ε K : ℝ) : Prop :=
  ∃ (n dt : ℕ) (At : Finset (Fin n → ℤ)) (ct : ℝ)
    (Wt : SubSumWitness At ct dt) (c' δ γ C : ℝ),
    0 < δ ∧ 4 * δ < 1 ∧ 0 < γ ∧ γ ≤ δ ^ K ∧
    (A.card : ℝ) ^ (-(1 : ℝ) / 3) ≤ γ ∧
    DerivedFrom A δ At ∧ 1 ≤ C ∧ 2 * C ≤ (A.card : ℝ) ^ (ε / 4) ∧
    (A.card : ℝ) ^ (1 - ε) ≤ (At.card : ℝ) ∧
    (At.card : ℝ) / 2 ≤ (Wt.imageAh.card : ℝ) ∧
    Irreducible Wt c' δ γ ∧
    (d < dt → (Wt.P.coeffBox.card : ℝ) ≤
      C * (A.card : ℝ) ^ (-(1 - ε) * ((dt : ℝ) - d)) * B.card) ∧
    (dt = d → (Wt.P.coeffBox.card : ℝ) ≤
      C * ((At.card : ℝ) / (A.card : ℝ)) ^ K * B.card) ∧
    (dt < d → (Wt.P.coeffBox.card : ℝ) ≤ C * B.card)

/-- **Lemma-10 leaf** (`irreduciblization`, faithful form): every
sufficiently large non-averaging `A ⊆ B` with `|B| ≤ |A|⁴` in ambient
dimension `d ≤ D₀` admits the bundle `Lemma10Data`.

This is discharged by `irreduciblization_faithful`
(`Nonaveraging/Irreducibility.lean`), which produces *universal*
constants `c₀(d)`, `c'(d)`, `C(d)`, `D(d)`, `N(d)` per ambient
dimension.  The bridging steps:

* the move parameters are instantiated to the constants `δ = 1/2` and
  `γ = (1/2)^K` (`γ ≤ δ^K` is then an equality); the faithful lemma's
  side condition `|A|^{-1/3} ≤ γ` becomes the largeness `|A| ≥ γ^{-3}`;
* `|Ã|/2 ≤ |ϕ(Ât)| = |Ât|` follows from `half_le_Ah_card` once
  `2c₀⁻¹ ≤ log|Ã|`, which holds since `|Ã| ≥ |A|^{1-ε}` and
  `|A| ≥ exp(2c₀⁻¹/(1-ε))`;
* `|P̃.coeffBox| = |P̃.toFinset|` is `witness_card_coeffBox`
  (`kP̃` proper ⇒ `P̃` proper), and `C(d)` is upgraded to `max (C d) 1`;
* the bound `D₀` on the ambient dimension is needed because the faithful
  constants vary with `d`: `thm2_step` supplies `D₀ = ⌈2/ζ₀⌉` via
  `dim_lt_of_slack`. -/
theorem lemma10_data {ε K : ℝ} (hε : 0 < ε) (hε3 : ε < 1 / 3)
    (_hK : 0 < K) (D₀ : ℕ)
    (hKbig : (2 : ℝ) * (2 * D₀ + 6) / ε < K) :
    ∃ N : ℕ, ∀ {d : ℕ} {A : Finset (Fin d → ℤ)} {B : GAP.Box d},
      d ≤ D₀ → B.IsInterval → NonAveraging A → A ⊆ B.toFinset →
      (B.card : ℝ) ≤ (A.card : ℝ) ^ (4 : ℝ) → N ≤ A.card →
      Lemma10Data A B ε K := by
  have hβ4 : (1 : ℝ) < 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 8 := by norm_num
  have hδ1 : (1 / 8 : ℝ) < 1 := by norm_num
  have hγ : (0 : ℝ) < (1 / 8 : ℝ) ^ K := Real.rpow_pos_of_pos hδ _
  -- the faithful constants are dimension-dependent; collect them per `d`.
  -- `hKbig` supplies each `d ≤ D₀` with the eq.-(10) largeness of `K`
  -- (at `ℓ = d`, `β = 4` the threshold is `2(2d+6)/ε ≤ 2(2D₀+6)/ε < K`).
  have hKbigd : ∀ {d : ℕ}, d ≤ D₀ →
      (2 : ℝ) * (2 * (d : ℝ) + 4 + 2) / ε < K := by
    intro d hd
    have hd' : (d : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hd
    have h1 : (2 : ℝ) * (2 * (d : ℝ) + 4 + 2) ≤ 2 * (2 * (D₀ : ℝ) + 6) := by
      linarith
    calc (2 : ℝ) * (2 * (d : ℝ) + 4 + 2) / ε
        ≤ (2 : ℝ) * (2 * (D₀ : ℝ) + 6) / ε :=
          div_le_div_of_nonneg_right h1 hε.le
      _ < K := hKbig
  have hf := fun (d : ℕ) (hd : d ≤ D₀) ↦
    irreduciblization_faithful (ℓ := d) hβ4 hε hε3 hδ hδ1 hγ (le_refl _)
      (hKbigd hd)
  choose c₀ c' Cf Df Nf hfA using hf
  -- per-dimension threshold: the faithful `Nf d`, the largeness
  -- `|A| ≥ γ^{-3}` making `|A|^{-1/3} ≤ γ`,
  -- `|A| ≥ exp(2c₀⁻¹/(1-ε))` making `2c₀⁻¹ ≤ (1-ε)·log|A| ≤ log|Ã|`, and
  -- `|A| ≥ (2·max(C d,1))^{4/ε}` making `2C ≤ |A|^{ε/4}`.
  refine ⟨max 4 ((Finset.range (D₀ + 1)).attach.sup fun x ↦
    max (Nf x.1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp x.2)))
      (max ⌈((1 / 8 : ℝ) ^ K) ^ (-3 : ℝ)⌉₊
        (max ⌈Real.exp (2 * (c₀ x.1 (Nat.lt_succ_iff.mp
            (Finset.mem_range.mp x.2)))⁻¹ / (1 - ε))⌉₊
          ⌈(2 * max (Cf x.1 (Nat.lt_succ_iff.mp
            (Finset.mem_range.mp x.2))) 1 : ℝ) ^ (4 / ε : ℝ)⌉₊))), ?_⟩
  intro d A B hdD hBint hNA hsub hB hN
  have hmem : d ∈ Finset.range (D₀ + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hdD)
  have hTd : max (Nf d hdD) (max ⌈((1 / 8 : ℝ) ^ K) ^ (-3 : ℝ)⌉₊
      (max ⌈Real.exp (2 * (c₀ d hdD)⁻¹ / (1 - ε))⌉₊
        ⌈(2 * max (Cf d hdD) 1 : ℝ) ^ (4 / ε : ℝ)⌉₊)) ≤ A.card := by
    have h1 := Finset.le_sup (s := (Finset.range (D₀ + 1)).attach)
      (f := fun x : {x // x ∈ Finset.range (D₀ + 1)} ↦
        max (Nf x.1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp x.2)))
          (max ⌈((1 / 8 : ℝ) ^ K) ^ (-3 : ℝ)⌉₊
            (max ⌈Real.exp (2 * (c₀ x.1 (Nat.lt_succ_iff.mp
                (Finset.mem_range.mp x.2)))⁻¹ / (1 - ε))⌉₊
              ⌈(2 * max (Cf x.1 (Nat.lt_succ_iff.mp
                (Finset.mem_range.mp x.2))) 1 : ℝ) ^ (4 / ε : ℝ)⌉₊)))
      (Finset.mem_attach _ ⟨d, hmem⟩)
    exact h1.trans (le_trans (le_max_right _ _) hN)
  have hNf : Nf d hdD ≤ A.card := (le_max_left _ _).trans hTd
  have hγ3N : ⌈((1 / 8 : ℝ) ^ K) ^ (-3 : ℝ)⌉₊ ≤ A.card :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hTd
  have hexpN : ⌈Real.exp (2 * (c₀ d hdD)⁻¹ / (1 - ε))⌉₊ ≤ A.card :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))).trans hTd
  have hC4N : ⌈(2 * max (Cf d hdD) 1 : ℝ) ^ (4 / ε : ℝ)⌉₊ ≤ A.card :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))).trans hTd
  have h4 : (4 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast (le_trans (le_max_left _ _) hN)
  have hApos : (0 : ℝ) < (A.card : ℝ) := by linarith
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  -- `|A| ≥ γ⁻³` gives `|A|^{1/3} ≥ γ⁻¹`, i.e. `|A|^{-1/3} ≤ γ`.
  have hγ3le : ((1 / 8 : ℝ) ^ K) ^ (-3 : ℝ) ≤ (A.card : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hγ3N)
  have hr3 : ((1 / 8 : ℝ) ^ K) ^ (-1 : ℝ) ≤
      (A.card : ℝ) ^ (1 / 3 : ℝ) := by
    have e : ((1 / 8 : ℝ) ^ K) ^ (-1 : ℝ)
        = (((1 / 8 : ℝ) ^ K) ^ (-3 : ℝ)) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_mul hγ.le]
      congr 1
      ring
    rw [e]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hγ.le _) hγ3le
      (by norm_num)
  have hAγ : (A.card : ℝ) ^ (-(1 : ℝ) / 3) ≤ (1 / 8 : ℝ) ^ K := by
    rw [show (-(1 : ℝ) / 3 : ℝ) = -((1 : ℝ) / 3) by ring,
      Real.rpow_neg hApos.le]
    have h2 : ((A.card : ℝ) ^ (1 / 3 : ℝ))⁻¹ ≤
        (((1 / 8 : ℝ) ^ K) ^ (-1 : ℝ))⁻¹ :=
      (inv_le_inv₀ (Real.rpow_pos_of_pos hApos _)
        (Real.rpow_pos_of_pos hγ _)).mpr hr3
    rwa [Real.rpow_neg_one, inv_inv] at h2
  -- apply the faithful lemma at dimension `d`
  obtain ⟨_hc₀, _hc', _hCf, hfB⟩ := hfA d hdD
  obtain ⟨n, At, dt, Wt, hder, _hNAt, hAtcard, _hdtD, hirr, hup, hsame,
    hdown⟩ := hfB hBint hNA hsub hB hAγ hNf
  -- `2c₀⁻¹ ≤ (1-ε)·log|A| ≤ log|Ã|`, hence `|Ât| ≥ |Ã|/2`.
  have hlogA : 2 * (c₀ d hdD)⁻¹ ≤ (1 - ε) * Real.log (A.card : ℝ) := by
    have hexp : Real.exp (2 * (c₀ d hdD)⁻¹ / (1 - ε)) ≤ (A.card : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hexpN)
    have h1 : 2 * (c₀ d hdD)⁻¹ / (1 - ε) ≤ Real.log (A.card : ℝ) :=
      calc 2 * (c₀ d hdD)⁻¹ / (1 - ε)
          = Real.log (Real.exp (2 * (c₀ d hdD)⁻¹ / (1 - ε))) :=
            (Real.log_exp _).symm
        _ ≤ Real.log (A.card : ℝ) :=
            Real.log_le_log (Real.exp_pos _) hexp
    calc 2 * (c₀ d hdD)⁻¹ ≤ Real.log (A.card : ℝ) * (1 - ε) :=
          (div_le_iff₀ h1ε).mp h1
      _ = (1 - ε) * Real.log (A.card : ℝ) := mul_comm _ _
  have hlogAt : 2 * (c₀ d hdD)⁻¹ ≤ Real.log (At.card : ℝ) :=
    calc 2 * (c₀ d hdD)⁻¹ ≤ (1 - ε) * Real.log (A.card : ℝ) := hlogA
      _ = Real.log ((A.card : ℝ) ^ (1 - ε)) :=
          (Real.log_rpow hApos _).symm
      _ ≤ Real.log (At.card : ℝ) :=
          Real.log_le_log (Real.rpow_pos_of_pos hApos _) hAtcard
  have hAh2 : (At.card : ℝ) / 2 ≤ (Wt.imageAh.card : ℝ) := by
    rw [Wt.card_imageAh]
    exact half_le_Ah_card Wt hlogAt
  -- `|A| ≥ (2C)^{4/ε}` gives `2C ≤ |A|^{ε/4}`.
  have hC4 : ((2:ℝ) * max (Cf d hdD) 1) ^ (4 / ε : ℝ) ≤ (A.card : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hC4N)
  have hCa : 2 * max (Cf d hdD) 1 ≤ (A.card : ℝ) ^ (ε / 4 : ℝ) := by
    have hCpos : (0 : ℝ) ≤ 2 * max (Cf d hdD) 1 := by positivity
    have h2 : ((2 * max (Cf d hdD) 1 : ℝ) ^ (4 / ε : ℝ)) ^ (ε / 4 : ℝ)
        = 2 * max (Cf d hdD) 1 := by
      rw [← Real.rpow_mul hCpos]
      rw [show (4 / ε : ℝ) * (ε / 4) = 1 by
        rw [div_mul_div_comm, show (4 : ℝ) * ε = ε * 4 from mul_comm _ _,
          div_self (mul_ne_zero hε.ne' (by norm_num))]]
      exact Real.rpow_one _
    rw [← h2]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hCpos _) hC4
      (by positivity : (0 : ℝ) ≤ ε / 4)
  -- assemble the bundle with `C := max (Cf d) 1`
  refine ⟨n, dt, At, c₀ d hdD, Wt, c' d hdD, 1 / 8, (1 / 8 : ℝ) ^ K,
    max (Cf d hdD) 1, hδ, by norm_num, hγ, le_refl _, hAγ, hder,
    le_max_right _ _, hCa, hAtcard, hAh2, hirr, ?_, ?_, ?_⟩
  · intro hlt
    rw [witness_card_coeffBox Wt]
    exact (hup hlt).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _))
  · intro heq
    rw [witness_card_coeffBox Wt]
    exact (hsame heq).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _))
      (Nat.cast_nonneg _))
  · intro hlt
    rw [witness_card_coeffBox Wt]
    exact (hdown hlt).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))

/-- **Case 1 assembly** (`d̃ > d`, genuine, gap-free): under the
Lemma-10 up-move bound `|P̃| = ∏ w̃ᵢ ≤ C·|A|^{-(1-ε)(d̃-d)}·|B|` and the
Observation-15 uniform bound, the embedded image `Ā = ϕ_{P̃}(Â)` inside
`B' = coeffBox P̃` is a non-averaging counterexample at slack
`ζ + incr`, provided `incr ≤ c₀/16`, `α_{d̃} + ζ + incr ≤ 1`, and the
largeness thresholds `2C ≤ |A|^{c₀/8}`, `2 ≤ |A|^ε` hold.  The retained
factor is `ρ = |A|^{-ε}/2`. -/
theorem step_up {d n dt : ℕ} {A : Finset (Fin d → ℤ)} {B : GAP.Box d}
    {At : Finset (Fin n → ℤ)} {ct : ℝ} (Wt : SubSumWitness At ct dt)
    {δ ζ incr ε C c₀ q : ℝ} (hder : DerivedFrom A δ At)
    (hd : 1 ≤ d) (hdt : d < dt) (hζ : 0 < ζ)
    (hNA : NonAveraging A)
    (hincr : 0 < incr) (hincrc : incr ≤ c₀ / 16)
    (hαe' : αd dt + ζ + incr ≤ 1)
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
    (hεpow : (2 : ℝ) ≤ (A.card : ℝ) ^ ε) :
    StepConclusion A ζ incr q := by
  set a : ℝ := (A.card : ℝ)
  have ha1 : (1 : ℝ) ≤ a := ha.le
  have ha0 : (0 : ℝ) < a := by linarith
  have he4 : (1 / 4 : ℝ) ≤ αd d + ζ := (αd_quarter_le hd).trans (by linarith)
  have hinv4 : (αd d + ζ)⁻¹ ≤ 4 := by
    calc (αd d + ζ)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he4
      _ = 4 := by norm_num
  have hk : (0 : ℝ) < (dt : ℝ) - (d : ℝ) :=
    sub_pos.mpr (by exact_mod_cast hdt)
  have he' : (0 : ℝ) < αd dt + (ζ + incr) := by
    have h1dt : 1 ≤ dt := by omega
    linarith [αd_quarter_le h1dt, hincr]
  -- the Observation-15 bound at slack `ζ + incr` (the bracket is `≤ 4`,
  -- absorbing the extra `incr·X ≤ c₀/4`).
  have hXnn : (0 : ℝ) ≤ (1 - ε) * ((dt : ℝ) - (d : ℝ)) :=
    mul_nonneg (by linarith) hk.le
  have hX : incr * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)))
      ≤ c₀ / 4 := by
    have hle : (αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)) ≤ 4 := by
      linarith
    calc incr * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)))
        ≤ incr * 4 := mul_le_mul_of_nonneg_left hle hincr.le
      _ ≤ c₀ / 4 := by linarith
  have hobs : (αd dt + (ζ + incr)) *
      ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) ≤ 1 - c₀ / 2 := by
    have hde : (αd dt + (ζ + incr)) *
        ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) =
        (αd dt + ζ) * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) +
        incr * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) := by ring
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
  have hmain := case_up_pow (a := a) (b := (B.card : ℝ))
    (p := (Wt.P.coeffBox.card : ℝ)) (C := C) (e := αd d + ζ)
    (e' := αd dt + (ζ + incr)) (k := (dt : ℝ) - (d : ℝ)) (ε := ε)
    (c := c₀ / 2) ha (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC he'
    (by linarith : αd dt + (ζ + incr) ≤ 1) hk.le (by linarith) hε.le
    hεc' hobs hp hba hCa'
  -- assemble `StepConclusion` with `A' = ϕ(Â)`, `B' = coeffBox P̃`,
  -- `ζ' = ζ + incr`, `ρ = a^{-ε}/2`.
  refine ⟨dt, Wt.imageAh, Wt.P.coeffBox, ζ + incr, a ^ (-ε) / 2,
    by omega, coeffBox_isInterval _, ?_, Wt.imageAh_subset_coeffBox, ?_,
    le_rfl, ?_, ?_, ?_, ?_⟩
  · -- non-averaging: `DerivedFrom` moves preserve it, `Â ⊆ Ã` inherits,
    -- and `ϕ` transports it.
    exact GAP.nonAveraging_ptCoeffImage _
      (fun _ ha ↦ Wt.hsub (Finset.mem_union_left _ ha))
      (NonAveraging.mono Wt.hAh (hder.nonAveraging hNA))
  · -- `|A'| ≤ |A|`
    rw [Wt.card_imageAh]
    exact (Finset.card_le_card Wt.hAh).trans hder.card_le
  · -- `(B'.card)^{α_{d'} + ζ'} < |A'|`
    calc (Wt.P.coeffBox.card : ℝ) ^ (αd dt + (ζ + incr))
        < a ^ (1 - ε) / 2 := hmain
      _ ≤ (At.card : ℝ) / 2 := by linarith
      _ ≤ (Wt.imageAh.card : ℝ) := hAh
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

/-- **Non-shrink `d̃ = d` leaf** (the density-increment step).  In the
`d̃ = d` case with `ρ = |Ã|/|A|` not small (`|A|^{-σ} < ρ`), the paper
produces the new counterexample by: `embedded_in_mu_convex_position`
(Theorem 4, applied to `Ā = ϕ_{P̃}(Â)` at `μ = ρ^K` inside `conv B̄` —
the irreducibility `Wt` supplies the `(δ,γ)` input, `|A|^{-1/3} ≤ γ` and
the largeness `N ≤ |A|` absorb Theorem 4's threshold), `density_increment`
(Lemma 1, giving `η ∈ [μ, μ^τ]` and a convex `Ω' ⊆ conv B̄` capturing an
`η^{(d-1)/(d+1)+ε'}`-fraction of `Ā`), and `discrete_john_strong`
(Lemma 7) to replace `Ω'` by an integer box `B̃` with
`|B̃| ≪ η·ρ^K·|B|`.  The resulting counterexample sits at increment
`θ'(ζ,d,|A|) ≍ log log log |A| / log |A|` — hence the hypothesis
`incr ≤ ι / log |A|`.

**This is the single remaining gap of the iteration step.**

Round-14 note — the existing lemmas do not assemble to this goal:
`embedded_in_mu_convex_position` and `density_increment` produce
*existential* thresholds (`∃ N`, `∃ δ₀, ∃ M`) that cannot be
discharged against the fixed `A` here (only `|Ã| ≥ |A|^{1-ε}` and
`|A| ≥ γ^{-3}` are available, and `N`, `δ₀`, `M` are opaque functions
of the parameters); `DerivedFrom.exists_interval_box` only supplies the
crude `|B'| ≤ 2^{|A|} + |B|` box for `Ã` (the polynomial bound needs
Lemmas 6–8); and no lemma converts the Lemma-7 `GAP.centered` output
inside `Ω'` into a `GAP.Box` with `|B̃| ≪ ρ̃^K |B|`.  The bare bound
`hp` alone cannot produce the counterexample either:
`|P̃|^{α_d+ζ+incr} < |Ã̂|` would need
`2C^{e'}ρ̃^{Ke'-1} < |A|^{-(e'/e - 1)}`, whose LHS is `≥ 1` while the
RHS is `< 1`.

Round-15 note — the conclusion was strengthened from `StepConclusion`
to `StepConclusionD` (same ambient dimension `d`, `ρ ≤ 1`, and the
diagonal box-shrinkage `|B'| ≤ ρ^κ·|B|` at slack `2κ ≤ K`), so that the
same leaf serves both `residual_step` (which projects the extra fields)
and `residual_step_bookkeeping` (which needs them for `StepConclusionB`).
The strengthened form is what the paper's pipeline delivers: the new
counterexample `A' ⊆ B̃ ⊆ ℤ^{d}` lives in dimension `d` with
`|B̃| ≪ η·ρ̃^K·|B|`, `η ≤ 1`, and `ρ ≤ μ^{c(d)}` absorbs constants into
`ρ^κ` once `K ≥ 2κ` and `|A|` is large.  The two extra hypotheses
`hκ`, `hKκ` record that parameter relation. -/
theorem residual_density_step
    {d n : ℕ} {A : Finset (Fin d → ℤ)} {B : GAP.Box d}
    {At : Finset (Fin n → ℤ)} {ct c' δ γ C σ : ℝ}
    (Wt : SubSumWitness At ct d)
    {ζ incr q ε K ι κ : ℝ} {N : ℕ}
    (hd : 1 ≤ d) (hζ : 0 < ζ) (hαζ : αd d + ζ < 1)
    (hBint : B.IsInterval) (hNA : NonAveraging A)
    (hsub : A ⊆ B.toFinset)
    (hcex : (B.card : ℝ) ^ (αd d + ζ) < (A.card : ℝ))
    (hN : N ≤ A.card)
    (hε : 0 < ε) (hε1 : ε < 1) (hK : 100 ≤ K)
    (hq0 : 0 < q) (hq : q ≤ 1 - 2 * ε)
    (hι : 0 < ι) (hincr : 0 < incr)
    (hincrι : incr ≤ ι) (hincrθ : incr ≤ ι / Real.log (A.card : ℝ))
    (hεpow : (2 : ℝ) ≤ (A.card : ℝ) ^ ε)
    (hδ : 0 < δ) (hδ4 : 4 * δ < 1) (hγ : 0 < γ) (hγδ : γ ≤ δ ^ K)
    (hγa : (A.card : ℝ) ^ (-(1 : ℝ) / 3) ≤ γ)
    (hder : DerivedFrom A δ At) (hC : 1 ≤ C)
    (hCa : 2 * C ≤ (A.card : ℝ) ^ (ε / 4))
    (hAt : (A.card : ℝ) ^ (1 - ε) ≤ (At.card : ℝ))
    (hAh : (At.card : ℝ) / 2 ≤ (Wt.imageAh.card : ℝ))
    (hirr : Irreducible Wt c' δ γ)
    (hp : (Wt.P.coeffBox.card : ℝ) ≤
      C * ((At.card : ℝ) / (A.card : ℝ)) ^ K * (B.card : ℝ))
    (hσ : 0 < σ)
    (hρ : (A.card : ℝ) ^ (-σ) < (At.card : ℝ) / (A.card : ℝ))
    (hκ : 0 < κ) (hKκ : 2 * κ ≤ K) :
    StepConclusionD A B ζ incr q κ := by
  sorry

set_option maxHeartbeats 800000 in
/-- **Residual §4 leaf**: given the Lemma-10 bundle, produce the step
conclusion in every case where the clean up-move bound is unavailable —
`d̃ < d`, `d̃ = d`, or `d̃ > d` with `α_{d̃} + ζ + incr ≥ 1`.

The `d̃ < d` case is `case_down_pow` (margin `ε' = g/4`, where `g` is a
uniform lower bound on the `αd`-gap `α_d − α_{d̃}` supplied by `hgap`);
the `d̃ = d` case splits on `ρ = |Ã|/|A|` against
`|A|^{-σ}` with `σ = max (incr/2) (20·log(2C²)/(K·log|A|))`: the shrink
sub-case is `case_shrink_pow_sq`, the non-shrink sub-case is the
remaining leaf `residual_density_step`; and the degenerate `d̃ > d`
case (target exponent already above `1`) is `case_up_pow_hi` with
margin `3c₀/4`.

Note on the hypothesis list: `hgap`, `hobs15`, `hCa` (inside the bundle)
and `hεpow` are the largeness/margin inputs `thm2_step`'s parameter
choices supply; without them the statement would be *false* — e.g. at
`|A| = 2`, `d = 1`, a degenerate `d̃ = 0` witness satisfies the bare
bundle while no `StepConclusion` exists. -/
theorem residual_step
    {d : ℕ} {A : Finset (Fin d → ℤ)} {B : GAP.Box d}
    {ζ incr q ε K ι g c₀ : ℝ} {N : ℕ}
    (hd : 1 ≤ d) (hζ : 0 < ζ) (hαζ : αd d + ζ < 1)
    (hBint : B.IsInterval) (hNA : NonAveraging A)
    (hsub : A ⊆ B.toFinset)
    (hcex : (B.card : ℝ) ^ (αd d + ζ) < (A.card : ℝ))
    (hN : N ≤ A.card)
    (hε : 0 < ε) (hεg : 2 * ε ≤ g) (hg : 0 < g) (hg12 : g ≤ 1 / 12)
    (hK : 100 ≤ K) (hq0 : 0 < q) (hq : q ≤ 1 - 2 * ε)
    (hgap : ∀ {dt : ℕ}, 1 ≤ dt → dt < d → g ≤ αd d - αd dt)
    (hι : 0 < ι) (hc₀ : 0 < c₀) (hεc : ε ≤ c₀ / 8)
    (hobs15 : ∀ {dt : ℕ}, d < dt → (αd dt + ζ) *
      ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) ≤ 1 - c₀)
    (hincr : 0 < incr) (hincrι : incr ≤ ι) (hincrg : 4 * incr ≤ g)
    (hincrc : 16 * incr ≤ c₀)
    (hincrθ : incr ≤ ι / Real.log (A.card : ℝ))
    (hεpow : (2 : ℝ) ≤ (A.card : ℝ) ^ ε)
    (hdata : Lemma10Data A B ε K) :
    StepConclusion A ζ incr q := by
  obtain ⟨n, dt, At, ct, Wt, c', δ, γ, C, hδ, hδ4, hγ, hγδ, hγa, hder, hC,
    hCa, hAt, hAh, hirr, hup, hsame, hdown⟩ := hdata
  -- `|A|^ε ≥ 2` forces `|A| ≥ 2^{1/ε}`; hence `|Ã| ≥ |A|^{1-ε} ≥ 3`
  -- and `d̃ ≥ 1` (a `0`-dimensional witness sees at most one point).
  have ha0 : (0 : ℝ) < (A.card : ℝ) := by
    have := Wt.two_le_card.trans hder.card_le
    positivity
  have ha1 : (1 : ℝ) < (A.card : ℝ) := by
    by_contra hle
    push_neg at hle
    have h := Real.rpow_le_one (Nat.cast_nonneg _) hle hε.le
    linarith [hεpow]
  have ha2 : (2 : ℝ) ^ (1 / ε : ℝ) ≤ (A.card : ℝ) := by
    have h1 : ((A.card : ℝ) ^ ε) ^ (1 / ε : ℝ) = (A.card : ℝ) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg _), one_div,
        mul_inv_cancel₀ hε.ne', Real.rpow_one]
    rw [← h1]
    exact Real.rpow_le_rpow (by norm_num) hεpow (by positivity)
  have hAt3 : (3 : ℝ) ≤ (At.card : ℝ) := by
    have hε24 : ε ≤ 1 / 24 := by linarith [hεg, hg12]
    calc (3 : ℝ) ≤ (2 : ℝ) ^ (12 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (1 / (2 * ε) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε)]
          linarith [hε24]
      _ = ((2 : ℝ) ^ (1 / ε : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
      _ ≤ (A.card : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) ha2
            (by norm_num)
      _ ≤ (A.card : ℝ) ^ (1 - ε) :=
          Real.rpow_le_rpow_of_exponent_le ha1.le (by linarith)
      _ ≤ (At.card : ℝ) := hAt
  have hAt3n : 3 ≤ At.card := by exact_mod_cast hAt3
  have hdt1 : 1 ≤ dt := by
    rcases Nat.eq_zero_or_pos dt with h0 | h0
    · exfalso
      subst h0
      have h1 : (Wt.imageAh.card : ℝ) ≤ 1 := by
        rw [Wt.card_imageAh]
        exact_mod_cast Wt.card_Ah_le_one
      have h2 : (At.card : ℝ) ≤ 2 := by linarith [hAh]
      linarith [hAt3]
    · exact h0
  -- shared bounds and the `StepConclusion` assembly
  have he4 : (1 / 4 : ℝ) ≤ αd d + ζ := (αd_quarter_le hd).trans (by linarith)
  have he0 : (0 : ℝ) < αd d + ζ := by linarith
  have hba : (B.card : ℝ) ≤ (A.card : ℝ) ^ (αd d + ζ)⁻¹ :=
    (card_lt_rpow_of_rpow_lt he0 (by exact_mod_cast ha0) hcex).le
  have hinv4 : (αd d + ζ)⁻¹ ≤ 4 := by
    calc (αd d + ζ)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he4
      _ = 4 := by norm_num
  have hNA' : NonAveraging Wt.imageAh :=
    GAP.nonAveraging_ptCoeffImage _
      (fun _ ha ↦ Wt.hsub (Finset.mem_union_left _ ha))
      (NonAveraging.mono Wt.hAh (hder.nonAveraging hNA))
  have hA'card : Wt.imageAh.card ≤ A.card := by
    calc Wt.imageAh.card = Wt.Ah.card := Wt.card_imageAh
      _ ≤ At.card := Finset.card_le_card Wt.hAh
      _ ≤ A.card := hder.card_le
  -- assembly: any bound `|P̃|^{α_{d̃}+ζ+incr} < |A|^{1-ε}/2` gives the
  -- conclusion with `A' = ϕ(Â)`, `B' = coeffBox P̃`, `ζ' = ζ+incr`,
  -- `ρ' = |Ã|/(2|A|)`.
  have finish (h : (Wt.P.coeffBox.card : ℝ) ^ (αd dt + (ζ + incr))
      < (At.card : ℝ) / 2) : StepConclusion A ζ incr q := by
    refine ⟨dt, Wt.imageAh, Wt.P.coeffBox, ζ + incr,
      (At.card : ℝ) / (2 * (A.card : ℝ)), hdt1, coeffBox_isInterval _,
      hNA', Wt.imageAh_subset_coeffBox, hA'card, le_rfl, ?_, ?_, ?_, ?_⟩
    · exact h.trans_le hAh
    · calc (A.card : ℝ) ^ q ≤ (A.card : ℝ) ^ (1 - 2 * ε) :=
            Real.rpow_le_rpow_of_exponent_le ha1.le hq
        _ = (A.card : ℝ) ^ (1 - ε) / (A.card : ℝ) ^ ε := by
            rw [show (1 - 2 * ε : ℝ) = (1 - ε) - ε by ring,
              Real.rpow_sub ha0]
        _ ≤ (A.card : ℝ) ^ (1 - ε) / 2 :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg ha0.le _)
              (by norm_num) hεpow
        _ ≤ (Wt.imageAh.card : ℝ) := by linarith [hAt, hAh]
    · have hρmul : (At.card : ℝ) / (2 * (A.card : ℝ)) * (A.card : ℝ)
          = (At.card : ℝ) / 2 := by
        have hne : (A.card : ℝ) ≠ 0 := ha0.ne'
        field_simp
      rw [hρmul]
      linarith [hAh]
    · exact div_pos
        (by exact_mod_cast (by omega : 0 < At.card)) (by linarith)
  have hhalf : (A.card : ℝ) ^ (1 - ε) / 2 ≤ (At.card : ℝ) / 2 := by
    linarith [hAt]
  rcases lt_trichotomy dt d with hdt | hdt | hdt
  · -- **`d̃ < d`**: down-move via `case_down_pow` with margin `ε' = g/4`.
    have hΔ : g ≤ αd d - αd dt := hgap hdt1 hdt
    have he'pos : (0 : ℝ) < αd dt + (ζ + incr) := by
      linarith [αd_quarter_le hdt1, hζ, hincr]
    have he'le : αd dt + (ζ + incr) ≤ αd d + ζ := by
      linarith [hΔ, hincrg]
    have hsplit : (αd dt + (ζ + incr)) * (αd d + ζ)⁻¹
        ≤ 1 - ε - g / 4 := by
      have hΔi : (0 : ℝ) ≤ αd d - αd dt - incr := by linarith [hΔ, hincrg]
      have hge : αd d - αd dt - incr
          ≤ (αd d - αd dt - incr) * (αd d + ζ)⁻¹ := by
        rw [show (αd d - αd dt - incr) * (αd d + ζ)⁻¹
            = (αd d - αd dt - incr) / (αd d + ζ) from div_eq_mul_inv _ _]
        rw [le_div_iff₀ he0]
        nlinarith [hΔi, hαζ]
      have e'eq : αd dt + (ζ + incr)
          = αd d + ζ - (αd d - αd dt - incr) := by ring
      calc (αd dt + (ζ + incr)) * (αd d + ζ)⁻¹
          = (αd d + ζ - (αd d - αd dt - incr)) * (αd d + ζ)⁻¹ := by
            rw [e'eq]
        _ = (αd d + ζ) * (αd d + ζ)⁻¹
            - (αd d - αd dt - incr) * (αd d + ζ)⁻¹ := by ring
        _ = 1 - (αd d - αd dt - incr) * (αd d + ζ)⁻¹ := by
            rw [mul_inv_cancel₀ he0.ne']
        _ ≤ 1 - (αd d - αd dt - incr) := by linarith [hge]
        _ ≤ 1 - ε - g / 4 := by linarith [hΔ, hincrg, hεg]
    have hCa' : 2 * C ≤ (A.card : ℝ) ^ (g / 4 / 2) := by
      calc 2 * C ≤ (A.card : ℝ) ^ (ε / 4) := hCa
        _ ≤ (A.card : ℝ) ^ (g / 4 / 2) :=
            Real.rpow_le_rpow_of_exponent_le ha1.le (by linarith [hεg])
    exact finish ((case_down_pow (a := (A.card : ℝ)) (b := (B.card : ℝ))
      (p := (Wt.P.coeffBox.card : ℝ)) (C := C) (ε := ε) (ε' := g / 4)
      (e := αd d + ζ) (e' := αd dt + (ζ + incr))
      ha1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC he'pos
      (by linarith [hαζ] : αd dt + (ζ + incr) ≤ 1) hε.le
      (by linarith [hg] : (0 : ℝ) < g / 4) hsplit (hdown hdt) hba hCa').trans_le
      hhalf)
  · -- **`d̃ = d`**: shrink vs. density-increment split on
    -- `ρ = |Ã|/|A|` vs `|A|^{-σ}`.
    subst dt
    set σ : ℝ := max (incr / 2)
      (20 * Real.log (2 * C * C) / (K * Real.log (A.card : ℝ)))
      with hσdef
    have hσpos : (0 : ℝ) < σ :=
      lt_of_lt_of_le (by linarith [hincr] : (0 : ℝ) < incr / 2)
        (le_max_left _ _)
    by_cases hρσ : (At.card : ℝ) / (A.card : ℝ) ≤ (A.card : ℝ) ^ (-σ)
    · -- shrink regime: `case_shrink_pow_sq` with `t = incr·e⁻¹`.
      have hρpos : (0 : ℝ) < (At.card : ℝ) / (A.card : ℝ) :=
        div_pos (by exact_mod_cast (by omega : 0 < At.card)) ha0
      have he'pos : (0 : ℝ) < αd d + (ζ + incr) := by
        linarith [αd_quarter_le hd, hζ, hincr]
      have he'2 : αd d + (ζ + incr) ≤ 2 := by
        have h1 : incr ≤ 1 / 48 := by linarith [hincrg, hg12]
        linarith [hαζ]
      have hKpos : (0 : ℝ) < K := by linarith [hK]
      have hKsplit : K / 5 ≤ K * (αd d + (ζ + incr)) - 1 := by
        have he'4 : (1 / 4 : ℝ) ≤ αd d + (ζ + incr) :=
          (αd_quarter_le hd).trans (by linarith [hζ, hincr])
        have h1 : 1 + K / 5 ≤ K * (αd d + (ζ + incr)) := by
          have e1 : 1 + K / 5 = K * (1 / K + 1 / 5) := by
            field_simp
          rw [e1]
          apply mul_le_mul_of_nonneg_left _ hKpos.le
          have h2 : (1 : ℝ) / K ≤ 1 / 100 :=
            one_div_le_one_div_of_le (by norm_num) (by linarith [hK])
          linarith [he'4]
        linarith
      have ht : (αd d + (ζ + incr)) * (αd d + ζ)⁻¹
          ≤ 1 + incr * (αd d + ζ)⁻¹ := by
        have e1 : (αd d + (ζ + incr)) * (αd d + ζ)⁻¹
            = (αd d + ζ) * (αd d + ζ)⁻¹ + incr * (αd d + ζ)⁻¹ := by ring
        rw [e1, mul_inv_cancel₀ he0.ne']
      have htt : incr * (αd d + ζ)⁻¹ ≤ σ * K / 10 := by
        have h2 : incr * 4 ≤ incr * K / 20 := by
          have e1 : incr * K / 20 = incr * (K / 20) := by ring
          rw [e1]
          apply mul_le_mul_of_nonneg_left _ hincr.le
          linarith [hK]
        have h3 : incr * K / 20 ≤ σ * K / 10 := by
          have e1 : incr * K / 20 = (incr / 2) * (K / 10) := by ring
          have e2 : σ * K / 10 = σ * (K / 10) := by ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by linarith [hK] : (0 : ℝ) ≤ K / 10)
        calc incr * (αd d + ζ)⁻¹ ≤ incr * 4 :=
            mul_le_mul_of_nonneg_left hinv4 hincr.le
          _ ≤ incr * K / 20 := h2
          _ ≤ σ * K / 10 := h3
      have hloga : (0 : ℝ) < Real.log (A.card : ℝ) := Real.log_pos ha1
      have hσ2 : 2 * (Real.log (2 * C * C) / Real.log (A.card : ℝ))
          ≤ σ * K / 10 := by
        have h1 : 20 * Real.log (2 * C * C) /
            (K * Real.log (A.card : ℝ)) ≤ σ := le_max_right _ _
        have e1 : σ * K / 10 = σ * (K / 10) := by ring
        rw [e1]
        calc 2 * (Real.log (2 * C * C) / Real.log (A.card : ℝ))
            = (20 * Real.log (2 * C * C) /
                (K * Real.log (A.card : ℝ))) * (K / 10) := by
              field_simp
              ring
          _ ≤ σ * (K / 10) :=
              mul_le_mul_of_nonneg_right h1 (by linarith [hK] :
                (0 : ℝ) ≤ K / 10)
      have hC2pos : (0 : ℝ) < 2 * C * C := by positivity
      have hy : (A.card : ℝ) ^
          (Real.log (2 * C * C) / Real.log (A.card : ℝ)) = 2 * C * C := by
        rw [show Real.log (2 * C * C) / Real.log (A.card : ℝ)
            = Real.logb (A.card : ℝ) (2 * C * C) from rfl]
        exact Real.rpow_logb ha0 ha1.ne' hC2pos
      have hCa2 : 2 * C * C < (A.card : ℝ) ^ (σ * K / 10) := by
        have h1 : (2 * C * C) ^ 2
            ≤ (A.card : ℝ) ^ (σ * K / 10) := by
          calc (2 * C * C) ^ 2
              = ((A.card : ℝ) ^
                  (Real.log (2 * C * C) / Real.log (A.card : ℝ))) ^ 2 := by
                rw [hy]
            _ = (A.card : ℝ) ^
                (2 * (Real.log (2 * C * C) / Real.log (A.card : ℝ))) := by
                rw [sq, ← Real.rpow_add ha0]
                congr 1
                ring
            _ ≤ (A.card : ℝ) ^ (σ * K / 10) :=
                Real.rpow_le_rpow_of_exponent_le ha1.le hσ2
        have hlt : (2 * C * C : ℝ) < (2 * C * C) ^ 2 := by
          have h : (1 : ℝ) < 2 * C * C := by nlinarith [hC]
          nlinarith
        exact hlt.trans_le h1
      have hρa : (At.card : ℝ) / (A.card : ℝ) * (A.card : ℝ) / 2
          = (At.card : ℝ) / 2 := by
        have hne : (A.card : ℝ) ≠ 0 := ha0.ne'
        field_simp
      have hsc := case_shrink_pow_sq (a := (A.card : ℝ))
        (b := (B.card : ℝ)) (p := (Wt.P.coeffBox.card : ℝ)) (C := C)
        (ρ := (At.card : ℝ) / (A.card : ℝ)) (K := K) (σ := σ)
        (t := incr * (αd d + ζ)⁻¹)
        (e := αd d + ζ) (e' := αd d + (ζ + incr))
        ha1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC hρpos he'pos he'2
        (by linarith [hK] : (0 : ℝ) ≤ K) hKsplit ht hρσ hσpos (hsame rfl)
        hba hCa2 htt
      rw [hρa] at hsc
      exact finish hsc
    · -- non-shrink regime: the remaining leaf.
      push_neg at hρσ
      obtain ⟨A', B', ζ', ρ, hB'i, hNA2, hsub2, hcard2, hζ2, hlt2, hq2,
        hρm2, hρpos2, -, -⟩ :=
        residual_density_step (κ := K / 2) Wt hd hζ hαζ hBint hNA hsub hcex
          hN hε (by linarith [hεg, hg12] : ε < 1) hK hq0 hq hι hincr hincrι
          hincrθ hεpow hδ hδ4 hγ hγδ hγa hder hC hCa hAt hAh hirr
          (hsame rfl) hσpos hρσ (by linarith [hK]) (by linarith [hK])
      exact ⟨d, A', B', ζ', ρ, hd, hB'i, hNA2, hsub2, hcard2, hζ2, hlt2,
        hq2, hρm2, hρpos2⟩
  · -- **`d̃ > d` degenerate**: `case_up_pow_hi` covers `e' ∈ (0, 2]`
    -- (in particular `α_{d̃} + ζ + incr > 1`), margin `3c₀/4`.
    have he'pos : (0 : ℝ) < αd dt + (ζ + incr) := by
      linarith [αd_quarter_le hdt1, hζ, hincr]
    have he'2 : αd dt + (ζ + incr) ≤ 2 := by
      have h1 : αd dt < 1 := αd_lt_one hdt1
      have h2 : ζ + incr < 1 := by
        have h3 : ζ < 1 - αd d := by linarith [hαζ]
        have h4 : (1 / 4 : ℝ) ≤ αd d := αd_quarter_le hd
        have h5 : incr ≤ g / 4 := by linarith [hincrg]
        have h6 : g / 4 ≤ 1 / 48 := by linarith [hg12]
        linarith
      linarith
    have he'X : (αd dt + (ζ + incr)) *
        ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)))
        ≤ 1 - 3 * c₀ / 4 := by
      have h1 := hobs15 hdt
      have h2 : (αd dt + (ζ + incr)) *
          ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)))
          = (αd dt + ζ) *
            ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)))
            + incr * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) := by
        ring
      have hXle : (αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))
          ≤ (αd d + ζ)⁻¹ := by
        apply sub_le_self
        apply mul_nonneg (by linarith [hε])
        have hdd : (d : ℝ) ≤ (dt : ℝ) := by exact_mod_cast hdt.le
        linarith
      have h3 : incr * ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ)))
          ≤ incr * (αd d + ζ)⁻¹ :=
        mul_le_mul_of_nonneg_left hXle hincr.le
      have h4 : incr * (αd d + ζ)⁻¹ ≤ c₀ / 4 := by
        calc incr * (αd d + ζ)⁻¹ ≤ incr * 4 :=
            mul_le_mul_of_nonneg_left hinv4 hincr.le
          _ ≤ c₀ / 4 := by linarith [hincrc]
      rw [h2]
      linarith
    have hCa2' : 2 * C * C ≤ (A.card : ℝ) ^ ((3 * c₀ / 4) / 2) := by
      have h1 : C ≤ (A.card : ℝ) ^ (ε / 4) / 2 := by
        have hpos := Real.rpow_pos_of_pos ha0 (ε / 4)
        linarith [hCa]
      have h2 : C * C ≤ ((A.card : ℝ) ^ (ε / 4) / 2) *
          ((A.card : ℝ) ^ (ε / 4) / 2) := by
        apply mul_le_mul h1 h1
          (by linarith [hC] : (0 : ℝ) ≤ C)
          (by positivity : (0 : ℝ) ≤ (A.card : ℝ) ^ (ε / 4) / 2)
      have h3 : ((A.card : ℝ) ^ (ε / 4) / 2) * ((A.card : ℝ) ^ (ε / 4) / 2)
          = (A.card : ℝ) ^ (ε / 2) / 4 := by
        have e1 : (A.card : ℝ) ^ (ε / 4) * (A.card : ℝ) ^ (ε / 4)
            = (A.card : ℝ) ^ (ε / 4 + ε / 4) := (Real.rpow_add ha0 _ _).symm
        rw [div_mul_div_comm, e1, show ε / 4 + ε / 4 = ε / 2 by ring,
          show (2 : ℝ) * 2 = 4 by norm_num]
      have h4 : 2 * C * C ≤ (A.card : ℝ) ^ (ε / 2) / 2 := by
        linarith [h2, h3]
      have h5 : (A.card : ℝ) ^ (ε / 2) ≤ (A.card : ℝ) ^ (3 * c₀ / 4 / 2) :=
        Real.rpow_le_rpow_of_exponent_le ha1.le (by linarith [hεc, hc₀])
      linarith [Real.rpow_nonneg ha0.le (3 * c₀ / 4 / 2)]
    exact finish ((case_up_pow_hi (a := (A.card : ℝ)) (b := (B.card : ℝ))
      (p := (Wt.P.coeffBox.card : ℝ)) (C := C) (c := 3 * c₀ / 4) (ε := ε)
      (k := (dt : ℝ) - (d : ℝ)) (e := αd d + ζ) (e' := αd dt + (ζ + incr))
      ha1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC he'pos he'2
      (by have hdd : (d : ℝ) ≤ (dt : ℝ) := by exact_mod_cast hdt.le
          linarith)
      (by linarith [hc₀] : (0 : ℝ) < 3 * c₀ / 4) hε.le
      (by linarith [hεc, hc₀] : ε ≤ (3 * c₀ / 4) / 4) he'X (hup hdt) hba
      hCa2').trans_le hhalf)

/-- The per-instance §4 step property: every large non-averaging
counterexample `A ⊆ B` at exponent `α_d + ζ < 1` produces a
`StepConclusion` at increment `min ι (θ |A|)`.  Unlike `IterationStepProp`
(uniform `ι`), the increment may decay with `|A|` — this matches the
paper, whose `d̃ = d` increment `θ'(ζ,d,|A|)` has scale
`log log log |A| / log |A|`. -/
def StepProp (ζ₀ : ℝ) (ι : ℝ) (q : ℝ) (θ : ℝ → ℝ) (N : ℕ) : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ {ζ : ℝ}, ζ₀ ≤ ζ → αd d + ζ < 1 →
    ∀ {A : Finset (Fin d → ℤ)} {B : GAP.Box d},
      B.IsInterval → NonAveraging A → A ⊆ B.toFinset →
      (B.card : ℝ) ^ (αd d + ζ) < (A.card : ℝ) → N ≤ A.card →
      StepConclusion A ζ (min ι (θ (A.card : ℝ))) q

/-- **The §4 step** (assembly theorem).  For each fixed `ζ₀ > 0` the step
property holds for uniform `ι, q` and `θ |A| = ι / log |A|`.

Modulo the two leaf sorries (`lemma10_data`, `residual_step`) this is
proved: parameters are chosen as in the paper (`ε ≤ 0.01ζ`,
`K = 100`, `D = ⌈2/ζ₀⌉`), the Lemma-10 bundle is obtained, and the
`d̃ > d` case is dispatched to `step_up` (genuine), with all other cases
delegated to `residual_step`. -/
theorem thm2_step (ζ₀ : ℝ) (hζ₀ : 0 < ζ₀) :
    ∃ (ι q : ℝ) (θ : ℝ → ℝ) (N : ℕ), 0 < ι ∧ 0 < q ∧ q ≤ 1 ∧
      (∀ x : ℝ, 2 ≤ x → 0 < θ x) ∧ AntitoneOn θ (Set.Ici (2 : ℝ)) ∧
      1 ≤ N ∧ StepProp ζ₀ ι q θ N := by
  rcases lt_or_ge ζ₀ 1 with hζ1 | hζ1
  · obtain ⟨c₀, hc₀, hc₀1, hobs15⟩ := observation15_ge hζ₀ hζ1
    -- parameters: `D` the dimension bound, `g` the down-move gap floor,
    -- `ε` small in `ζ₀, c₀, g`, `K = max 100 (2(2D₀+6)/ε + 1)`, `q = 1 - 2ε`,
    -- `ι = min(c₀/16, g)`, `θ x = ι / log x`.
    have hD0 : (0 : ℝ) < ((⌈2 / ζ₀⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr (div_pos two_pos hζ₀)
    set D : ℝ := ((⌈2 / ζ₀⌉₊ : ℕ) : ℝ) with hD_def
    set g := min (1 / 12 : ℝ) (2 / (D * (D + 1))) with hg_def
    have hg : 0 < g := by
      rw [hg_def]
      exact lt_min (by norm_num)
        (div_pos two_pos (mul_pos hD0 (by linarith)))
    set ε := min (0.01 * ζ₀) (min (c₀ / 8) (g / 2)) with hε_def
    have hε : 0 < ε := by
      rw [hε_def]
      exact lt_min (mul_pos (by norm_num) hζ₀)
        (lt_min (by linarith) (by linarith))
    have hεle : ε ≤ 0.01 * ζ₀ := by rw [hε_def]; exact min_le_left _ _
    have hεc : ε ≤ c₀ / 8 := by
      rw [hε_def]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hε1 : ε < 1 := by linarith
    have hε3 : ε < 1 / 3 := by linarith
    obtain ⟨N₀, hl10⟩ := lemma10_data (ε := ε)
      (K := max 100 (2 * (2 * (⌈2 / ζ₀⌉₊ : ℝ) + 6) / ε + 1)) hε hε3
      (by positivity) ⌈2 / ζ₀⌉₊
      (lt_of_lt_of_le (lt_add_one _) (le_max_right _ _))
    set q := 1 - 2 * ε with hq_def
    have hq0 : 0 < q := by rw [hq_def]; linarith
    have hq1 : q ≤ 1 := by rw [hq_def]; linarith
    set ι := min (c₀ / 16) g with hι_def
    have hι : 0 < ι := by rw [hι_def]; exact lt_min (by linarith) hg
    have hιc : ι ≤ c₀ / 16 := by rw [hι_def]; exact min_le_left _ _
    have hιg : ι ≤ g := by rw [hι_def]; exact min_le_right _ _
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
    -- global threshold: `N` dominates Lemma-10's `N₀`, `3` (so
    -- `log |A| > 0`), and `2^{1/ε}` (so `2 ≤ |A|^ε`).
    refine ⟨ι, q, θ, max N₀ (max 3 (Nat.ceil ((2 : ℝ) ^ (1 / ε)))),
      hι, hq0, hq1, hθpos, hθanti, by omega, ?_⟩
    intro d hd ζ hζ hαζ A B hBint hNA hsub hcex hN
    have h2a : (2 : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast (le_trans (by omega : 2 ≤
        max N₀ (max 3 (Nat.ceil ((2 : ℝ) ^ (1 / ε))))) hN)
    have ha1 : (1 : ℝ) < (A.card : ℝ) := by linarith
    have ha0 : (0 : ℝ) < (A.card : ℝ) := by linarith
    have he : 0 < αd d + ζ := add_pos (αd_pos hd) (hζ₀.trans_le hζ)
    have hba : (B.card : ℝ) ≤ (A.card : ℝ) ^ (αd d + ζ)⁻¹ :=
      (card_lt_rpow_of_rpow_lt he (by omega) hcex).le
    -- `|B| ≤ |A|^4` for the Lemma-10 input (`β = (α_d+ζ)⁻¹ ≤ 4`).
    have hbox4 : (B.card : ℝ) ≤ (A.card : ℝ) ^ (4 : ℝ) := by
      have he4 : (1 / 4 : ℝ) ≤ αd d + ζ :=
        (αd_quarter_le hd).trans (by linarith)
      have hinv : (αd d + ζ)⁻¹ ≤ 4 := by
        calc (αd d + ζ)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he4
          _ = 4 := by norm_num
      exact hba.trans (Real.rpow_le_rpow_of_exponent_le ha1.le hinv)
    have hN0 : N₀ ≤ A.card := le_trans (by omega) hN
    -- `α_d + ζ < 1` bounds the ambient dimension by `⌈2/ζ₀⌉`.
    have hdD : d ≤ ⌈2 / ζ₀⌉₊ := by
      have hlt : (d : ℝ) < 2 / ζ :=
        dim_lt_of_slack hd (hζ₀.trans_le hζ) hαζ
      have hle : (2 : ℝ) / ζ ≤ 2 / ζ₀ :=
        div_le_div_of_nonneg_left (by norm_num) hζ₀ hζ
      have hlt' : (d : ℝ) < (⌈2 / ζ₀⌉₊ : ℝ) :=
        (hlt.trans_le hle).trans_le (Nat.le_ceil _)
      exact le_of_lt (by exact_mod_cast hlt')
    obtain ⟨n, dt, At, ct, Wt, c', δ, γ, C, hδ, hδ4, hγ, hγδ, hγa, hder,
      hC, hCa, hAt, hAh, hirr, hup, hsame, hdown⟩ :=
      hl10 hdD hBint hNA hsub hbox4 hN0
    -- the per-instance increment `incr = min ι (θ |A|)`
    set incr := min ι (θ (A.card : ℝ)) with hincr_def
    have hincr : 0 < incr := by
      rw [hincr_def]
      exact lt_min hι (hθpos _ h2a)
    have hincrι : incr ≤ ι := by rw [hincr_def]; exact min_le_left _ _
    have hincrg : incr ≤ g := le_trans hincrι hιg
    have hincrθ : incr ≤ ι / Real.log (A.card : ℝ) := by
      rw [hincr_def]
      simp only [hθ_def]
      exact min_le_right _ _
    have h2ε : (2 : ℝ) ^ (1 / ε : ℝ) ≤ (A.card : ℝ) := by
      calc (2 : ℝ) ^ (1 / ε : ℝ)
          ≤ ((⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        _ ≤ (A.card : ℝ) := by
            exact_mod_cast (le_trans (by omega : ⌈(2 : ℝ) ^ (1 / ε)⌉₊ ≤
              max N₀ (max 3 (Nat.ceil ((2 : ℝ) ^ (1 / ε))))) hN)
    have hεpow : (2 : ℝ) ≤ (A.card : ℝ) ^ ε := by
      have h2 : ((2 : ℝ) ^ (1 / ε : ℝ)) ^ ε = 2 := by
        rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
        rw [show (1 / ε : ℝ) * ε = 1 from div_mul_cancel₀ _ hε.ne']
        exact Real.rpow_one _
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε : ℝ)) ^ ε := h2.symm
        _ ≤ (A.card : ℝ) ^ ε :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h2ε hε.le
    -- derived facts `residual_step` consumes: `2ε ≤ g`, `g ≤ 1/12`,
    -- `g ≤ α_d − α_{d̃}` for `d̃ < d`, `4·incr ≤ g`, `16·incr ≤ c₀`, and
    -- the ∀-form of the Observation-15 bound.
    have hεg : 2 * ε ≤ g := by
      have : ε ≤ g / 2 := by
        rw [hε_def]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    have hg12 : g ≤ 1 / 12 := by rw [hg_def]; exact min_le_left _ _
    have hd0' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hDd : (d : ℝ) ≤ D := by
      rw [hD_def]
      exact_mod_cast hdD
    have hgap : ∀ {dt : ℕ}, 1 ≤ dt → dt < d → g ≤ αd d - αd dt := by
      intro dt hdt1 hdt
      have hsub' := αd_sub_gap hdt1 hdt
      have h1 : 2 / (D * (D + 1)) ≤ 2 / ((d : ℝ) * ((d : ℝ) + 1)) := by
        apply div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hd0' (by linarith))
        exact mul_le_mul hDd (by linarith) (by linarith)
          (by linarith [hD0])
      have h2 : g ≤ min (1 / 12 : ℝ) (2 / ((d : ℝ) * ((d : ℝ) + 1))) := by
        rw [hg_def]
        exact le_min (min_le_left _ _) ((min_le_right _ _).trans h1)
      linarith [hsub', h2]
    have hloga4 : (4 : ℝ) ≤ Real.log (A.card : ℝ) := by
      have hε24 : ε ≤ 1 / 24 := by linarith [hεg, hg12]
      have hlog2 : (0.693 : ℝ) < Real.log 2 :=
        (by norm_num : (0.693 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
      have h1 : (4 : ℝ) ≤ Real.log 2 / ε := by
        rw [le_div_iff₀ hε]
        nlinarith [hε24]
      calc (4 : ℝ) ≤ Real.log 2 / ε := h1
        _ = Real.log ((2 : ℝ) ^ (1 / ε : ℝ)) := by
            rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
            rw [one_div, mul_comm, ← div_eq_mul_inv]
        _ ≤ Real.log (A.card : ℝ) :=
            Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) _) h2ε
    have hincrg4 : 4 * incr ≤ g := by
      have h1 : ι / Real.log (A.card : ℝ) ≤ g / 4 := by
        rw [div_le_iff₀ (by linarith [hloga4] :
          (0 : ℝ) < Real.log (A.card : ℝ))]
        calc ι ≤ g := hιg
          _ = g / 4 * 4 := by ring
          _ ≤ g / 4 * Real.log (A.card : ℝ) :=
            mul_le_mul_of_nonneg_left hloga4 (by linarith [hg])
      calc 4 * incr ≤ 4 * (ι / Real.log (A.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hincrθ (by norm_num)
        _ ≤ 4 * (g / 4) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = g := by ring
    have hincrc : 16 * incr ≤ c₀ := by
      calc 16 * incr ≤ 16 * ι :=
          mul_le_mul_of_nonneg_left hincrι (by norm_num)
        _ ≤ c₀ := by linarith [hιc]
    have hobs15all : ∀ {dt : ℕ}, d < dt → (αd dt + ζ) *
        ((αd d + ζ)⁻¹ - (1 - ε) * ((dt : ℝ) - (d : ℝ))) ≤ 1 - c₀ := by
      intro dt hdt
      have hlem := hobs15 dt d ζ hd hdt hζ ε hε.le hεle
      simpa [one_div] using hlem
    by_cases hcase : d < dt ∧ αd dt + ζ + incr ≤ 1
    · -- **Case 1** (`d̃ > d`): genuine up-move via `step_up`.
      obtain ⟨hdt, hαe'⟩ := hcase
      have hCa' : 2 * C ≤ (A.card : ℝ) ^ (c₀ / 8) := by
        calc 2 * C ≤ (A.card : ℝ) ^ (ε / 4) := hCa
          _ ≤ (A.card : ℝ) ^ (c₀ / 8) :=
            Real.rpow_le_rpow_of_exponent_le ha1.le
              (by linarith [hεc, hc₀])
      exact step_up Wt hder hd hdt (hζ₀.trans_le hζ) hNA hincr
        (le_trans hincrι hιc) hαe' (hobs15all hdt) hc₀ hc₀1 hε hεc ha1 hba
        (hup hdt) hAt hAh hC hCa' hq0 (le_of_eq hq_def) hεpow
    · -- **Residual cases** (`d̃ < d`, `d̃ = d`, degenerate `d̃ > d`).
      clear hcase
      exact residual_step hd (hζ₀.trans_le hζ) hαζ hBint hNA hsub hcex
        hN hε hεg hg hg12 (le_max_left _ _) hq0 (le_of_eq hq_def) hgap hι
        hc₀ hεc
        hobs15all hincr hincrι hincrg4 hincrc hincrθ hεpow
        ⟨n, dt, At, ct, Wt, c', δ, γ, C, hδ, hδ4, hγ, hγδ, hγa, hder, hC,
          hCa, hAt, hAh, hirr, hup, hsame, hdown⟩
  · -- `ζ₀ ≥ 1`: `α_d + ζ < 1` is impossible since `α_d ≥ 1/4`, so the
    -- step property is vacuous.
    refine ⟨1, 1, fun _ => 1, 1, one_pos, one_pos, le_rfl, ?_, ?_,
      le_rfl, ?_⟩
    · intro x _; exact one_pos
    · intro x _ y _ _; rfl
    · intro d hd ζ hζ hαζ A B _ _ _ _ _
      exfalso
      have h14 : (1 / 4 : ℝ) ≤ αd d := αd_quarter_le hd
      linarith

end Thm2

end Nonaveraging
