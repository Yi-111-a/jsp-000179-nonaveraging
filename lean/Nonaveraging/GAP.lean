import Nonaveraging.Defs

/-!
# Generalized arithmetic progressions and the subset-sum structure theorem

Paper references (arXiv:2410.14624v2, §3 + Appendix A):

* **Theorem 3** — the Conlon–Fox–Pham structure theorem for subset sums
  (`cfp_structure`), stated for `(ℓ, β)`-sets: `A ⊆ B ⊆ ℤ^ℓ`, `|B| ≤ |A|^β`.
* **Corollary 5** — the specialization to `s = m / log² m`
  (`cfp_structure_cor`), with `P` symmetric and `csP` proper.

A `GAP ℓ d` is a `d`-dimensional generalized arithmetic progression in `ℤ^ℓ`:
`{ base + Σ nᵢ·stepᵢ : 0 ≤ nᵢ < widthᵢ }`.
-/

open Finset Asymptotics Filter

namespace Nonaveraging

/-- A `d`-dimensional generalized arithmetic progression in `ℤ^ℓ`. -/
structure GAP (ℓ d : ℕ) where
  base : Fin ℓ → ℤ
  step : Fin d → (Fin ℓ → ℤ)
  width : Fin d → ℕ

namespace GAP

variable {ℓ d : ℕ} (P : GAP ℓ d)

/-- The coefficient tuples indexing `P`. -/
def coeffs : Finset (Fin d → ℕ) :=
  Finset.univ.image fun n : Π i, Fin (P.width i) ↦ fun i ↦ (n i : ℕ)

/-- The evaluation map `n ↦ base + Σ nᵢ·stepᵢ`. -/
def eval (n : Fin d → ℕ) : Fin ℓ → ℤ :=
  P.base + ∑ i, (n i : ℤ) • P.step i

/-- The point set of the GAP. -/
def toFinset : Finset (Fin ℓ → ℤ) := P.coeffs.image P.eval

/-- `P` is *proper* if each point has a unique coefficient representation. -/
def Proper : Prop := Set.InjOn P.eval P.coeffs

/-- `P` is *homogeneous* if its base is an integer combination of its steps. -/
def Homogeneous : Prop := ∃ c : Fin d → ℤ, P.base = ∑ i, c i • P.step i

/-- Dilation `k·P`: scale base and steps, keep widths. -/
def smul (k : ℤ) : GAP ℓ d := ⟨k • P.base, fun i ↦ k • P.step i, P.width⟩

instance : SMul ℤ (GAP ℓ d) := ⟨fun k P ↦ P.smul k⟩

instance : SMul ℕ (GAP ℓ d) := ⟨fun k P ↦ P.smul (k : ℤ)⟩

/-- Translation `t +ᵥ P`. -/
def translate (t : Fin ℓ → ℤ) : GAP ℓ d := ⟨t + P.base, P.step, P.width⟩

/-- `P` is *symmetric*: there is a center `m` with `x ↦ 2m − x` preserving `P`. -/
def Symmetric : Prop := ∃ m : Fin ℓ → ℤ, ∀ x ∈ P.toFinset, (2 • m - x) ∈ P.toFinset

/-- Cardinality bound: `|P| ≤ ∏ widthᵢ`, with equality iff `P` is proper. -/
theorem card_toFinset_le : P.toFinset.card ≤ ∏ i, P.width i := by
  unfold toFinset
  calc (P.coeffs.image P.eval).card ≤ P.coeffs.card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Π i, Fin (P.width i))).card := by
        unfold coeffs
        exact Finset.card_image_le
    _ = ∏ i, P.width i := by
        rw [Finset.card_univ, Fintype.card_pi]
        exact Finset.prod_congr rfl fun i _ ↦ Fintype.card_fin _

/-- The subset sums of a finset in `ℤ^ℓ` (contains `0`). -/
def subsetSumsL {ℓ : ℕ} (A : Finset (Fin ℓ → ℤ)) : Finset (Fin ℓ → ℤ) :=
  A.powerset.image (·.sum id)

/-- An axis-aligned box in `ℤ^ℓ`: a product of intervals. -/
def Box (ℓ : ℕ) := Fin ℓ → Finset ℤ

namespace Box

def toFinset (B : Box ℓ) : Finset (Fin ℓ → ℤ) :=
  Fintype.piFinset B

def card (B : Box ℓ) : ℕ := ∏ i, (B i).card

theorem card_toFinset (B : Box ℓ) : B.toFinset.card = B.card :=
  Fintype.card_piFinset B

end Box

/-- `A` is an `(ℓ, β)`-set: a subset of `ℤ^ℓ` contained in a box of size
`|B| ≤ |A|^β`. -/
def IsLBSet (A : Finset (Fin ℓ → ℤ)) (β : ℝ) : Prop :=
  ∃ B : Box ℓ, A ⊆ B.toFinset ∧ (B.card : ℝ) ≤ (A.card : ℝ) ^ β

end GAP

/-- **Theorem 3 (CFP structure theorem)**.  For `ℓ, β > 1` and `0 < η < 1`
there are `c, d > 0` such that for any `A ⊆ B ⊆ ℤ^ℓ`, `|A| = m`, `|B| ≤ m^β`
and `s ∈ [m^η, c·m/log m]` there exist `Â ⊆ A` with
`|Â| ≥ m − c⁻¹·s·log m`, an integer `d' ≤ d`, a `d'`-dimensional GAP `P`
containing `Â ∪ {0}`, and `A' ⊆ Â` of size `≤ s` such that `Σ(A')` contains a
homogeneous translate of `csP`, and `csP` is proper. -/
theorem cfp_structure (ℓ : ℕ) {β η : ℝ} (hβ : 1 < β) (hη : 0 < η) (hη1 : η < 1) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ (A : Finset (Fin ℓ → ℤ)) (B : GAP.Box ℓ) (s : ℕ),
      A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      (A.card : ℝ) ^ η ≤ s → (s : ℝ) ≤ c * A.card / Real.log A.card →
      ∃ (Â : Finset (Fin ℓ → ℤ)) (d' : ℕ) (P : GAP ℓ d'),
        Â ⊆ A ∧ (A.card : ℝ) - c⁻¹ * s * Real.log A.card ≤ Â.card ∧
        (d' : ℝ) ≤ d ∧ P.Symmetric ∧
        (Â ∪ {0}) ⊆ P.toFinset ∧
        ∃ A' ⊆ Â, A'.card ≤ s ∧
          ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ c * s ∧
            ∃ t : Fin ℓ → ℤ,
              ((k • P).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
              (k • P).Proper := by
  sorry

/-- **Corollary 5**: Theorem 3 at `s = ⌊m / log² m⌋`; `P` may be taken
symmetric and `kP` proper.  Requires `m ≥ C` so that `s` lies in the
admissible range `[m^{1/2}, c·m/log m]` of Theorem 3. -/
theorem cfp_structure_cor (ℓ : ℕ) {β : ℝ} (hβ : 1 < β) :
    ∃ c d C : ℝ, 0 < c ∧ 0 < d ∧ 0 < C ∧ ∀ (A : Finset (Fin ℓ → ℤ))
      (B : GAP.Box ℓ),
      A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      C ≤ (A.card : ℝ) →
      ∃ (Â : Finset (Fin ℓ → ℤ)) (d' : ℕ) (P : GAP ℓ d'),
        Â ⊆ A ∧ (A.card : ℝ) - c⁻¹ * A.card / Real.log A.card ≤ Â.card ∧
        (d' : ℝ) ≤ d ∧ P.Symmetric ∧
        (Â ∪ {0}) ⊆ P.toFinset ∧
        ∃ A' ⊆ Â, (A'.card : ℝ) ≤ A.card / (Real.log A.card) ^ 2 ∧
          ∃ k : ℕ, 0 < k ∧
            (k : ℝ) ≤ c * (A.card / (Real.log A.card) ^ 2) ∧
            ∃ t : Fin ℓ → ℤ,
              ((k • P).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
              (k • P).Proper := by
  obtain ⟨c, d, hc, hd, hcfp⟩ :=
    cfp_structure ℓ hβ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)
  -- Eventually `(log m)² ≤ 64·m^{1/8}` (hence `≤ m^{1/4}`), `64 ≤ m^{1/8}`,
  -- `1/c ≤ log m`, `16 ≤ m`.
  have evLog : ∀ᶠ m : ℝ in atTop,
      (Real.log m) ^ 2 ≤ 64 * m ^ ((1 : ℝ) / 8) := by
    have hLo : (fun x : ℝ ↦ (Real.log (x ^ ((1 : ℝ) / 8))) ^ 2) =o[atTop]
        (fun x ↦ x ^ ((1 : ℝ) / 8)) :=
      (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [hLo.bound zero_lt_one, eventually_gt_atTop 0]
      with m hm hm0
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hm
    have hm' : |(Real.log (m ^ ((1 : ℝ) / 8))) ^ 2| ≤ 1 * |m ^ ((1 : ℝ) / 8)| := hm
    rw [one_mul, abs_of_nonneg (Real.rpow_nonneg hm0.le _), Real.log_rpow hm0,
      abs_of_nonneg (sq_nonneg _)] at hm'
    nlinarith [hm']
  have ev64 : ∀ᶠ m : ℝ in atTop, (64 : ℝ) ≤ m ^ ((1 : ℝ) / 8) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually_ge_atTop 64
  have evlog : ∀ᶠ m : ℝ in atTop, (1 : ℝ) / c ≤ Real.log m :=
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / c)
  obtain ⟨C₁, hC₁⟩ := eventually_atTop.mp
    (evLog.and (ev64.and (evlog.and (eventually_ge_atTop (16 : ℝ)))))
  refine ⟨c, d, max C₁ 1, hc, hd,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun A B hsub hB hCm ↦ ?_⟩
  obtain ⟨hlog2, h64, h1c, hm16⟩ :=
    hC₁ (A.card : ℝ) (le_trans (le_max_left _ _) hCm)
  have hmpos : (0 : ℝ) < (A.card : ℝ) := lt_of_lt_of_le (by norm_num) hm16
  have hlpos : (0 : ℝ) < Real.log (A.card : ℝ) := lt_of_lt_of_le (by positivity) h1c
  have hl2pos : (0 : ℝ) < (Real.log (A.card : ℝ)) ^ 2 := sq_pos_of_pos hlpos
  have hq14 : (Real.log (A.card : ℝ)) ^ 2 ≤ (A.card : ℝ) ^ ((1 : ℝ) / 4) := by
    have h18 : (0 : ℝ) ≤ (A.card : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_nonneg hmpos.le _
    have hmul : (64 : ℝ) * (A.card : ℝ) ^ ((1 : ℝ) / 8)
        ≤ (A.card : ℝ) ^ ((1 : ℝ) / 8) * (A.card : ℝ) ^ ((1 : ℝ) / 8) :=
      mul_le_mul_of_nonneg_right h64 h18
    rw [← Real.rpow_add hmpos, show (1 : ℝ) / 8 + 1 / 8 = 1 / 4 by norm_num]
      at hmul
    linarith
  set s := ⌊(A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2⌋₊ with hs_def
  have hs_le : (s : ℝ) ≤ (A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2 :=
    Nat.floor_le (by positivity)
  -- `m^{1/2} + 1 ≤ m / log²m`, so `m^{1/2} ≤ s`.
  have hbig : (A.card : ℝ) ^ ((1 : ℝ) / 2) + 1
      ≤ (A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2 := by
    rw [le_div_iff₀ hl2pos]
    have h1 : ((A.card : ℝ) ^ ((1 : ℝ) / 2) + 1) * (Real.log (A.card : ℝ)) ^ 2
        ≤ ((A.card : ℝ) ^ ((1 : ℝ) / 2) + 1) * (A.card : ℝ) ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left hq14 (by positivity)
    refine h1.trans ?_
    have h2 : ((A.card : ℝ) ^ ((1 : ℝ) / 2) + 1) * (A.card : ℝ) ^ ((1 : ℝ) / 4)
        = (A.card : ℝ) ^ ((3 : ℝ) / 4) + (A.card : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [add_mul, one_mul, ← Real.rpow_add hmpos]
      norm_num
    rw [h2]
    have h3 : (A.card : ℝ) ^ ((1 : ℝ) / 4) ≤ (A.card : ℝ) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le
        (le_trans (by norm_num : (1 : ℝ) ≤ 16) hm16) (by norm_num)
    have h4 : 2 * (A.card : ℝ) ^ ((3 : ℝ) / 4) ≤ (A.card : ℝ) := by
      have h5 : (2 : ℝ) ≤ (A.card : ℝ) ^ ((1 : ℝ) / 4) := by
        have h16 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
            show (1 : ℝ) / 4 = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
        calc (2 : ℝ) = (16 : ℝ) ^ ((1 : ℝ) / 4) := h16.symm
          _ ≤ (A.card : ℝ) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hm16) (by norm_num)
      calc 2 * (A.card : ℝ) ^ ((3 : ℝ) / 4)
          ≤ (A.card : ℝ) ^ ((1 : ℝ) / 4) * (A.card : ℝ) ^ ((3 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hmpos.le _)
        _ = (A.card : ℝ) := by
            rw [← Real.rpow_add hmpos]
            norm_num
    linarith
  have hs_ge : (A.card : ℝ) ^ ((1 : ℝ) / 2) ≤ (s : ℝ) := by
    have := Nat.lt_floor_add_one ((A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2)
    linarith [hbig]
  have hs_le2 : (s : ℝ) ≤ c * (A.card : ℝ) / Real.log (A.card : ℝ) := by
    refine hs_le.trans ?_
    rw [div_le_div_iff₀ hl2pos hlpos]
    have hcm : (1 : ℝ) ≤ c * Real.log (A.card : ℝ) := by
      have := (div_le_iff₀ hc).mp h1c
      nlinarith
    calc (A.card : ℝ) * Real.log (A.card : ℝ)
        = 1 * ((A.card : ℝ) * Real.log (A.card : ℝ)) := by ring
      _ ≤ (c * Real.log (A.card : ℝ)) * ((A.card : ℝ) * Real.log (A.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hcm (by positivity)
      _ = c * (A.card : ℝ) * Real.log (A.card : ℝ) ^ 2 := by ring
  obtain ⟨Â, d', P, hÂsub, hÂcard, hd'le, hSym, hsub0,
    A', hA'sub, hA'card, k, hkpos, hkle, t, htrans, hprop⟩ :=
    hcfp A B s hsub hB hs_ge hs_le2
  have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
  have hst : (s : ℝ) * Real.log (A.card : ℝ)
      ≤ (A.card : ℝ) / Real.log (A.card : ℝ) := by
    rw [le_div_iff₀ hlpos, mul_assoc, ← sq]
    calc (s : ℝ) * (Real.log (A.card : ℝ)) ^ 2
        ≤ ((A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2)
            * (Real.log (A.card : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hs_le (sq_nonneg _)
      _ = (A.card : ℝ) := by field_simp
  refine ⟨Â, d', P, hÂsub, ?_, hd'le, hSym, hsub0, A', hA'sub, ?_, k, hkpos, ?_,
    t, htrans, hprop⟩
  · refine le_trans ?_ hÂcard
    apply sub_le_sub_left
    have hle : c⁻¹ * (s : ℝ) * Real.log (A.card : ℝ)
        ≤ c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ) := by
      rw [mul_div_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left hst hcinv.le
    exact hle
  · have : (A'.card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hA'card
    exact this.trans hs_le
  · exact hkle.trans (mul_le_mul_of_nonneg_left hs_le hc.le)

end Nonaveraging
