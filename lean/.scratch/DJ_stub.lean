import Nonaveraging.GAP
import Nonaveraging.GeoNumbers
import Nonaveraging.ConvexBody

/-!
# Discrete John, GAP covolumes, and the lattice-intersection step

Supporting lemmas for `embedded_in_mu_convex_position` (Theorem 4 of
arXiv:2410.14624).  The remaining `sorry` in `Structure.lean` is the
Lemma 11–14 core: one must show that the subset-sum sets of the two
shifted pieces share a nonzero vector.

* **§A** packages `B ∩ ℤ^d` (`intPoints`, `intPointsFinset`) and the
  centered progression `P(𝐯,𝐍) = {∑ nᵢ vᵢ : |nᵢ| ≤ Nᵢ}` as `GAP.centered`.
* **§B** is Lemma 7 (discrete John): `exists_progBox_sandwich` is the
  qualitative version (proved, from `GeoNumbers.discrete_john`);
  `discrete_john_strong` is the faithful uniform statement (left as a
  `sorry`).
* **§C** is the covolume machinery of Lemmas 11–12: the index of a
  generated lattice equals `|det|` of its step matrix
  (`index_intLattice_eq_natAbs_det`), a Hadamard-type bound on that
  determinant (`natAbs_det_le`), the "GAP inside a box" step bound
  (`step_abs_le_of_subset`), the resulting covolume bound
  (`index_gapLattice_le`), a subset-sum growth bound
  (`subsetSumsL_card_le_mul`), and the Minkowski lemma
  `exists_ne_zero_mem_inf_mem_box` producing a nonzero lattice point of
  `⟨P₁⟩ ∩ ⟨P₂⟩` inside a symmetric coordinate box.
* **§D** is the covering step (paper eq. (15)):
  `mem_subsetSumsL_of_zonotope_translate`, followed by the assembled
  intersection statement `exists_ne_zero_subsetSum_inter`, which is
  exactly the shape needed at the end of
  `embedded_in_mu_convex_position`.
-/

open Finset MeasureTheory
open scoped Pointwise

namespace Nonaveraging

variable {d ℓ : ℕ}

/-! ## §0. Generic GAP facts (relocated from `Structure.lean`)

These lemmas are proved here so that this file does not depend on
`Nonaveraging.Structure` (which in turn imports this file for the
Lemma 11–14 core of Theorem 4).  The names are unchanged. -/

namespace GAP

variable {ℓ d : ℕ} (P : GAP ℓ d)

/-- Evaluating a scaled GAP: `(k·P).eval n = k • P.eval n`. -/
theorem eval_smul {d : ℕ} (P : GAP ℓ d) (k : ℤ) (n : Fin d → ℕ) :
    (k • P).eval n = k • P.eval n := by
  show (k • P.base) + ∑ i, (n i : ℤ) • (k • P.step i)
      = k • (P.base + ∑ i, (n i : ℤ) • P.step i)
  rw [smul_add, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

end GAP

/-! ## §A. Integer points and the centered progression `P(𝐯,𝐍)` -/

section IntPoints

variable {B : Set (Fin d → ℝ)}

/-- The integer points of `B`, viewed as a subset of `ℤ^d` (the paper's
`B ∩ ℤ^d`). -/
def intPoints (B : Set (Fin d → ℝ)) : Set (Fin d → ℤ) := {z | intVec z ∈ B}

theorem mem_intPoints {z : Fin d → ℤ} : z ∈ intPoints B ↔ intVec z ∈ B :=
  Iff.rfl

/-- A bounded set in `ℝ^d` contains finitely many integer points. -/
theorem finite_intPoints (hBb : Bornology.IsBounded B) :
    (intPoints B).Finite := by
  obtain ⟨R, hR⟩ := hBb.subset_closedBall (0 : Fin d → ℝ)
  refine Set.Finite.subset
    (Set.Finite.pi (t := fun i ↦ Set.Icc (-(⌈R⌉₊ : ℤ)) (⌈R⌉₊ : ℤ))
      fun i ↦ Set.finite_Icc _ _) ?_
  intro z hz
  rw [Set.mem_univ_pi]
  intro i
  have hzR : intVec z ∈ Metric.closedBall (0 : Fin d → ℝ) R := hR hz
  have hzi : |(z i : ℝ)| ≤ R := by
    calc |(z i : ℝ)| = ‖intVec z i‖ := by
          rw [intVec_apply, Real.norm_eq_abs]
      _ ≤ ‖intVec z‖ := norm_le_pi_norm _ i
      _ ≤ R := mem_closedBall_zero_iff.mp hzR
  rw [Set.mem_Icc, ← abs_le]
  have h5 : ((|z i| : ℤ) : ℝ) ≤ ((⌈R⌉₊ : ℤ) : ℝ) := by
    rw [Int.cast_abs, Int.cast_natCast]
    exact hzi.trans (Nat.le_ceil _)
  exact Int.cast_le.mp h5

/-- `B ∩ ℤ^d` as a finset. -/
noncomputable def intPointsFinset (B : Set (Fin d → ℝ))
    (hBb : Bornology.IsBounded B) : Finset (Fin d → ℤ) :=
  (finite_intPoints hBb).toFinset

theorem mem_intPointsFinset (hBb : Bornology.IsBounded B) {z : Fin d → ℤ} :
    z ∈ intPointsFinset B hBb ↔ intVec z ∈ B :=
  Set.Finite.mem_toFinset _

/-- Integer linear independence lifts from `ℝ^d` to `ℤ^d` through
`intVec`. -/
theorem linearIndependent_int_of_intVec {v : Fin d → Fin ℓ → ℤ}
    (hv : LinearIndependent ℝ fun i ↦ intVec (v i)) :
    LinearIndependent ℤ v := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  have hsum : (∑ j ∈ s, (g j : ℝ) • intVec (v j)) = 0 := by
    funext k
    rw [Pi.zero_apply, Finset.sum_apply]
    have hz : (∑ j ∈ s, g j * v j k : ℤ) = 0 := by
      have h0 := congrFun hg k
      simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at h0
      exact h0
    simp only [Pi.smul_apply, smul_eq_mul, intVec_apply, ← Int.cast_mul,
      ← Int.cast_sum, hz, Int.cast_zero]
  have h := hv s (fun j ↦ (g j : ℝ)) hsum i hi
  exact_mod_cast h

/-- A centered GAP built on a `ℤ`-linearly-independent family is
proper. -/
theorem proper_centered_of_linearIndependent {v : Fin d → Fin ℓ → ℤ}
    (hv : LinearIndependent ℤ v) (N : Fin d → ℕ) :
    (GAP.centered v N).Proper := by
  intro a ha b hb hab
  rw [GAP.centered_eval, GAP.centered_eval] at hab
  have hsum : (∑ i, ((a i : ℤ) - (b i : ℤ)) • v i) = 0 := by
    have e : (∑ i, ((a i : ℤ) - (N i : ℤ)) • v i)
        - (∑ i, ((b i : ℤ) - (N i : ℤ)) • v i) = 0 := sub_eq_zero.mpr hab
    rw [← Finset.sum_sub_distrib] at e
    convert e using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_smul]
    congr 1
    ring
  have hz : ∀ i, (a i : ℤ) - (b i : ℤ) = 0 :=
    fun i ↦ (linearIndependent_iff'.mp hv) Finset.univ _ hsum i
      (Finset.mem_univ i)
  funext i
  exact_mod_cast sub_eq_zero.mp (hz i)

/-- `|P(𝐯,𝐍)| = ∏ (2Nᵢ+1)` when `𝐯` is `ℤ`-linearly independent. -/
theorem card_centered_toFinset {v : Fin d → Fin ℓ → ℤ}
    (hv : LinearIndependent ℤ v) (N : Fin d → ℕ) :
    (GAP.centered v N).toFinset.card = ∏ i, (2 * N i + 1) := by
  rw [GAP.card_toFinset_of_proper _
    (proper_centered_of_linearIndependent hv N)]
  exact Finset.prod_congr rfl fun i _ ↦ rfl

end IntPoints

/-! ## §B. The discrete John lemma (Lemma 7) -/

section DiscreteJohn

variable {B : Set (Fin d → ℝ)}

/-- Qualitative discrete John lemma: an integer progression box sandwiched
around `B ∩ ℤ^d`, built on a linearly independent integer family.  This is
`GeoNumbers.discrete_john` repackaged with `P(𝐯,𝐍)` as `GAP.centered`;
here `c` may depend on `B`, and the vectors are only `ℝ`-independent (hence
`ℤ`-independent)
(in the construction of `GeoNumbers.discrete_john` they are in fact the
standard basis).  The faithful uniform statement with a genuine `ℤ`-basis
is `discrete_john_strong`. -/
theorem exists_progBox_sandwich (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) (hBs : ∀ x ∈ B, -x ∈ B)
    (hBb : Bornology.IsBounded B) :
    ∃ (c : ℝ) (v : Fin d → Fin d → ℤ) (N : Fin d → ℕ),
      0 < c ∧ LinearIndependent ℤ v ∧ (∀ i, 0 < N i) ∧
        ((GAP.centered v fun i ↦ ⌊c * (N i : ℝ)⌋₊).toFinset ⊆
          intPointsFinset B hBb) ∧
        (intPointsFinset B hBb ⊆ (GAP.centered v N).toFinset) := by
  obtain ⟨c, v, N, hc, hv, hN, hinner, houter⟩ :=
    discrete_john hBo hBc hB0 hBs hBb
  refine ⟨c, v, N, hc, linearIndependent_int_of_intVec hv, hN, ?_, ?_⟩
  · intro x hx
    rw [GAP.mem_centered] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [mem_intPointsFinset]
    apply hinner
    intro i
    have h1 : ((|a i| : ℤ) : ℝ) ≤ (⌊c * (N i : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast ha i
    have h2 : (⌊c * (N i : ℝ)⌋₊ : ℝ) ≤ c * (N i : ℝ) :=
      Nat.floor_le (mul_nonneg hc.le (Nat.cast_nonneg _))
    rw [Int.cast_abs] at h1
    exact h1.trans h2
  · intro x hx
    rw [mem_intPointsFinset] at hx
    obtain ⟨z', hz', rfl⟩ := houter x hx
    rw [GAP.mem_centered]
    refine ⟨z', fun i ↦ ?_, rfl⟩
    have hzi := hz' i
    rw [← Int.cast_abs] at hzi
    exact_mod_cast hzi

/-- The counting consequence of a John sandwich:
`|P(𝐯,𝐍)| ≤ (3/c)^d · |B ∩ ℤ^d|`, the `≪_d` bound used in Lemmas 11–12. -/
theorem card_progBox_le {v : Fin d → Fin d → ℤ} {N : Fin d → ℕ}
    (hv : LinearIndependent ℤ v) (hBb : Bornology.IsBounded B)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hinner : (GAP.centered v fun i ↦ ⌊c * (N i : ℝ)⌋₊).toFinset ⊆
      intPointsFinset B hBb) :
    ((GAP.centered v N).toFinset.card : ℝ) ≤
      (3 / c) ^ d * ((intPointsFinset B hBb).card : ℝ) := by
  have key : ∀ i, (2 * (N i : ℝ) + 1)
      ≤ (3 / c) * (2 * (⌊c * (N i : ℝ)⌋₊ : ℝ) + 1) := by
    intro i
    have hNnn : (0 : ℝ) ≤ N i := Nat.cast_nonneg _
    rcases eq_or_lt_of_le hNnn with hN0 | hNpos
    · have hNi : (N i : ℝ) = 0 := hN0.symm
      rw [hNi]
      simp only [mul_zero, Nat.floor_zero, Nat.cast_zero]
      have h3c : (1 : ℝ) ≤ 3 / c := by
        rw [one_le_div₀ hc]
        linarith [hc1]
      nlinarith [h3c]
    · by_cases hbig : 1 ≤ c * (N i : ℝ)
      · have hfl : c * (N i : ℝ) / 2 ≤ (⌊c * (N i : ℝ)⌋₊ : ℝ) := by
          have h1 : (1 : ℝ) ≤ (⌊c * (N i : ℝ)⌋₊ : ℝ) := by
            have h1' : (1 : ℕ) ≤ ⌊c * (N i : ℝ)⌋₊ :=
              Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ c * (N i : ℝ) by
                exact_mod_cast hbig)
            exact_mod_cast h1'
          have h2 : c * (N i : ℝ) ≤ (⌊c * (N i : ℝ)⌋₊ : ℝ) + 1 :=
            le_of_lt (Nat.lt_floor_add_one _)
          linarith
        have hge : c * (N i : ℝ) ≤ 2 * (⌊c * (N i : ℝ)⌋₊ : ℝ) + 1 := by
          linarith
        have key2 : (3 / c) * (c * (N i : ℝ)) ≤
            (3 / c) * (2 * (⌊c * (N i : ℝ)⌋₊ : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hge (by positivity)
        have heq : (3 / c) * (c * (N i : ℝ)) = 3 * (N i : ℝ) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hc.ne']
        have hNi : (1 : ℝ) ≤ (N i : ℝ) := by
          have : 0 < N i := Nat.cast_pos.mp hNpos
          exact_mod_cast this
        rw [heq] at key2
        linarith
      · push_neg at hbig
        have h3 : (N i : ℝ) < 1 / c := by
          have hmul := mul_lt_mul_of_pos_left hbig (inv_pos.mpr hc)
          rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, mul_one] at hmul
          rwa [one_div]
        have hNi : (1 : ℝ) ≤ (N i : ℝ) := by exact_mod_cast hNpos
        have h4 : 2 * (N i : ℝ) + 1 ≤ 3 / c := by
          calc 2 * (N i : ℝ) + 1 ≤ 3 * (N i : ℝ) := by linarith
            _ ≤ 3 * (1 / c) :=
              mul_le_mul_of_nonneg_left h3.le (by norm_num)
            _ = 3 / c := by ring
        have h5 : (3 / c) ≤
            (3 / c) * (2 * (⌊c * (N i : ℝ)⌋₊ : ℝ) + 1) := by
          have hpos : (0 : ℝ) < 3 / c := by positivity
          have hnn : (1 : ℝ) ≤ 2 * (⌊c * (N i : ℝ)⌋₊ : ℝ) + 1 := by
            have hnn' : (0 : ℝ) ≤ (⌊c * (N i : ℝ)⌋₊ : ℝ) :=
              Nat.cast_nonneg _
            linarith
          nlinarith
        exact h4.trans h5
  rw [card_centered_toFinset hv]
  have hcard := card_centered_toFinset hv (fun i ↦ ⌊c * (N i : ℝ)⌋₊)
  have hle : (((GAP.centered v fun i ↦ ⌊c * (N i : ℝ)⌋₊).toFinset).card : ℝ)
      ≤ ((intPointsFinset B hBb).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hinner
  calc ((∏ i, (2 * N i + 1) : ℕ) : ℝ)
      = ∏ i, (2 * (N i : ℝ) + 1) := by push_cast; rfl
    _ ≤ ∏ i, (3 / c) * (2 * (⌊c * (N i : ℝ)⌋₊ : ℝ) + 1) := by
        apply Finset.prod_le_prod₀
        · intro i _; positivity
        · intro i _; exact key i
    _ = (3 / c) ^ d * ∏ i, (2 * (⌊c * (N i : ℝ)⌋₊ : ℝ) + 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
    _ = (3 / c) ^ d *
          (((GAP.centered v fun i ↦ ⌊c * (N i : ℝ)⌋₊).toFinset).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ (3 / c) ^ d * ((intPointsFinset B hBb).card : ℝ) :=
        mul_le_mul_of_nonneg_left hle (by positivity)

/-- Dilations of a convex set containing `0` add: a point of `a • B`
plus a point of `b • B` is a point of `(a + b) • B` (for `a, b ≥ 0`). -/
theorem mem_smul_add (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {x y : Fin d → ℝ}
    (hx : x ∈ a • B) (hy : y ∈ b • B) :
    x + y ∈ (a + b) • B := by
  obtain ⟨x', hx', rfl⟩ := Set.mem_smul_set.mp hx
  obtain ⟨y', hy', rfl⟩ := Set.mem_smul_set.mp hy
  rcases (add_nonneg ha hb).eq_or_lt with h0 | hpos
  · obtain rfl : a = 0 := by linarith
    obtain rfl : b = 0 := by linarith
    show (0 : ℝ) • x' + (0 : ℝ) • y' ∈ (0 + 0 : ℝ) • B
    rw [zero_smul, zero_smul, add_zero, add_zero]
    exact ⟨0, hB0, by simp⟩
  · have hne : a + b ≠ 0 := hpos.ne'
    refine Set.mem_smul_set.mpr
      ⟨(a / (a + b)) • x' + (b / (a + b)) • y', ?_, ?_⟩
    · exact hBc hx' hy' (div_nonneg ha hpos.le) (div_nonneg hb hpos.le)
        (by field_simp)
    · rw [smul_add, smul_smul, smul_smul]
      have e1 : (a + b) * (a / (a + b)) = a := by field_simp
      have e2 : (a + b) * (b / (a + b)) = b := by field_simp
      rw [e1, e2]

/-- A finite sum of points of `wᵢ • B` lies in `(∑ wᵢ) • B`
(for `wᵢ ≥ 0` and convex `B ∋ 0`). -/
theorem sum_mem_smul (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    {ι : Type*} {s : Finset ι} {w : ι → ℝ} {t : ι → Fin d → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (ht : ∀ i ∈ s, t i ∈ w i • B) :
    (∑ i ∈ s, t i) ∈ (∑ i ∈ s, w i) • B := by
  sorry
/-- For convex `B ∋ 0`, `t • B ⊆ B` when `0 ≤ t ≤ 1`. -/
theorem smul_self_subset (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • B ⊆ B := by
  rintro x ⟨y, hy, rfl⟩
  have h := hBc hB0 hy (sub_nonneg.mpr ht1) ht0 (by ring)
  simpa using h

/-- **The adapted integer basis lemma** — the geometry-of-numbers input
behind Lemma 7 (discrete John): uniformly in the symmetric convex bounded
body `B ∋ 0`, there is a `ℤ`-basis `v` of `ℤ^d` and "successive-minima
widths" `λᵢ ≥ 0` such that

* each `vᵢ` with `λᵢ > 0` lies in every dilation `t • B`, `t > K·λᵢ`, and
* every `z ∈ B ∩ ℤ^d` has `v`-coordinates `m` with `|mᵢ| ≤ K / λᵢ`;
  with `K / 0 = 0` this forces `mᵢ = 0` in directions outside `span B`,
  where `λᵢ` is set to `0`.

This is precisely the lattice input that the proof of Lemma 7 (Tao–Vu,
Theorem 3.36) extracts from **Minkowski's second theorem** on `ℤ^d`:
the successive-minima vectors `wᵢ` (which exist by
`GeoNumbers.exists_succMinima`) generate a sublattice `Λ'` of index
`[ℤ^d : Λ'] ≤ d!` (the cross-polytope bound
`vol B ≥ 2^d·|det w| / (d! · λ₁⋯λ_d)` combined with the successive-minima
product bound `λ₁⋯λ_d · vol B ≤ 2^d`), the Hermite normal form completes
`w` to a `ℤ`-basis `v` adapted to the flag `span(w₁,…,wᵢ) ∩ ℤ^d`, and
the triangular coefficient relations together with the minimality of the
`wᵢ` give `gauge B (vᵢ) ≲_d λᵢ` and `|mᵢ| ≲_d 1/λᵢ`.  Mathlib (v4.34.0)
contains Minkowski's *first* theorem
(`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` and its
weak-inequality variant in `MeasureTheory/Group/GeometryOfNumbers.lean`)
and the `ZLattice` covolume API
(`Algebra/Module/ZLattice/Covolume.lean`), but no successive-minima
product bound (Minkowski's second theorem) and no Hermite/Smith normal
form machinery for sublattices of `ℤ^d`; this lemma is exactly that
missing input. -/
theorem exists_zbasis_adapted (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : Set (Fin d → ℝ)), Convex ℝ B →
      (0 : Fin d → ℝ) ∈ B → (∀ x ∈ B, -x ∈ B) →
      Bornology.IsBounded B →
      ∃ (v : Fin d → Fin d → ℤ) (lam : Fin d → ℝ),
        LinearIndependent ℤ v ∧ Submodule.span ℤ (Set.range v) = ⊤ ∧
        (∀ i, 0 ≤ lam i) ∧
        (∀ i, 0 < lam i → ∀ t : ℝ, K * lam i < t →
            intVec (v i) ∈ t • B) ∧
        (∀ z : Fin d → ℤ, intVec z ∈ B → ∃ m : Fin d → ℤ,
            z = ∑ i, m i • v i ∧ ∀ i, |(m i : ℝ)| ≤ K / lam i) := by
  sorry

/-- **Lemma 7 (discrete John, Tao–Vu Theorem 3.36 form)**: there is a
constant `c_d > 0` depending only on `d` such that for every bounded
symmetric convex `B ⊆ ℝ^d` containing `0` there exist a `ℤ`-basis
`v = (v₁,…,v_d)` of `ℤ^d` and widths `N` with

`P(𝐯, ⌊c_d·𝐍⌋) ⊆ B ∩ ℤ^d ⊆ P(𝐯, 𝐍)`.

This is the faithful statement.  The existing `GeoNumbers.discrete_john`
proves the qualitative version with `c` depending on `B` and only
`ℝ`-linear independence (its `v` is in fact the standard basis, which
gives the outer inclusion for every `B` but the inner inclusion only with
`B`-dependent constant); a uniform constant with a basis adapted to the
successive minima of `B` requires the genuine argument via Minkowski's
second theorem on the integer lattice.

The proof here reduces the theorem to the adapted-basis lemma
`exists_zbasis_adapted` (the missing Minkowski-second-theorem input,
currently a `sorry`): with `K` and `v`, `λ` from that lemma one takes
`c = (4dK² + 1)⁻¹` and `Nᵢ = ⌊K/λᵢ⌋₊`.  The outer inclusion is immediate
from the coordinate bound; the inner inclusion follows by writing
`∑ rᵢvᵢ` (`|rᵢ| ≤ ⌊cNᵢ⌋`) as a positive combination
`∑ 2Kλᵢ|rᵢ| • (±yᵢ)` of points `yᵢ = vᵢ/(2Kλᵢ) ∈ B` whose total weight is
`< 1`, so convexity (plus `0 ∈ B`) gives membership — this works for
every convex `B`, including non-open and degenerate ones, since no gauge
subadditivity is used. -/
theorem discrete_john_strong (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (B : Set (Fin d → ℝ)),
      Convex ℝ B → (0 : Fin d → ℝ) ∈ B → (∀ x ∈ B, -x ∈ B) →
      Bornology.IsBounded B →
      ∃ (v : Fin d → Fin d → ℤ) (N : Fin d → ℕ),
        LinearIndependent ℤ v ∧ Submodule.span ℤ (Set.range v) = ⊤ ∧
        (∀ z ∈ (GAP.centered v fun i ↦ ⌊c * (N i : ℝ)⌋₊).toFinset,
            intVec z ∈ B) ∧
        (∀ z : Fin d → ℤ, intVec z ∈ B →
            z ∈ (GAP.centered v N).toFinset) := by
  sorry
/-! ## §C. Covolumes of generated lattices and the intersection lemma -/

section Covolume

/-- The integer lattice generated by a family of integer vectors (the
paper's `⟨P⟩` when the family is the step set of a homogeneous GAP). -/
def intLattice (v : Fin d → Fin ℓ → ℤ) : Submodule ℤ (Fin ℓ → ℤ) :=
  Submodule.span ℤ (Set.range v)

theorem mem_intLattice {v : Fin d → Fin ℓ → ℤ} {x : Fin ℓ → ℤ} :
    x ∈ intLattice v ↔ ∃ c : Fin d → ℤ, x = ∑ i, c i • v i := by
  rw [intLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor <;> rintro ⟨c, hc⟩ <;> exact ⟨c, hc.symm⟩

/-- `⟨P⟩`: the lattice generated by the steps of `P`.  For a homogeneous
`P` this coincides with the subgroup generated by `P.toFinset`, which is
the paper's usage in Lemmas 11–14. -/
def gapLattice (P : GAP ℓ d) : Submodule ℤ (Fin ℓ → ℤ) :=
  intLattice P.step

/-- The index (covolume) of a full-rank generated lattice is `|det|` of
the matrix whose columns are the generators. -/
theorem index_intLattice_eq_natAbs_det {v : Fin d → Fin d → ℤ}
    (hv : LinearIndependent ℤ v) :
    (intLattice v).toAddSubgroup.index =
      ((Matrix.of fun i j ↦ (v j) i).det).natAbs := by
  set bL : Module.Basis (Fin d) ℤ ↥((intLattice v).toAddSubgroup) :=
    Module.Basis.span hv
  have hbv : ∀ i, (bL i : Fin d → ℤ) = v i :=
    fun i ↦ Module.Basis.coe_span_apply hv i
  have h := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin d))
    (intLattice v).toAddSubgroup bL
  have hmat : (Pi.basisFun ℤ (Fin d)).toMatrix
        (fun x ↦ (bL x : Fin d → ℤ))
      = Matrix.of fun i j ↦ (v j) i := by
    ext i j
    simp only [Module.Basis.toMatrix_apply, Pi.basisFun_repr,
      Matrix.of_apply, hbv]
  rw [h, Module.Basis.det_apply, hmat]

/-- Hadamard-type bound: `|det M| ≤ d! · ∏_j C_j.natAbs` when column `j`
of the integer matrix `M` is coordinatewise bounded by `C j`. -/
theorem natAbs_det_le {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ)
    {C : Fin d → ℤ} (hC : ∀ i j, |M i j| ≤ C j) :
    M.det.natAbs ≤ d.factorial * ∏ j, (C j).natAbs := by
  classical
  have hnatAbs_prod : ∀ (s : Finset (Fin d)) (f : Fin d → ℤ),
      (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs := by
    intro s f
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.natAbs_mul,
          ih]
  rw [Matrix.det_apply]
  have h1 : |∑ σ : Equiv.Perm (Fin d),
        Equiv.Perm.sign σ • ∏ i, M (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin d), |(∏ i, M (σ i) i : ℤ)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun σ _ ↦ ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
      simp [hs]
  have hsum : (∑ σ : Equiv.Perm (Fin d),
        Equiv.Perm.sign σ • ∏ i, M (σ i) i).natAbs
      ≤ ∑ σ : Equiv.Perm (Fin d), (∏ i, M (σ i) i).natAbs := by
    have hcast : ((∑ σ : Equiv.Perm (Fin d),
            Equiv.Perm.sign σ • ∏ i, M (σ i) i).natAbs : ℤ)
        ≤ ((∑ σ : Equiv.Perm (Fin d), (∏ i, M (σ i) i).natAbs) : ℕ) := by
      rw [Int.natCast_natAbs, Nat.cast_sum]
      refine h1.trans (Finset.sum_le_sum fun σ _ ↦ ?_)
      rw [Int.natCast_natAbs]
    exact_mod_cast hcast
  apply hsum.trans
  have hterm : ∀ σ : Equiv.Perm (Fin d),
      (∏ i, M (σ i) i).natAbs ≤ ∏ i, (C i).natAbs := by
    intro σ
    rw [hnatAbs_prod]
    apply Finset.prod_le_prod
    intro i _
    have hle : |M (σ i) i| ≤ |C i| := (hC (σ i) i).trans (le_abs_self _)
    have hle' : (((M (σ i) i).natAbs : ℕ) : ℤ) ≤ ((C i).natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs]
      exact hle
    exact_mod_cast hle'
  calc ∑ σ : Equiv.Perm (Fin d), (∏ i, M (σ i) i).natAbs
      ≤ ∑ _σ : Equiv.Perm (Fin d), ∏ i, (C i).natAbs :=
        Finset.sum_le_sum fun σ _ ↦ hterm σ
    _ = d.factorial * ∏ i, (C i).natAbs := by
        simp [Finset.sum_const, Fintype.card_perm, Fintype.card_fin]

/-- Steps of a nonempty GAP contained in an integer coordinate box are
bounded by the box widths — the quantitative heart of the Lemma 11
statement "`Pᵢ ⊆ translate of C·B` implies `|step| ≪ w`". -/
theorem step_abs_le_of_subset {P : GAP ℓ d} {lo hi : Fin ℓ → ℤ}
    (hsub : P.toFinset ⊆
      Fintype.piFinset fun i ↦ Finset.Icc (lo i) (hi i))
    (hne : P.toFinset.Nonempty) (j : Fin d) (hj : 2 ≤ P.width j) :
    ∀ i, |P.step j i| ≤ hi i - lo i := by
  classical
  have hw : ∀ i, 0 < P.width i := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨n, hn, -⟩ := Finset.mem_image.mp hx
    exact fun i ↦ Nat.pos_of_ne_zero fun h ↦ by
      have hc := GAP.mem_coeffs.mp hn i
      omega
  have h0mem : (0 : Fin d → ℕ) ∈ P.coeffs :=
    GAP.mem_coeffs.mpr fun i ↦ hw i
  have hemem : Function.update (0 : Fin d → ℕ) j 1 ∈ P.coeffs := by
    apply GAP.mem_coeffs.mpr
    intro i
    by_cases hij : i = j
    · subst hij; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hij]; simpa using hw i
  have heval0 : P.eval 0 = P.base := by simp [GAP.eval]
  have hevale : P.eval (Function.update (0 : Fin d → ℕ) j 1)
      = P.base + P.step j := by
    calc P.eval (Function.update (0 : Fin d → ℕ) j 1)
        = P.base +
            ∑ i, ((Function.update (0 : Fin d → ℕ) j 1 i : ℤ) •
              P.step i) := rfl
      _ = P.base + (Function.update (0 : Fin d → ℕ) j 1 j : ℤ) •
            P.step j := by
          congr 1
          apply Finset.sum_eq_single j
          · intro i _ hij
            rw [Function.update_of_ne hij]; simp
          · intro h; exact absurd (Finset.mem_univ j) h
      _ = P.base + P.step j := by
          rw [Function.update_self]; simp
  have hbase : P.base ∈ P.toFinset :=
    Finset.mem_image.mpr ⟨0, h0mem, heval0⟩
  have hpt : P.base + P.step j ∈ P.toFinset :=
    Finset.mem_image.mpr ⟨_, hemem, hevale⟩
  intro i
  have hblo := Fintype.mem_piFinset.mp (hsub hbase) i
  have hplo := Fintype.mem_piFinset.mp (hsub hpt) i
  rw [Finset.mem_Icc] at hblo hplo
  have hsteq : P.step j i = (P.base + P.step j) i - P.base i := by simp
  rw [hsteq]
  have h1 : lo i ≤ P.base i := hblo.1
  have h2 : P.base i ≤ hi i := hblo.2
  have h3 : lo i ≤ (P.base + P.step j) i := hplo.1
  have h4 : (P.base + P.step j) i ≤ hi i := hplo.2
  simp only [Pi.add_apply] at h3 h4
  rw [abs_le]
  constructor <;> omega

/-- Covolume bound for the GAP lattice: `index ⟨P⟩ ≤ d!·∏ C_j.natAbs`
when the `j`-th step is bounded by `C j`. -/
theorem index_gapLattice_le {P : GAP d d}
    (hv : LinearIndependent ℤ P.step) {C : Fin d → ℤ}
    (hC : ∀ j i, |P.step j i| ≤ C j) :
    (gapLattice P).toAddSubgroup.index ≤
      d.factorial * ∏ j, (C j).natAbs := by
  rw [gapLattice, index_intLattice_eq_natAbs_det hv]
  exact natAbs_det_le _ fun i j ↦ hC j i

/-- **Minkowski in the intersection of two lattices** (the Lemma-12
ingredient for `⟨P₁⟩ ∩ ⟨P₂⟩`): if `L₁, L₂` are finite-index subgroups of
`ℤ^d` and the symmetric coordinate box of radii `r` satisfies
`∏ rᵢ ≥ 2^d · index(L₁) · index(L₂)`, then `L₁ ∩ L₂` has a nonzero point
in the box. -/
theorem exists_ne_zero_mem_inf_mem_box {d : ℕ} [NeZero d]
    (L₁ L₂ : AddSubgroup (Fin d → ℤ))
    (hL₁ : L₁.index ≠ 0) (hL₂ : L₂.index ≠ 0)
    {r : Fin d → ℝ} (hr : ∀ i, 0 ≤ r i)
    (h : 2 ^ d * ((L₁.index * L₂.index : ℕ) : ℝ) ≤ ∏ i, r i) :
    ∃ z : Fin d → ℤ, z ≠ 0 ∧ z ∈ L₁ ∧ z ∈ L₂ ∧
      ∀ i, |(z i : ℝ)| ≤ r i := by
  classical
  set L := L₁ ⊓ L₂ with hLdef
  have hLi : L.index ≠ 0 := AddSubgroup.index_inf_ne_zero hL₁ hL₂
  have hLle : L.index ≤ L₁.index * L₂.index := AddSubgroup.index_inf_le
  -- A `ℤ`-basis of `L`.
  obtain ⟨e⟩ : Nonempty (↥(L.toIntSubmodule) ≃ₗ[ℤ] (Fin d → ℤ)) :=
    (Int.submodule_toAddSubgroup_index_ne_zero_iff).mp (by
      rw [AddSubgroup.toIntSubmodule_toAddSubgroup]; exact hLi)
  set bL : Module.Basis (Fin d) ℤ ↥(L.toIntSubmodule) :=
    (Pi.basisFun ℤ (Fin d)).map e.symm
  set w : Fin d → Fin d → ℤ := fun i ↦ (bL i : Fin d → ℤ)
  have hwmem : ∀ i, w i ∈ L.toIntSubmodule := fun i ↦ (bL i).2
  -- `index L = |det w|`.
  have hdet : L.index =
      (((Pi.basisFun ℤ (Fin d)).det w).natAbs) := by
    have h := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin d)) L bL
    exact h
  -- The same vectors form an `ℝ`-basis of `ℝ^d`.
  set vR : Fin d → Fin d → ℝ := fun i ↦ intVec (w i)
  have hdetR : ((Pi.basisFun ℝ (Fin d)).det vR) ≠ 0 := by
    rw [Module.Basis.det_apply]
    intro hd
    have hdZ : ((Pi.basisFun ℤ (Fin d)).det w) ≠ 0 := by
      rw [hdet] at hLi
      exact fun h0 ↦ hLi (congrArg Int.natAbs h0)
    apply hdZ
    rw [Module.Basis.det_apply]
    have hmap : (Pi.basisFun ℝ (Fin d)).toMatrix vR =
        (Int.castRingHom ℝ).mapMatrix
          ((Pi.basisFun ℤ (Fin d)).toMatrix w) := by
      ext i j
      simp only [Module.Basis.toMatrix_apply, Pi.basisFun_repr,
        RingHom.mapMatrix_apply, Int.coe_castRingHom]
      exact intVec_apply _ _
    rw [hmap, ← RingHom.map_det] at hd
    simp only [Int.coe_castRingHom] at hd
    exact_mod_cast hd
  have hbasis : LinearIndependent ℝ vR ∧
      Submodule.span ℝ (Set.range vR) = ⊤ :=
    (Module.Basis.is_basis_iff_det _).mpr (isUnit_iff_ne_zero.mpr hdetR)
  set bR : Module.Basis (Fin d) ℝ (Fin d → ℝ) :=
    Module.Basis.mk hbasis.1 hbasis.2.ge
  have hbR_eq : ⇑bR = vR := Module.Basis.coe_mk _ _
  -- The determinant in the Minkowski bound equals `index L`.
  have hdet_eq : |(Matrix.of ⇑bR).det| = (L.index : ℝ) := by
    have h1 : Matrix.of ⇑bR = Matrix.of vR := by rw [hbR_eq]
    rw [h1]
    have h2 : (Matrix.of vR).det =
        ((Pi.basisFun ℝ (Fin d)).det vR) := by
      rw [Module.Basis.det_apply]
      have htr : ((Pi.basisFun ℝ (Fin d)).toMatrix vR).transpose =
          Matrix.of vR := by
        ext i j
        simp [Module.Basis.toMatrix_apply, Pi.basisFun_repr,
          Matrix.transpose_apply]
      rw [← htr, Matrix.det_transpose]
    rw [h2]
    have h3 : (Pi.basisFun ℝ (Fin d)).det vR =
        (((Pi.basisFun ℤ (Fin d)).det w : ℤ) : ℝ) := by
      rw [Module.Basis.det_apply, Module.Basis.det_apply]
      have hmap : (Pi.basisFun ℝ (Fin d)).toMatrix vR =
          (Int.castRingHom ℝ).mapMatrix
            ((Pi.basisFun ℤ (Fin d)).toMatrix w) := by
        ext i j
        simp only [Module.Basis.toMatrix_apply, Pi.basisFun_repr,
          RingHom.mapMatrix_apply, Int.coe_castRingHom]
        exact intVec_apply _ _
      rw [hmap, ← RingHom.map_det]
      simp only [Int.coe_castRingHom]
    rw [h3, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    exact_mod_cast hdet.symm
  -- Minkowski on the symmetric coordinate box.
  set s : Set (Fin d → ℝ) := Set.univ.pi fun i ↦ Set.Icc (-r i) (r i)
  have hssymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    rw [Set.mem_univ_pi] at hx ⊢
    intro i
    have hxi := hx i
    rw [Set.mem_Icc] at hxi ⊢
    rw [Pi.neg_apply]
    constructor <;> linarith [hxi.1, hxi.2]
  have hscvx : Convex ℝ s := convex_pi fun i _ ↦ convex_Icc _ _
  have hscpct : IsCompact s := isCompact_univ_pi fun i ↦ isCompact_Icc
  have hsvol : MeasureTheory.volume s =
      ENNReal.ofReal (2 ^ Fintype.card (Fin d) * ∏ i, r i) :=
    volume_pi_Icc_neg r hr
  have hbound : ENNReal.ofReal |(Matrix.of ⇑bR).det| *
        2 ^ Fintype.card (Fin d) ≤ MeasureTheory.volume s := by
    rw [hsvol, hdet_eq, Fintype.card_fin]
    have hLpos : (0 : ℝ) < (L.index : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hLi
    have hpropos : (0 : ℝ) < ((L₁.index * L₂.index : ℕ) : ℝ) := by
      have hpos : 0 < L₁.index * L₂.index :=
        Nat.mul_pos (Nat.pos_of_ne_zero hL₁) (Nat.pos_of_ne_zero hL₂)
      exact_mod_cast hpos
    have hge : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hLle' : (L.index : ℝ) ≤ ∏ i, r i := by
      have h1 : (L.index : ℝ) ≤ ((L₁.index * L₂.index : ℕ) : ℝ) := by
        exact_mod_cast hLle
      have h2 : ((L₁.index * L₂.index : ℕ) : ℝ) ≤ ∏ i, r i := by
        calc ((L₁.index * L₂.index : ℕ) : ℝ)
            ≤ 2 ^ d * ((L₁.index * L₂.index : ℕ) : ℝ) := by
              nlinarith
          _ ≤ ∏ i, r i := h
      exact h1.trans h2
    calc ENNReal.ofReal (L.index : ℝ) * 2 ^ d
        = ENNReal.ofReal (L.index : ℝ) * ENNReal.ofReal (2 ^ d) := by
          rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_ofNat]
      _ = ENNReal.ofReal ((L.index : ℝ) * 2 ^ d) := by
          rw [← ENNReal.ofReal_mul hLpos.le]
      _ ≤ ENNReal.ofReal ((∏ i, r i) * 2 ^ d) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right hLle' (by positivity)
      _ = ENNReal.ofReal (2 ^ d * ∏ i, r i) := by rw [mul_comm]
  obtain ⟨x, hx0, hxs, hxspan⟩ :=
    exists_ne_zero_mem_span_range_of_volume_le bR hssymm hscvx hscpct
      hbound
  -- `x` is an integer combination of the `w i`, hence lies in `L₁ ∩ L₂`.
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxspan
  set z : Fin d → ℤ := ∑ i, c i • w i
  have hzL : z ∈ L := by
    have hmem : z ∈ L.toIntSubmodule :=
      Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hwmem i)
    exact hmem
  have hzx : intVec z = x := by
    rw [← hc, hbR_eq]
    have hterm : ∀ i, c i • vR i = intVec (c i • w i) := by
      intro i
      rw [← Int.cast_smul_eq_zsmul ℝ (c i) (vR i), intVec_smul]
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i]
    exact intVec_sum Finset.univ _
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hx0
    rw [← hzx, hz]
    simp
  · exact (AddSubgroup.mem_inf.mp hzL).1
  · exact (AddSubgroup.mem_inf.mp hzL).2
  · intro i
    have hxi : -r i ≤ x i ∧ x i ≤ r i := hxs i (Set.mem_univ i)
    have hzi : (z i : ℝ) = x i := by rw [← hzx]; rfl
    rw [hzi]
    exact abs_le.mpr hxi

/-- The subset sums of a disjoint union split (used to combine the
`Σ(X∖X')` and `Σ(X')` contributions in eq. (15)). -/
theorem subsetSumsL_add {X Y : Finset (Fin ℓ → ℤ)} (hdj : Disjoint X Y)
    {s t : Fin ℓ → ℤ} (hs : s ∈ GAP.subsetSumsL X)
    (ht : t ∈ GAP.subsetSumsL Y) :
    s + t ∈ GAP.subsetSumsL (X ∪ Y) := by
  obtain ⟨S, hS, hSeq⟩ := GAP.mem_subsetSumsL.mp hs
  obtain ⟨T', hT', hTeq⟩ := GAP.mem_subsetSumsL.mp ht
  apply GAP.mem_subsetSumsL.mpr
  refine ⟨S ∪ T', Finset.union_subset_union hS hT', ?_⟩
  rw [Finset.sum_union (Finset.disjoint_of_subset_right hT'
    (Finset.disjoint_of_subset_left hS hdj)), hSeq, hTeq]

/-- **Subset-sum growth bound** (Lemma 8 style): for `A ⊆ P` every subset
sum `∑_{a∈S} a = |S|·base + ∑ᵢ mᵢ·stepᵢ` has `|S| ≤ |A|` and
`0 ≤ mᵢ ≤ |A|·wᵢ`, so `|Σ(A)| ≤ (|A|+1)·∏(|A|·wᵢ+1)`. -/
theorem subsetSumsL_card_le_mul {P : GAP ℓ d} {A : Finset (Fin ℓ → ℤ)}
    (hA : A ⊆ P.toFinset) :
    (GAP.subsetSumsL A).card ≤
      (A.card + 1) * ∏ i, (A.card * P.width i + 1) := by
  classical
  let rep : (Fin ℓ → ℤ) → Fin d → ℕ := fun a ↦
    if h : a ∈ P.toFinset then (Finset.mem_image.mp h).choose else 0
  have hrep : ∀ a ∈ A, rep a ∈ P.coeffs ∧ P.eval (rep a) = a := by
    intro a ha
    have h : a ∈ P.toFinset := hA ha
    have hspec := (Finset.mem_image.mp h).choose_spec
    have hra : rep a = (Finset.mem_image.mp h).choose := dif_pos h
    rw [hra]
    exact hspec
  set boxN : Finset (ℕ × (Fin d → ℕ)) :=
    (Finset.range (A.card + 1)) ×ˢ
      (Fintype.piFinset fun i ↦ Finset.range (A.card * P.width i + 1))
    with hboxN
  have hsub : GAP.subsetSumsL A ⊆ boxN.image fun ⟨j, m⟩ ↦
      j • P.base + ∑ i, (m i : ℤ) • P.step i := by
    intro y hy
    rw [GAP.mem_subsetSumsL] at hy
    obtain ⟨S, hS, rfl⟩ := hy
    rw [Finset.mem_image]
    refine ⟨(S.card, fun i ↦ ∑ a ∈ S, rep a i), ?_, ?_⟩
    · rw [hboxN, Finset.mem_product]
      refine ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.card_le_card hS)), ?_⟩
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      have hle : (∑ a ∈ S, rep a i) ≤ S.card * P.width i := by
        calc ∑ a ∈ S, rep a i ≤ ∑ _a ∈ S, P.width i := by
              apply Finset.sum_le_sum
              intro a ha
              exact (GAP.mem_coeffs.mp (hrep a (hS ha)).1 i).le
          _ = S.card * P.width i := by
              rw [Finset.sum_const, smul_eq_mul]
      exact Nat.lt_succ_of_le
        (hle.trans (Nat.mul_le_mul (Finset.card_le_card hS) le_rfl))
    · have hsum : (∑ a ∈ S, a) = S.card • P.base +
          ∑ i, ((∑ a ∈ S, rep a i : ℕ) : ℤ) • P.step i := by
        calc ∑ a ∈ S, a = ∑ a ∈ S, P.eval (rep a) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [(hrep a (hS ha)).2]
          _ = ∑ a ∈ S, (P.base + ∑ i, (rep a i : ℤ) • P.step i) :=
              Finset.sum_congr rfl fun a _ ↦ rfl
          _ = S.card • P.base +
                ∑ i, ((∑ a ∈ S, rep a i : ℕ) : ℤ) • P.step i := by
              rw [Finset.sum_add_distrib, Finset.sum_const]
              congr 1
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _
              rw [Nat.cast_sum]
              exact Finset.sum_smul.symm
      exact hsum.symm
  calc (GAP.subsetSumsL A).card
      ≤ (boxN.image fun ⟨j, m⟩ ↦
          j • P.base + ∑ i, (m i : ℤ) • P.step i).card :=
        Finset.card_le_card hsub
    _ ≤ boxN.card := Finset.card_image_le
    _ = (A.card + 1) * ∏ i, (A.card * P.width i + 1) := by
        rw [hboxN]
        simp [Finset.card_product, Fintype.card_piFinset]

end Covolume

/-! ## §D. The covering lemma (eq. (15)) and the assembled intersection -/

section Covering

/-- `x ∈ P.translate t` iff `x - t ∈ P`: the point set of a translate is
the translate of the point set. -/
theorem GAP.mem_translate_iff {P : GAP ℓ d} {t x : Fin ℓ → ℤ} :
    x ∈ (P.translate t).toFinset ↔ x - t ∈ P.toFinset := by
  simp only [GAP.toFinset, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n, hn, ?_⟩
    have hev : (P.translate t).eval n = t + P.eval n := by
      show (t + P.base) + ∑ i, (n i : ℤ) • P.step i =
          t + (P.base + ∑ i, (n i : ℤ) • P.step i)
      rw [add_assoc]
    rw [hev]
    ext i
    simp [Pi.sub_apply, Pi.add_apply]
  · rintro ⟨n, hn, hnx⟩
    refine ⟨n, hn, ?_⟩
    have hev : (P.translate t).eval n = t + P.eval n := by
      show (t + P.base) + ∑ i, (n i : ℤ) • P.step i =
          t + (P.base + ∑ i, (n i : ℤ) • P.step i)
      rw [add_assoc]
    rw [hev, hnx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

/-- Points of `k·P` lie in `⟨P⟩` when `P` is homogeneous. -/
theorem GAP.smul_toFinset_subset_span {P : GAP ℓ d} (hP : P.Homogeneous)
    (z : ℤ) :
    ((z • P).toFinset : Set (Fin ℓ → ℤ)) ⊆
      Submodule.span ℤ (Set.range P.step) := by
  obtain ⟨cb, hcb⟩ := hP
  intro x hx
  rw [Finset.mem_coe, GAP.toFinset, Finset.mem_image] at hx
  obtain ⟨n, -, rfl⟩ := hx
  rw [GAP.eval_smul]
  apply Submodule.smul_mem
  show P.base + ∑ i, (n i : ℤ) • P.step i ∈
    Submodule.span ℤ (Set.range P.step)
  rw [hcb]
  apply Submodule.add_mem
  · exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i))
  · exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i))

/-- **Covering lemma** (Pham–Zakharov §3.3, eq. (15)): if a translate of
`k·P` is contained in the subset sums of `X' ⊆ X`, then every point `y`
of the lattice `⟨P⟩` that lies in the region `𝒵_{X∖X'} + q + (k/2)·P`
is a subset sum of `X`.

The hypothesis `habs` packages the absorption step that the paper
performs implicitly: a lattice point `r ∈ ⟨P⟩` whose coordinates are
bounded by `ℓ·wX` satisfies `r + t ∈ k·P` for every `t ∈ (k/2)·P`.  In
the paper `r` is the Lemma-13 rounding error (`|rᵢ| ≤ √(d|X|)·wᵢ`,
sharpened to `d·wᵢ` in `exists_subset_sum_sub_le_int`); the paper writes
`r ∈ (cs/2)P` as a *region* and combines `r + t` coefficientwise — for a
general `⟨P⟩`-point the needed coefficient bound uses the discrete John
sandwich on `⟨P⟩` (`discrete_john_strong`). -/
theorem mem_subsetSumsL_of_zonotope_translate {X X' : Finset (Fin ℓ → ℤ)}
    (hX' : X' ⊆ X) {P : GAP ℓ d} (hPh : P.Homogeneous) {K : ℤ}
    {q : Fin ℓ → ℤ}
    (hq : q ∈ Submodule.span ℤ (Set.range P.step))
    (hXspan : ∀ a ∈ X, a ∈ Submodule.span ℤ (Set.range P.step))
    (htr : ((K • P).translate q).toFinset ⊆ GAP.subsetSumsL X')
    {wX : Fin ℓ → ℝ} (hwX0 : ∀ i, 0 ≤ wX i)
    (hwX : ∀ a ∈ X \ X', ∀ i, |(a i : ℝ)| ≤ wX i)
    (habs : ∀ r : Fin ℓ → ℤ,
        r ∈ Submodule.span ℤ (Set.range P.step) →
        (∀ i, |(r i : ℝ)| ≤ (ℓ : ℝ) * wX i) →
        ∀ t ∈ ((K / 2) • P).toFinset, r + t ∈ (K • P).toFinset)
    {y : Fin ℓ → ℤ}
    (hy : y ∈ Submodule.span ℤ (Set.range P.step))
    (hz : ∃ z : Fin ℓ → ℝ,
        z ∈ zonotope ((X \ X').image fun x i ↦ (x i : ℝ)) ∧
        ∃ t ∈ ((K / 2) • P).toFinset,
          ∀ i, (y i : ℝ) = z i + (q i : ℝ) + (t i : ℝ)) :
    y ∈ GAP.subsetSumsL X := by
  classical
  obtain ⟨z, hzZ, t, ht, hdecomp⟩ := hz
  -- `z` is in fact the integer point `y − q − t`.
  set zint : Fin ℓ → ℤ := y - q - t
  have hz_eq : z = fun i ↦ (zint i : ℝ) := by
    funext i
    have h := hdecomp i
    have hzi : (zint i : ℝ) = (y i : ℝ) - (q i : ℝ) - (t i : ℝ) := by
      have hz0 : zint i = y i - q i - t i := rfl
      rw [hz0]
      push_cast
      ring
    rw [hzi]
    linarith
  rw [hz_eq] at hzZ
  obtain ⟨S, hS, hclose⟩ := exists_subset_sum_sub_le_int hzZ hwX0 hwX
  set s : Fin ℓ → ℤ := ∑ a ∈ S, a
  set r : Fin ℓ → ℤ := zint - s
  have htspan : t ∈ Submodule.span ℤ (Set.range P.step) :=
    GAP.smul_toFinset_subset_span hPh (K / 2) (Finset.mem_coe.mpr ht)
  have hsspan : s ∈ Submodule.span ℤ (Set.range P.step) :=
    Submodule.sum_mem _ fun a ha ↦
      hXspan a (Finset.mem_sdiff.mp (hS ha)).1
  have hrspan : r ∈ Submodule.span ℤ (Set.range P.step) :=
    Submodule.sub_mem _
      (Submodule.sub_mem _ (Submodule.sub_mem _ hy hq) htspan) hsspan
  have hrbound : ∀ i, |(r i : ℝ)| ≤ (ℓ : ℝ) * wX i := by
    intro i
    have hi := hclose i
    have hrw : (r i : ℝ) = (zint i : ℝ) - (s i : ℝ) := by
      have hr : r i = zint i - s i := rfl
      rw [hr, Int.cast_sub]
    rw [hrw, abs_sub_comm]
    exact hi
  have hrt : r + t ∈ (K • P).toFinset := habs r hrspan hrbound t ht
  have hqmem : q + (r + t) ∈ ((K • P).translate q).toFinset := by
    rw [GAP.mem_translate_iff]
    have hsub' : q + (r + t) - q = r + t := by
      ext i; simp [Pi.add_apply, Pi.sub_apply]
    rw [hsub']
    exact hrt
  have hcov : s + (q + (r + t)) ∈ GAP.subsetSumsL ((X \ X') ∪ X') :=
    subsetSumsL_add Finset.sdiff_disjoint
      (GAP.mem_subsetSumsL.mpr ⟨S, hS, rfl⟩) (htr hqmem)
  rw [Finset.sdiff_union_of_subset hX'] at hcov
  have key : s + (q + (r + t)) = y := by
    ext i
    have hr : r i = y i - q i - t i - s i := rfl
    simp only [Pi.add_apply, hr]
    ring
  rwa [key] at hcov

/-- **Assembled intersection step** (Theorem 4, paper §3.3): the two
subset-sum sets share a nonzero vector once (i) the `⟨Pᵢ⟩`-lattice
points of the box around `T` are covered by the respective subset sums
(the output of `mem_subsetSumsL_of_zonotope_translate` together with the
Lemma-14 fat boxes) and (ii) the box is large enough for the Minkowski
bound `2^d·covol(⟨P₁⟩∩⟨P₂⟩) ≤ ∏ rᵢ`.  The basepoint `T` is taken
integral and in both lattices; in the paper `T` is the common zonotope
point and the integrality is supplied by the `⟨Pᵢ⟩`-membership of `y`
together with the `qᵢ`-translate bookkeeping.  The `hTbig` hypothesis
says the box is strictly smaller than `T` in some coordinate, so the
output point `y = T + z` is nonzero. -/
theorem exists_ne_zero_subsetSum_inter {d : ℕ} [NeZero d]
    {X₁ X₂ : Finset (Fin d → ℤ)} {P₁ P₂ : GAP d d}
    (hL₁ : (gapLattice P₁).toAddSubgroup.index ≠ 0)
    (hL₂ : (gapLattice P₂).toAddSubgroup.index ≠ 0)
    {T : Fin d → ℤ}
    (hT1 : T ∈ gapLattice P₁) (hT2 : T ∈ gapLattice P₂)
    {r : Fin d → ℝ} (hr : ∀ i, 0 ≤ r i)
    (hTbig : ∃ i₀, r i₀ < |(T i₀ : ℝ)|)
    (hcovol : 2 ^ d *
        (((gapLattice P₁).toAddSubgroup.index *
          (gapLattice P₂).toAddSubgroup.index : ℕ) : ℝ) ≤ ∏ i, r i)
    (hcov₁ : ∀ y : Fin d → ℤ, y ∈ gapLattice P₁ →
        (∀ i, |((y - T) i : ℝ)| ≤ r i) → y ∈ GAP.subsetSumsL X₁)
    (hcov₂ : ∀ y : Fin d → ℤ, y ∈ gapLattice P₂ →
        (∀ i, |((y - T) i : ℝ)| ≤ r i) → y ∈ GAP.subsetSumsL X₂) :
    ∃ z : Fin d → ℤ, z ≠ 0 ∧ z ∈ GAP.subsetSumsL X₁ ∧
      z ∈ GAP.subsetSumsL X₂ := by
  obtain ⟨z, hz0, hz1, hz2, hzr⟩ := exists_ne_zero_mem_inf_mem_box
    (gapLattice P₁).toAddSubgroup (gapLattice P₂).toAddSubgroup
    hL₁ hL₂ hr hcovol
  set y := z + T
  have hz1' : z ∈ gapLattice P₁ := hz1
  have hz2' : z ∈ gapLattice P₂ := hz2
  have hy1 : y ∈ gapLattice P₁ := Submodule.add_mem _ hz1' hT1
  have hy2 : y ∈ gapLattice P₂ := Submodule.add_mem _ hz2' hT2
  have hbd : ∀ i, |((y - T) i : ℝ)| ≤ r i := by
    intro i
    have hyt : (y - T) i = z i := by
      change ((z + T) - T) i = z i
      simp [Pi.sub_apply, Pi.add_apply]
    rw [hyt]
    exact hzr i
  have hy0 : y ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hTbig
    intro h0
    have hc : (y i₀ : ℝ) = 0 := by rw [h0]; simp
    have he : (y i₀ : ℝ) = (T i₀ : ℝ) + (z i₀ : ℝ) := by
      change (((z + T) i₀ : ℤ) : ℝ) = _
      rw [Pi.add_apply, Int.cast_add, add_comm]
    rw [he] at hc
    have habs : |(T i₀ : ℝ)| = |(z i₀ : ℝ)| := by
      have hneg : (T i₀ : ℝ) = -(z i₀ : ℝ) := by linarith
      rw [hneg, abs_neg]
    linarith [hi₀, hzr i₀]
  exact ⟨y, hy0, hcov₁ y hy1 hbd, hcov₂ y hy2 hbd⟩

end Covering

end Nonaveraging
