import Nonaveraging.GAP
import Nonaveraging.GeoNumbers
import Nonaveraging.ConvexBody

/-!
# Discrete John, GAP covolumes, and the lattice-intersection step

Supporting lemmas for `embedded_in_mu_convex_position` (Theorem 4 of
arXiv:2410.14624).  The remaining gap in `Structure.lean` is the
Lemma 11–14 core: one must show that the subset-sum sets of the two
shifted pieces share a nonzero vector.

* **§A** packages `B ∩ ℤ^d` (`intPoints`, `intPointsFinset`) and the
  centered progression `P(𝐯,𝐍) = {∑ nᵢ vᵢ : |nᵢ| ≤ Nᵢ}` as `GAP.centered`.
* **§B** is Lemma 7 (discrete John): `exists_progBox_sandwich` is the
  qualitative version (proved, from `GeoNumbers.discrete_john`);
  `discrete_john_strong` is the faithful uniform statement, proved from
  `exists_zbasis_adapted`, which in turn reduces to the single remaining
  gap `exists_zbasis_mahler` (the Mahler-form basis bound extracted from
  Minkowski's second theorem).
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
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact ⟨0, hB0, by simp⟩
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      exact mem_smul_add hBc hB0 (hw a (Finset.mem_insert_self _ _))
        (Finset.sum_nonneg fun i hi ↦ hw i (Finset.mem_insert_of_mem hi))
        (ht a (Finset.mem_insert_self _ _))
        (ih (fun i hi ↦ hw i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ ht i (Finset.mem_insert_of_mem hi)))

/-- For convex `B ∋ 0`, `t • B ⊆ B` when `0 ≤ t ≤ 1`. -/
theorem smul_self_subset (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • B ⊆ B := by
  rintro x ⟨y, hy, rfl⟩
  have h := hBc hB0 hy (sub_nonneg.mpr ht1) ht0 (by ring)
  simpa using h

/-! ### Successive minima and the Mahler basis for bounded `B`

The following machinery attacks parts (a) and (b) of the classical proof
of `exists_zbasis_mahler_core` (see its docstring): successive minima for
a merely *bounded* symmetric convex `B` (living inside `intSpan B`, the
`ℝ`-span of the integer points of `B`), and the Mahler flag-completion
lemma over `ℤ`.  The remaining gap is only the Minkowski-second-theorem
pairing bound `mahler_coord_bound`. -/

/-- The embedding `ℤ^d ↪ ℝ^d` as an `Int.castRingHom`-semilinear map. -/
def intVecLin : (Fin d → ℤ) →ₛₗ[Int.castRingHom ℝ] (Fin d → ℝ) where
  toFun := intVec
  map_add' := intVec_add
  map_smul' := fun n z ↦ intVec_smul n z

@[simp] theorem intVecLin_apply (z : Fin d → ℤ) :
    intVecLin z = intVec z := rfl

theorem intVecLin_injective :
    Function.Injective (intVecLin : (Fin d → ℤ) →ₛₗ[Int.castRingHom ℝ]
      (Fin d → ℝ)) := intVec_injective

/-- The `ℝ`-span of the integer points of `B`; the successive minima of
`B` with respect to `ℤ^d` live inside this subspace (points outside are
not absorbed by `B`, so `gauge B` is degenerate there). -/
def intSpan (B : Set (Fin d → ℝ)) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (intVec '' (intVec ⁻¹' B))

theorem intVec_mem_intSpan {z : Fin d → ℤ} (hz : intVec z ∈ B) :
    intVec z ∈ intSpan B :=
  Submodule.subset_span ⟨z, hz, rfl⟩

theorem intSpan_le_span (B : Set (Fin d → ℝ)) :
    intSpan B ≤ Submodule.span ℝ B :=
  Submodule.span_mono (Set.image_preimage_subset _ _)

/-- For convex symmetric `B ∋ 0`, every point of `span B` is absorbed:
`x ∈ span B → x ∈ r • B` for some `r > 0`. -/
theorem exists_pos_smul_mem_of_mem_span (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) (hBs : ∀ x ∈ B, -x ∈ B) {x : Fin d → ℝ}
    (hx : x ∈ Submodule.span ℝ B) :
    ∃ r : ℝ, 0 < r ∧ x ∈ r • B := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, ⟨y, hy, one_smul ℝ _⟩⟩
  | zero => exact ⟨1, one_pos, ⟨0, hB0, by simp⟩⟩
  | add y hy_mem z hz_mem ihy ihz =>
      obtain ⟨r₁, hr₁, hyr⟩ := ihy
      obtain ⟨r₂, hr₂, hzr⟩ := ihz
      exact ⟨r₁ + r₂, add_pos hr₁ hr₂,
        mem_smul_add hBc hB0 hr₁.le hr₂.le hyr hzr⟩
  | smul a y hy_mem ihy =>
      obtain ⟨r, hr, hyr⟩ := ihy
      rcases eq_or_lt_of_le (abs_nonneg a) with ha | ha
      · -- `a = 0`: `a • y = 0 ∈ 1 • B`
        have : a = 0 := abs_eq_zero.mp ha.symm
        subst this
        rw [zero_smul]
        exact ⟨1, one_pos, ⟨0, hB0, by simp⟩⟩
      · obtain ⟨y', hy', rfl⟩ := Set.mem_smul_set.mp hyr
        rcases le_or_gt 0 a with ha0 | ha0
        · refine ⟨|a| * r, mul_pos ha hr, ⟨y', hy', ?_⟩⟩
          rw [smul_smul, abs_of_nonneg ha0]
        · refine ⟨|a| * r, mul_pos ha hr, ⟨-y', hBs _ hy', ?_⟩⟩
          simp only [smul_smul, abs_of_neg ha0, neg_mul, neg_smul,
            smul_neg, neg_neg]

/-- For convex symmetric bounded `B ∋ 0`, an absorbed point `x` of gauge
strictly below `t` lies in `t • B`.  (No openness needed.) -/
theorem mem_smul_of_gauge_lt (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    (hBs : ∀ x ∈ B, -x ∈ B) {x : Fin d → ℝ}
    (hx : x ∈ Submodule.span ℝ B) {t : ℝ} (ht : gauge B x < t) :
    x ∈ t • B := by
  obtain ⟨r₀, hr₀, hxr₀⟩ := exists_pos_smul_mem_of_mem_span hBc hB0 hBs hx
  have hne : {r : ℝ | 0 < r ∧ x ∈ r • B}.Nonempty := ⟨r₀, hr₀, hxr₀⟩
  obtain ⟨r, ⟨hr0, hxr⟩, hrt⟩ :=
    exists_lt_of_csInf_lt hne (show gauge B x < t from ht)
  have htp : (0 : ℝ) < t := hr0.trans hrt
  have hsub : r • B ⊆ t • B := by
    have h1 : (r / t) • B ⊆ B :=
      smul_self_subset hBc hB0 (div_nonneg hr0.le htp.le)
        ((div_le_one htp).mpr hrt.le)
    calc r • B = t • ((r / t) • B) := by
          rw [smul_smul, mul_div_cancel₀ r htp.ne']
      _ ⊆ t • B := Set.smul_set_mono h1
  exact hsub hxr

/-- For convex symmetric bounded `B ∋ 0`, a nonzero absorbed point has
positive gauge. -/
theorem gauge_pos_of_mem_span (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    (hBs : ∀ x ∈ B, -x ∈ B) (hBb : Bornology.IsBounded B) {x : Fin d → ℝ}
    (hx : x ∈ Submodule.span ℝ B) (hx0 : x ≠ 0) : 0 < gauge B x := by
  obtain ⟨R, hR⟩ := hBb.subset_closedBall (0 : Fin d → ℝ)
  obtain ⟨r₀, hr₀, hxr₀⟩ := exists_pos_smul_mem_of_mem_span hBc hB0 hBs hx
  have hne : {r : ℝ | 0 < r ∧ x ∈ r • B}.Nonempty := ⟨r₀, hr₀, hxr₀⟩
  have hRpos : 0 < R := by
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hxr₀
    have hy0 : y ≠ 0 := fun h ↦ by simp [h] at hx0
    have : ‖y‖ ≤ R := mem_closedBall_zero_iff.mp (hR hy)
    exact (norm_pos_iff.mpr hy0).trans_le this
  apply lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hx0) hRpos)
  apply le_csInf hne
  rintro r ⟨hr0, hxr⟩
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hxr
  have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.mp (hR hy)
  rw [div_le_iff₀ hRpos]
  calc ‖r • y‖ = r * ‖y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hr0.le]
    _ ≤ r * R := mul_le_mul_of_nonneg_left hyR hr0.le

/-- A bounded set contains only finitely many integer vectors of bounded
gauge inside `intSpan B` — the bounded-`B` replacement of
`GeoNumbers.finite_intVec_gauge_le`. -/
theorem finite_intVec_gauge_le_of_mem_intSpan (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) (hBs : ∀ x ∈ B, -x ∈ B)
    (hBb : Bornology.IsBounded B) (C : ℝ) :
    Set.Finite {z : Fin d → ℤ |
      intVec z ∈ intSpan B ∧ gauge B (intVec z) ≤ C} := by
  obtain ⟨R, hR⟩ := hBb.subset_closedBall (0 : Fin d → ℝ)
  have hR0 : 0 ≤ R := Metric.nonempty_closedBall.mp ⟨0, hR hB0⟩
  set D : ℝ := max C 0 + 1 with hD
  have hDpos : (0 : ℝ) < D := by rw [hD]; linarith [le_max_right C 0]
  have hCD : C < D := by rw [hD]; linarith [le_max_left C 0]
  have hsub : D • B ⊆ Metric.closedBall (0 : Fin d → ℝ) (D * R) := by
    calc D • B ⊆ D • Metric.closedBall 0 R := fun x hx ↦ by
          obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
          exact Set.smul_mem_smul_set (hR hy)
      _ = Metric.closedBall (D • (0 : Fin d → ℝ)) (‖D‖ * R) :=
          smul_closedBall D _ hR0
      _ = Metric.closedBall 0 (D * R) := by
          rw [smul_zero, Real.norm_of_nonneg hDpos.le]
  refine Set.Finite.subset
    (Set.Finite.pi (t := fun i ↦ Set.Icc (-(⌈D * R⌉₊ : ℤ)) (⌈D * R⌉₊ : ℤ))
      fun i ↦ Set.finite_Icc _ _) ?_
  intro z hz
  rw [Set.mem_univ_pi]
  intro i
  obtain ⟨hzV, hzC⟩ := hz
  have hxD : intVec z ∈ D • B :=
    mem_smul_of_gauge_lt hBc hB0 hBs (intSpan_le_span _ hzV)
      (hzC.trans_lt hCD)
  have hx : intVec z ∈ Metric.closedBall (0 : Fin d → ℝ) (D * R) :=
    hsub hxD
  have hzi : |(z i : ℝ)| ≤ D * R := by
    calc |(z i : ℝ)| = ‖intVec z i‖ := by
          rw [intVec_apply, Real.norm_eq_abs]
      _ ≤ ‖intVec z‖ := norm_le_pi_norm _ i
      _ ≤ D * R := mem_closedBall_zero_iff.mp hx
  rw [Set.mem_Icc, ← abs_le]
  have h5 : ((|z i| : ℤ) : ℝ) ≤ ((⌈D * R⌉₊ : ℤ) : ℝ) := by
    rw [Int.cast_abs, Int.cast_natCast]
    exact hzi.trans (Nat.le_ceil _)
  exact Int.cast_le.mp h5

/-- **Greedy minimization inside `intSpan B`**: if `S` is a proper
subspace of `intSpan B`, some integer vector with `intVec z ∈
intSpan B \ S` minimizes `gauge B` among such vectors. -/
theorem exists_intVec_min_gauge_intSpan (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) (hBs : ∀ x ∈ B, -x ∈ B)
    (hBb : Bornology.IsBounded B) (S : Submodule ℝ (Fin d → ℝ))
    (hS : S < intSpan B) :
    ∃ z : Fin d → ℤ, intVec z ∈ intSpan B ∧ intVec z ∉ S ∧
      ∀ z' : Fin d → ℤ, intVec z' ∈ intSpan B → intVec z' ∉ S →
        gauge B (intVec z) ≤ gauge B (intVec z') := by
  classical
  obtain ⟨u, huB, huS⟩ : ∃ u : Fin d → ℤ, intVec u ∈ B ∧ intVec u ∉ S := by
    by_contra h
    push Not at h
    have hsub : intSpan B ≤ S := by
      rw [intSpan, Submodule.span_le]
      rintro x ⟨z, hz, rfl⟩
      exact h z hz
    exact absurd (le_antisymm hS.le hsub) (ne_of_lt hS)
  -- the finite minimizing set
  have huV : intVec u ∈ intSpan B := intVec_mem_intSpan huB
  set F : Set (Fin d → ℤ) := {z | intVec z ∈ intSpan B ∧ intVec z ∉ S ∧
      gauge B (intVec z) ≤ gauge B (intVec u)} with hF
  have hFfin : F.Finite :=
    (finite_intVec_gauge_le_of_mem_intSpan hBc hB0 hBs hBb _).subset
      fun z hz ↦ ⟨hz.1, hz.2.2⟩
  obtain ⟨z, hzF, hzmin⟩ :=
    Set.exists_min_image F (fun z ↦ gauge B (intVec z)) hFfin
      ⟨u, huV, huS, le_rfl⟩
  refine ⟨z, hzF.1, hzF.2.1, fun z' hz'V hz'S ↦ ?_⟩
  by_cases hzz : gauge B (intVec z') ≤ gauge B (intVec u)
  · exact hzmin z' ⟨hz'V, hz'S, hzz⟩
  · exact (hzF.2.2).trans (not_le.mp hzz).le

/-- `Vᵢ` for an integer family `u`: the `ℝ`-span of `u₀,…,u_{i-1}`
(more precisely, of the `uⱼ` with `j < i`). -/
def flagSpan (u : Fin d → Fin d → ℤ) (i : ℕ) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (Set.range fun j : {j : Fin d // (j : ℕ) < i} ↦
    intVec (u j))

/-- `Lᵢ = Vᵢ ∩ ℤ^d`, a pure `ℤ`-submodule of `ℤ^d` (pure because `Vᵢ` is
a linear subspace: `n • intVec z ∈ Vᵢ` with `n ≠ 0` implies
`intVec z ∈ Vᵢ`). -/
def flagLattice (u : Fin d → Fin d → ℤ) (i : ℕ) : Submodule ℤ (Fin d → ℤ) :=
  (flagSpan u i).comap intVecLin

theorem mem_flagLattice {u : Fin d → Fin d → ℤ} {i : ℕ} {z : Fin d → ℤ} :
    z ∈ flagLattice u i ↔ intVec z ∈ flagSpan u i :=
  Iff.rfl

theorem flagSpan_mono {u : Fin d → Fin d → ℤ} {i j : ℕ} (h : i ≤ j) :
    flagSpan u i ≤ flagSpan u j := by
  apply Submodule.span_mono
  rintro x ⟨l, rfl⟩
  exact ⟨⟨l, lt_of_lt_of_le l.2 h⟩, rfl⟩

theorem flagLattice_mono {u : Fin d → Fin d → ℤ} {i j : ℕ} (h : i ≤ j) :
    flagLattice u i ≤ flagLattice u j :=
  fun _ hx ↦ flagSpan_mono h hx

theorem mem_flagLattice_succ_self (u : Fin d → Fin d → ℤ) (i : Fin d) :
    u i ∈ flagLattice u ((i : ℕ) + 1) :=
  Submodule.subset_span ⟨⟨i, Nat.lt_succ_self (i : ℕ)⟩, rfl⟩

theorem flagLattice_zero (u : Fin d → Fin d → ℤ) : flagLattice u 0 = ⊥ := by
  have hempty : (Set.range fun j : {j : Fin d // (j:ℕ) < 0} ↦
      intVec (u j)) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨j, -⟩
    exact absurd j.2 (by simp)
  have h0 : flagSpan u 0 = ⊥ := by
    rw [flagSpan, hempty, Submodule.span_empty]
  ext z
  rw [flagLattice, Submodule.mem_comap, intVecLin_apply, h0,
    Submodule.mem_bot, Submodule.mem_bot]
  constructor
  · intro hz
    exact intVec_injective (by rw [hz, intVec_zero])
  · intro hz
    rw [hz, intVec_zero]

/-- **Successive minima for a bounded (not necessarily open) symmetric
convex body** — the bounded-`B` generalization of
`GeoNumbers.exists_succMinima`, with successive-minima vectors drawn
from `intSpan B`, the `ℝ`-span of `B ∩ ℤ^d`.  Produces a full `ℝ`-basis
`u` of integer vectors whose first `r = dim(intSpan B)` members lie in
`intSpan B`, `uᵢ` minimizing `gauge B` among integer vectors of
`intSpan B` outside `Vᵢ = span{u₀,…,u_{i-1}}`; in particular
`Vᵣ = intSpan B`, so every integer point of `B` lies in `Vᵣ`. -/
theorem exists_succMinima_bounded (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) (hBs : ∀ x ∈ B, -x ∈ B)
    (hBb : Bornology.IsBounded B) :
    ∃ (r : ℕ) (u : Fin d → Fin d → ℤ),
      r = Module.finrank ℝ ↥(intSpan B) ∧
      LinearIndependent ℝ (fun i ↦ intVec (u i)) ∧
      (∀ i : Fin d, (i : ℕ) < r → intVec (u i) ∈ intSpan B) ∧
      (∀ i : Fin d, (i : ℕ) < r → ∀ z : Fin d → ℤ,
          intVec z ∈ intSpan B → intVec z ∉ flagSpan u (i : ℕ) →
          gauge B (intVec (u i)) ≤ gauge B (intVec z)) ∧
      flagSpan u r = intSpan B := by
  classical
  -- We build `u` by induction on `k ≤ d`.  The invariant: `intVec ∘ u`
  -- is `ℝ`-linearly independent, and every index `j` whose
  -- predecessor-span `Sⱼ` is a proper subspace of `intSpan B` was picked
  -- greedily in `intSpan B ∖ Sⱼ`.
  suffices hsuff : ∀ k : ℕ, k ≤ d → ∃ u : Fin k → (Fin d → ℤ),
      LinearIndependent ℝ (fun i ↦ intVec (u i)) ∧
      ∀ j : Fin k,
        Submodule.span ℝ (Set.range
            fun l : {l : Fin k // (l : ℕ) < (j : ℕ)} ↦ intVec (u l)) <
          intSpan B →
        intVec (u j) ∈ intSpan B ∧
        ∀ z : Fin d → ℤ, intVec z ∈ intSpan B →
          intVec z ∉ Submodule.span ℝ (Set.range
            fun l : {l : Fin k // (l : ℕ) < (j : ℕ)} ↦ intVec (u l)) →
          gauge B (intVec (u j)) ≤ gauge B (intVec z) by
    obtain ⟨u, huI, huM⟩ := hsuff d le_rfl
    set r := Module.finrank ℝ ↥(intSpan B) with hr
    have hrd : r ≤ d := by
      rw [hr]
      calc Module.finrank ℝ ↥(intSpan B)
          ≤ Module.finrank ℝ (Fin d → ℝ) := Submodule.finrank_le _
        _ = d := by
            rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have hcard : ∀ i : ℕ, i ≤ d →
        Fintype.card {l : Fin d // (l : ℕ) < i} = i := by
      intro i hi
      let e : Fin i ≃ {l : Fin d // (l : ℕ) < i} :=
        { toFun := fun j ↦ ⟨⟨j, j.isLt.trans_le hi⟩, j.isLt⟩
          invFun := fun j ↦ ⟨(j : Fin d).1, j.2⟩
          left_inv := fun j ↦ by ext; rfl
          right_inv := fun j ↦ by ext; rfl }
      rw [← Fintype.card_congr e, Fintype.card_fin]
    have hfinrank : ∀ i : ℕ, i ≤ d →
        Module.finrank ℝ ↥(flagSpan u i) ≤ i := by
      intro i hi
      show Module.finrank ℝ ↥(Submodule.span ℝ (Set.range
          fun j : {j : Fin d // (j:ℕ) < i} ↦ intVec (u j))) ≤ i
      calc Module.finrank ℝ ↥(Submodule.span ℝ (Set.range
              fun j : {j : Fin d // (j:ℕ) < i} ↦ intVec (u j)))
          ≤ (Set.range fun j : {j : Fin d // (j:ℕ) < i} ↦
              intVec (u j)).toFinset.card := finrank_span_le_card _
        _ = (Finset.univ.image fun j : {j : Fin d // (j:ℕ) < i} ↦
              intVec (u j)).card := by rw [Set.toFinset_range]
        _ ≤ Finset.univ.card := Finset.card_image_le
        _ = Fintype.card {l : Fin d // (l:ℕ) < i} := Finset.card_univ
        _ = i := hcard i hi
    -- `flagSpan u i ≤ intSpan B` whenever `i ≤ r`
    have hle : ∀ i : ℕ, i ≤ r → flagSpan u i ≤ intSpan B := by
      intro i
      induction i with
      | zero =>
          intro _
          show Submodule.span ℝ (Set.range
              fun j : {j : Fin d // (j:ℕ) < 0} ↦ intVec (u j)) ≤ intSpan B
          rw [Submodule.span_le]
          rintro x ⟨j, -⟩
          exact absurd j.2 (by simp)
      | succ i ih =>
          intro hir
          have hii : i ≤ r := Nat.le_of_succ_le hir
          show Submodule.span ℝ (Set.range
              fun j : {j : Fin d // (j:ℕ) < i+1} ↦ intVec (u j)) ≤
            intSpan B
          rw [Submodule.span_le]
          rintro x ⟨l, rfl⟩
          have hsub : flagSpan u (l : ℕ) ≤ intSpan B :=
            (flagSpan_mono (Nat.lt_succ_iff.mp l.2)).trans (ih hii)
          have hll : flagSpan u (l : ℕ) < intSpan B := by
            refine lt_of_le_of_ne hsub ?_
            intro heq
            have hfr := hfinrank (l : ℕ) (l.1.isLt.le)
            rw [heq, ← hr] at hfr
            have hlr : (l : ℕ) < r := (Nat.lt_succ_iff.mp l.2).trans_lt hir
            exact absurd (hfr.trans_lt hlr) (lt_irrefl _)
          exact (huM l hll).1
    -- `flagSpan u i` is a proper subspace of `intSpan B` for `i < r`
    have hlt : ∀ i : Fin d, (i : ℕ) < r →
        flagSpan u (i : ℕ) < intSpan B := by
      intro i hi
      refine lt_of_le_of_ne (hle (i : ℕ) hi.le) ?_
      intro heq
      have hfr := hfinrank (i : ℕ) i.isLt.le
      rw [heq, ← hr] at hfr
      exact absurd (hfr.trans_lt hi) (lt_irrefl _)
    refine ⟨r, u, rfl, huI, fun i hi ↦ (huM i (hlt i hi)).1,
      fun i hi ↦ (huM i (hlt i hi)).2, ?_⟩
    -- `flagSpan u r = intSpan B` by equality of finranks
    apply Submodule.eq_of_le_of_finrank_eq (hle r le_rfl)
    rw [← hr]
    show Module.finrank ℝ ↥(Submodule.span ℝ (Set.range
        fun j : {j : Fin d // (j:ℕ) < r} ↦ intVec (u j))) = r
    have hind : LinearIndependent ℝ
        (fun l : {l : Fin d // (l:ℕ) < r} ↦ intVec (u l)) :=
      huI.comp Subtype.val Subtype.coe_injective
    rw [finrank_span_eq_card hind, hcard r hrd]
  -- the induction on `k`
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨fun i ↦ i.elim0, linearIndependent_empty_type,
        fun i ↦ i.elim0⟩
  | succ k ih =>
      intro hk
      obtain ⟨u, huI, huM⟩ := ih (Nat.le_of_succ_le hk)
      set S := Submodule.span ℝ
        (Set.range fun j : Fin k ↦ intVec (u j)) with hSdef
      have hSne : S ≠ ⊤ := by
        intro htop
        have hle : Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ k := by
          calc Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ))
              = Module.finrank ℝ ↥S := by rw [htop]
            _ ≤ (Set.range fun j : Fin k ↦ intVec (u j)).toFinset.card :=
                finrank_span_le_card _
            _ ≤ Fintype.card (Fin k) := by
                rw [Set.toFinset_range]
                exact Finset.card_image_le
            _ = k := Fintype.card_fin _
        rw [finrank_top, Module.finrank_fintype_fun_eq_card,
          Fintype.card_fin] at hle
        omega
      by_cases hSV : S < intSpan B
      · -- greedy step: minimize `gauge` over `intSpan B ∖ S`
        obtain ⟨v, hvV, hvS, hvMin⟩ :=
          exists_intVec_min_gauge_intSpan hBc hB0 hBs hBb S hSV
        refine ⟨Fin.snoc u v, ?_, ?_⟩
        · have hcomp : Fin.snoc (fun i ↦ intVec (u i)) (intVec v) =
              fun i ↦ intVec ((Fin.snoc u v : Fin (k+1) → Fin d → ℤ) i) :=
            (Fin.comp_snoc intVec u v).symm
          rw [← hcomp, linearIndependent_finSnoc]
          exact ⟨huI, hvS⟩
        · intro j hj
          by_cases hjk : (j : ℕ) < k
          · have hrw : (Set.range fun l : {l : Fin (k+1) //
                    (l : ℕ) < (j : ℕ)} ↦
                  intVec ((Fin.snoc u v : Fin (k+1) → Fin d → ℤ) l)) =
                Set.range fun l : {l : Fin k // (l : ℕ) < (j : ℕ)} ↦
                  intVec (u l) := by
              ext x
              constructor
              · rintro ⟨l, rfl⟩
                have hlk : (l : Fin (k+1)).1 < k := lt_trans l.2 hjk
                refine ⟨⟨⟨(l : Fin (k+1)).1, hlk⟩, l.2⟩, ?_⟩
                show intVec (u ⟨(l : Fin (k+1)).1, hlk⟩) =
                    intVec ((Fin.snoc u v : Fin (k+1) → Fin d → ℤ) ↑l)
                conv_rhs =>
                  rw [show (l : Fin (k+1)) =
                        Fin.castSucc ⟨(l : Fin (k+1)).1, hlk⟩
                        from Fin.ext rfl]
                rw [Fin.snoc_castSucc]
              · rintro ⟨l, rfl⟩
                refine ⟨⟨Fin.castSucc l.1, l.2⟩, ?_⟩
                show intVec ((Fin.snoc u v : Fin (k+1) → Fin d → ℤ)
                      (Fin.castSucc l.1)) = intVec (u l.1)
                rw [Fin.snoc_castSucc]
            rw [hrw] at hj ⊢
            have hje : (Fin.snoc u v : Fin (k+1) → Fin d → ℤ) j =
                u ⟨(j : ℕ), hjk⟩ := by
              conv_lhs =>
                rw [show j = Fin.castSucc ⟨(j : ℕ), hjk⟩
                      from Fin.ext rfl]
              rw [Fin.snoc_castSucc]
            rw [hje]
            exact huM ⟨(j : ℕ), hjk⟩ hj
          · have hik : (j : ℕ) = k := by
              have := j.isLt
              omega
            have hj' : j = Fin.last k :=
              Fin.ext (hik.trans (Fin.val_last k).symm)
            subst hj'
            have hrw : (Set.range fun l : {l : Fin (k+1) //
                    (l : ℕ) < (Fin.last k : ℕ)} ↦
                  intVec ((Fin.snoc u v : Fin (k+1) → Fin d → ℤ) l)) =
                Set.range fun j : Fin k ↦ intVec (u j) := by
              ext x
              constructor
              · rintro ⟨l, rfl⟩
                have hlk : (l : Fin (k+1)).1 < k :=
                  lt_of_lt_of_eq l.2 (Fin.val_last k)
                refine ⟨⟨(l : Fin (k+1)).1, hlk⟩, ?_⟩
                show intVec (u ⟨(l : Fin (k+1)).1, hlk⟩) =
                    intVec ((Fin.snoc u v : Fin (k+1) → Fin d → ℤ) ↑l)
                conv_rhs =>
                  rw [show (l : Fin (k+1)) =
                        Fin.castSucc ⟨(l : Fin (k+1)).1, hlk⟩
                        from Fin.ext rfl]
                rw [Fin.snoc_castSucc]
              · rintro ⟨l, rfl⟩
                refine ⟨⟨Fin.castSucc l, l.isLt⟩, ?_⟩
                show intVec ((Fin.snoc u v : Fin (k+1) → Fin d → ℤ)
                      (Fin.castSucc l)) = intVec (u l)
                rw [Fin.snoc_castSucc]
            rw [hrw, ← hSdef] at hj ⊢
            rw [Fin.snoc_last]
            exact ⟨hvV, hvMin⟩
      · -- extension step: pick a standard basis vector outside `S`
        obtain ⟨m, hm⟩ : ∃ m : Fin d, Pi.basisFun ℝ (Fin d) m ∉ S := by
          by_contra h
          push Not at h
          have htop : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ S := by
            rw [← (Pi.basisFun ℝ (Fin d)).span_eq, Submodule.span_le]
            rintro x ⟨i, rfl⟩
            exact h i
          exact hSne (top_unique htop)
        refine ⟨Fin.snoc u (Pi.single m 1), ?_, ?_⟩
        · have hcomp : Fin.snoc (fun i ↦ intVec (u i))
              (intVec (Pi.single m 1)) =
              fun i ↦ intVec ((Fin.snoc u (Pi.single m 1) :
                Fin (k+1) → Fin d → ℤ) i) :=
            (Fin.comp_snoc intVec u (Pi.single m 1)).symm
          rw [← hcomp, linearIndependent_finSnoc]
          refine ⟨huI, ?_⟩
          rw [basisFun_eq_intVec_single] at hm
          exact hm
        · intro j hj
          by_cases hjk : (j : ℕ) < k
          · have hrw : (Set.range fun l : {l : Fin (k+1) //
                    (l : ℕ) < (j : ℕ)} ↦
                  intVec ((Fin.snoc u (Pi.single m 1) :
                    Fin (k+1) → Fin d → ℤ) l)) =
                Set.range fun l : {l : Fin k // (l : ℕ) < (j : ℕ)} ↦
                  intVec (u l) := by
              ext x
              constructor
              · rintro ⟨l, rfl⟩
                have hlk : (l : Fin (k+1)).1 < k := lt_trans l.2 hjk
                refine ⟨⟨⟨(l : Fin (k+1)).1, hlk⟩, l.2⟩, ?_⟩
                show intVec (u ⟨(l : Fin (k+1)).1, hlk⟩) =
                    intVec ((Fin.snoc u (Pi.single m 1) :
                      Fin (k+1) → Fin d → ℤ) ↑l)
                conv_rhs =>
                  rw [show (l : Fin (k+1)) =
                        Fin.castSucc ⟨(l : Fin (k+1)).1, hlk⟩
                        from Fin.ext rfl]
                rw [Fin.snoc_castSucc]
              · rintro ⟨l, rfl⟩
                refine ⟨⟨Fin.castSucc l.1, l.2⟩, ?_⟩
                show intVec ((Fin.snoc u (Pi.single m 1) :
                      Fin (k+1) → Fin d → ℤ) (Fin.castSucc l.1)) =
                    intVec (u l.1)
                rw [Fin.snoc_castSucc]
            rw [hrw] at hj ⊢
            have hje : (Fin.snoc u (Pi.single m 1) :
                Fin (k+1) → Fin d → ℤ) j = u ⟨(j : ℕ), hjk⟩ := by
              conv_lhs =>
                rw [show j = Fin.castSucc ⟨(j : ℕ), hjk⟩
                      from Fin.ext rfl]
              rw [Fin.snoc_castSucc]
            rw [hje]
            exact huM ⟨(j : ℕ), hjk⟩ hj
          · have hik : (j : ℕ) = k := by
              have := j.isLt
              omega
            have hj' : j = Fin.last k :=
              Fin.ext (hik.trans (Fin.val_last k).symm)
            subst hj'
            have hrw : (Set.range fun l : {l : Fin (k+1) //
                    (l : ℕ) < (Fin.last k : ℕ)} ↦
                  intVec ((Fin.snoc u (Pi.single m 1) :
                    Fin (k+1) → Fin d → ℤ) l)) =
                Set.range fun j : Fin k ↦ intVec (u j) := by
              ext x
              constructor
              · rintro ⟨l, rfl⟩
                have hlk : (l : Fin (k+1)).1 < k :=
                  lt_of_lt_of_eq l.2 (Fin.val_last k)
                refine ⟨⟨(l : Fin (k+1)).1, hlk⟩, ?_⟩
                show intVec (u ⟨(l : Fin (k+1)).1, hlk⟩) =
                    intVec ((Fin.snoc u (Pi.single m 1) :
                      Fin (k+1) → Fin d → ℤ) ↑l)
                conv_rhs =>
                  rw [show (l : Fin (k+1)) =
                        Fin.castSucc ⟨(l : Fin (k+1)).1, hlk⟩
                        from Fin.ext rfl]
                rw [Fin.snoc_castSucc]
              · rintro ⟨l, rfl⟩
                refine ⟨⟨Fin.castSucc l, l.isLt⟩, ?_⟩
                show intVec ((Fin.snoc u (Pi.single m 1) :
                      Fin (k+1) → Fin d → ℤ) (Fin.castSucc l)) =
                    intVec (u l)
                rw [Fin.snoc_castSucc]
            rw [hrw, ← hSdef] at hj
            exact absurd hj hSV

/-! ### The flag determinant and the adapted `ℤ`-basis (part (b))

`intMat u` is the integer matrix with columns `u i`; replacing column
`i` by `z` and taking the determinant defines `flagDetLin u i`, a
`ℤ`-linear functional on `ℤ^d` which vanishes on `Lᵢ = flagLattice u i`
(because `Lᵢ ⊆ Vᵢ = span{u₀,…,u_{i-1}}` and `Dᵢ` is alternating in the
columns).  The image of `L_{i+1}` under `Dᵢ` is a `ℤ`-submodule of `ℤ`,
hence principal, generated by some `kᵢ ≠ 0`; a preimage `vᵢ` of `kᵢ`
splits `L_{i+1} = Lᵢ ⊕ ℤ·vᵢ`.  Iterating over `i` produces a `ℤ`-basis
adapted to the flag (`exists_mahler_zbasis`), and rounding the
`u`-coordinates of `vᵢ` to the nearest integer produces the shifted
Mahler basis vectors `vᵢ' = vᵢ - Σⱼ nⱼ uⱼ` with
`intVec vᵢ' = θᵢ uᵢ + Σⱼ θⱼ'' uⱼ`, `|θᵢ| ≤ 1`, `|θⱼ''| ≤ 1/2`
(`exists_mahler_shift`). -/

/-- `Fintype.card {l : Fin d // l < i} = i` for `i ≤ d`. -/
theorem card_flagSubtype (i : ℕ) (hi : i ≤ d) :
    Fintype.card {l : Fin d // (l : ℕ) < i} = i := by
  classical
  let e : Fin i ≃ {l : Fin d // (l : ℕ) < i} :=
    { toFun := fun j ↦ ⟨⟨j, j.isLt.trans_le hi⟩, j.isLt⟩
      invFun := fun j ↦ ⟨(j : Fin d).1, j.2⟩
      left_inv := fun j ↦ by ext; rfl
      right_inv := fun j ↦ by ext; rfl }
  rw [← Fintype.card_congr e, Fintype.card_fin]

/-- `intVec` commutes with finite sums over arbitrary index types. -/
theorem intVec_sum' {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℤ)) :
    intVec (∑ i ∈ s, f i) = ∑ i ∈ s, intVec (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, intVec_add, ih]

theorem intVec_sub (z z' : Fin d → ℤ) :
    intVec (z - z') = intVec z - intVec z' := by
  rw [sub_eq_add_neg, intVec_add, intVec_neg, sub_eq_add_neg]

/-- Splitting off the last index of a `{l < i+1}`-indexed sum. -/
theorem sum_flagSnoc {M : Type*} [AddCommMonoid M] (i : Fin d)
    (f : {l : Fin d // (l:ℕ) < (i:ℕ)+1} → M) :
    ∑ l : {l : Fin d // (l:ℕ) < (i:ℕ)+1}, f l =
      f ⟨i, Nat.lt_succ_self _⟩ +
        ∑ l : {l : Fin d // (l:ℕ) < (i:ℕ)},
          f ⟨l.1, Nat.lt_succ_of_lt l.2⟩ := by
  classical
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ ⟨i, Nat.lt_succ_self _⟩)]
  congr 1
  apply Finset.sum_bij
    (fun a ha ↦ (⟨a.1, by
      have hne : (a : Fin d).1 ≠ (i : ℕ) := fun h ↦
        (Finset.mem_erase.mp ha).1 (Subtype.ext (Fin.ext h))
      have := a.2
      omega⟩ : {l : Fin d // (l:ℕ) < (i:ℕ)}))
  · intro a _
    exact Finset.mem_univ _
  · intro a _ b₂ _ hab
    exact Subtype.ext (congrArg
      (fun x : {l : Fin d // (l:ℕ) < (i:ℕ)} ↦ x.val) hab)
  · intro l _
    refine ⟨⟨l.1, Nat.lt_succ_of_lt l.2⟩, ?_, rfl⟩
    rw [Finset.mem_erase]
    exact ⟨fun h ↦ absurd (congrArg Fin.val (congrArg Subtype.val h))
      (ne_of_lt l.2), Finset.mem_univ _⟩
  · intro a _
    rfl

/-- The integer matrix whose columns are `u 0, …, u_{d-1}`. -/
def intMat (u : Fin d → Fin d → ℤ) : Matrix (Fin d) (Fin d) ℤ :=
  Matrix.of fun a b ↦ u b a

/-- The real matrix whose columns are `intVec (u i)`. -/
def intMatCast (u : Fin d → Fin d → ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  (intMat u).map (Int.castRingHom ℝ)

theorem intMatCast_apply (u : Fin d → Fin d → ℤ) (a b : Fin d) :
    intMatCast u a b = (u b a : ℝ) := rfl

theorem intMatCast_det_ne_zero {u : Fin d → Fin d → ℤ}
    (huI : LinearIndependent ℝ fun i ↦ intVec (u i)) :
    (intMatCast u).det ≠ 0 := by
  classical
  have hunit := (Pi.basisFun ℝ (Fin d)).isUnit_det
    (basisOfLinearIndependentOfCardEqFinrank' _ huI (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]))
  rw [Pi.basisFun_det_apply, coe_basisOfLinearIndependentOfCardEqFinrank']
    at hunit
  have hmat : Matrix.of (fun i ↦ intVec (u i)) = (intMatCast u).transpose :=
    rfl
  rw [hmat, Matrix.det_transpose] at hunit
  exact hunit.ne_zero

theorem intMat_det_ne_zero {u : Fin d → Fin d → ℤ}
    (huI : LinearIndependent ℝ fun i ↦ intVec (u i)) :
    (intMat u).det ≠ 0 := by
  intro hd
  have h := RingHom.map_det (Int.castRingHom ℝ) (intMat u)
  rw [hd, map_zero, RingHom.mapMatrix_apply] at h
  exact intMatCast_det_ne_zero huI h.symm

/-- `flagDetLin u i z` — the determinant of `intMat u` with column `i`
replaced by `z`; a `ℤ`-linear functional on `ℤ^d` vanishing on
`Lᵢ = Vᵢ ∩ ℤ^d`. -/
def flagDetLin (u : Fin d → Fin d → ℤ) (i : Fin d) :
    (Fin d → ℤ) →ₗ[ℤ] ℤ where
  toFun z := ((intMat u).updateCol i z).det
  map_add' x y := Matrix.det_updateCol_add _ _ _ _
  map_smul' c x := by
    rw [smul_eq_mul]
    exact Matrix.det_updateCol_smul _ _ _ _

/-- The real analogue of `flagDetLin`. -/
def flagDetLinℝ (u : Fin d → Fin d → ℤ) (i : Fin d) :
    (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ((intMatCast u).updateCol i x).det
  map_add' x y := Matrix.det_updateCol_add _ _ _ _
  map_smul' c x := by
    rw [smul_eq_mul]
    exact Matrix.det_updateCol_smul _ _ _ _

theorem flagDetLin_apply (u : Fin d → Fin d → ℤ) (i : Fin d)
    (z : Fin d → ℤ) :
    flagDetLin u i z = ((intMat u).updateCol i z).det := rfl

theorem flagDetLinℝ_apply (u : Fin d → Fin d → ℤ) (i : Fin d)
    (x : Fin d → ℝ) :
    flagDetLinℝ u i x = ((intMatCast u).updateCol i x).det := rfl

theorem flagDetLin_u_self (u : Fin d → Fin d → ℤ) (i : Fin d) :
    flagDetLin u i (u i) = (intMat u).det := by
  show ((intMat u).updateCol i (u i)).det = _
  rw [show (u i) = fun a ↦ intMat u a i from rfl,
    Matrix.updateCol_eq_self]

theorem flagDetLinℝ_u_self (u : Fin d → Fin d → ℤ) (i : Fin d) :
    flagDetLinℝ u i (intVec (u i)) = (intMatCast u).det := by
  show ((intMatCast u).updateCol i (intVec (u i))).det = _
  rw [show intVec (u i) = fun a ↦ intMatCast u a i from rfl,
    Matrix.updateCol_eq_self]

theorem flagDetLin_u_of_ne {u : Fin d → Fin d → ℤ} {i j : Fin d}
    (h : j ≠ i) : flagDetLin u i (u j) = 0 := by
  show ((intMat u).updateCol i (u j)).det = 0
  rw [show (u j) = fun a ↦ intMat u a j from rfl]
  exact Matrix.det_updateCol_eq_zero h

theorem flagDetLinℝ_u_of_ne {u : Fin d → Fin d → ℤ} {i j : Fin d}
    (h : j ≠ i) : flagDetLinℝ u i (intVec (u j)) = 0 := by
  show ((intMatCast u).updateCol i (intVec (u j))).det = 0
  rw [show intVec (u j) = fun a ↦ intMatCast u a j from rfl]
  exact Matrix.det_updateCol_eq_zero h

/-- `flagDetLin` and `flagDetLinℝ` agree on integer vectors. -/
theorem flagDetLin_cast (u : Fin d → Fin d → ℤ) (i : Fin d)
    (z : Fin d → ℤ) :
    (flagDetLin u i z : ℝ) = flagDetLinℝ u i (intVec z) := by
  show (((intMat u).updateCol i z).det : ℝ) =
    ((intMatCast u).updateCol i (intVec z)).det
  have hmap : (intMatCast u).updateCol i (intVec z) =
      ((intMat u).updateCol i z).map (Int.castRingHom ℝ) := by
    ext a b
    rw [Matrix.map_apply]
    by_cases hb : b = i
    · subst hb
      rw [Matrix.updateCol_self, Matrix.updateCol_self]
      rfl
    · rw [Matrix.updateCol_ne hb, Matrix.updateCol_ne hb]
      rfl
  rw [hmap, ← RingHom.mapMatrix_apply]
  exact RingHom.map_det (Int.castRingHom ℝ) ((intMat u).updateCol i z)

/-- `Dᵢ` vanishes on `Vᵢ`. -/
theorem flagDetLinℝ_eq_zero_of_mem_flagSpan {u : Fin d → Fin d → ℤ}
    {i : Fin d} {x : Fin d → ℝ} (hx : x ∈ flagSpan u (i:ℕ)) :
    flagDetLinℝ u i x = 0 := by
  classical
  rw [flagSpan] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  rw [← hc, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul, flagDetLinℝ_u_of_ne, smul_zero]
  exact fun h ↦ absurd (congrArg Fin.val h) (ne_of_lt j.2)

/-- `Dᵢ` vanishes on `Lᵢ`. -/
theorem flagDetLin_eq_zero_of_mem_flagLattice {u : Fin d → Fin d → ℤ}
    {i : Fin d} {z : Fin d → ℤ} (hz : z ∈ flagLattice u (i:ℕ)) :
    flagDetLin u i z = 0 := by
  have h0 : (flagDetLin u i z : ℝ) = 0 := by
    rw [flagDetLin_cast]
    exact flagDetLinℝ_eq_zero_of_mem_flagSpan hz
  exact_mod_cast h0

/-- The converse vanishing statement: for `z ∈ L_{i+1}`, `Dᵢ z = 0`
forces `z ∈ Lᵢ`.  This is the key linear-algebra step in the flag
extension: `Dᵢ` reads off the `uᵢ`-coordinate of `intVec z`. -/
theorem mem_flagLattice_of_flagDetLin_eq_zero {u : Fin d → Fin d → ℤ}
    (huI : LinearIndependent ℝ fun i ↦ intVec (u i)) {i : Fin d}
    {z : Fin d → ℤ} (hz : z ∈ flagLattice u ((i:ℕ)+1))
    (hD : flagDetLin u i z = 0) :
    z ∈ flagLattice u (i:ℕ) := by
  rw [mem_flagLattice] at hz ⊢
  rw [flagSpan] at hz ⊢
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
  have hDi : flagDetLinℝ u i (intVec z) = 0 := by
    rw [← flagDetLin_cast, hD]
    simp
  rw [← hc] at hDi
  rw [map_sum] at hDi
  have hterm : ∀ l : {l : Fin d // (l:ℕ) < (i:ℕ)+1},
      flagDetLinℝ u i (intVec (u (l : Fin d))) =
        if (l : Fin d) = i then (intMatCast u).det else 0 := by
    intro l
    by_cases hl : (l : Fin d) = i
    · rw [if_pos hl, hl, flagDetLinℝ_u_self]
    · rw [if_neg hl, flagDetLinℝ_u_of_ne hl]
  have hDi2 : ∑ l : {l : Fin d // (l:ℕ) < (i:ℕ)+1},
      c l • flagDetLinℝ u i (intVec (u l)) = 0 := by
    rw [← hDi]
    exact Finset.sum_congr rfl fun l _ ↦ (map_smul _ _ _).symm
  rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_self _⟩
    (fun b _ hb ↦ by
      rw [hterm b, if_neg (fun h ↦ hb (Subtype.ext h)), smul_zero])
    (fun h ↦ absurd (Finset.mem_univ _) h)] at hDi2
  rw [hterm, if_pos rfl, smul_eq_mul] at hDi2
  have hci : c ⟨i, Nat.lt_succ_self _⟩ = 0 := by
    rcases mul_eq_zero.mp hDi2 with h | h
    · exact h
    · exact absurd h (intMatCast_det_ne_zero huI)
  rw [← hc, sum_flagSnoc i, hci, zero_smul, zero_add]
  apply Submodule.sum_mem
  intro l _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

/-- **The flag extension step.**  The image of `L_{i+1}` under the flag
determinant `Dᵢ` is a `ℤ`-submodule of `ℤ`, hence principal with
generator `kᵢ ≠ 0` (`kᵢ` divides `det(intMat u) ≠ 0`).  A preimage `vᵢ`
of `kᵢ` satisfies `L_{i+1} = Lᵢ ⊕ ℤ·vᵢ`: every `z ∈ L_{i+1}` has
`z - (Dᵢ z / kᵢ) • vᵢ ∈ Lᵢ`. -/
theorem exists_flag_extension {u : Fin d → Fin d → ℤ}
    (huI : LinearIndependent ℝ fun i ↦ intVec (u i)) (i : Fin d) :
    ∃ v : Fin d → ℤ,
      flagDetLin u i v ≠ 0 ∧
      v ∈ flagLattice u ((i:ℕ)+1) ∧
      ∀ z : Fin d → ℤ, z ∈ flagLattice u ((i:ℕ)+1) →
        ∃ m : ℤ, z - m • v ∈ flagLattice u (i:ℕ) := by
  classical
  let I : Ideal ℤ := (flagLattice u ((i:ℕ)+1)).map (flagDetLin u i)
  have hIprin : I.IsPrincipal := IsPrincipalIdealRing.principal I
  set k := Submodule.IsPrincipal.generator I with hk
  have hkI : k ∈ I := Submodule.IsPrincipal.generator_mem I
  have hkne : k ≠ 0 := by
    intro hk0
    have hIbot : I = ⊥ :=
      (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hk0
    have hmem : flagDetLin u i (u i) ∈ I :=
      Submodule.mem_map_of_mem (mem_flagLattice_succ_self u i)
    rw [flagDetLin_u_self, hIbot] at hmem
    rw [Submodule.mem_bot] at hmem
    exact intMat_det_ne_zero huI hmem
  obtain ⟨v, hvL, hvD⟩ := Submodule.mem_map.mp hkI
  refine ⟨v, ?_, hvL, ?_⟩
  · rw [hvD]; exact hkne
  · intro z hz
    have hDz : flagDetLin u i z ∈ I := Submodule.mem_map_of_mem hz
    obtain ⟨m, hm⟩ :=
      (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hDz
    refine ⟨m, mem_flagLattice_of_flagDetLin_eq_zero huI ?_ ?_⟩
    · exact Submodule.sub_mem _ hz (Submodule.smul_mem _ m hvL)
    · have hstep : flagDetLin u i (z - m • v) =
          flagDetLin u i z - m • flagDetLin u i v := by
        rw [map_sub, map_smul]
      rw [hstep, hvD, hm, sub_self]

/-- A family `v` is *adapted* to the flag of `u` when `vᵢ ∈ L_{i+1}`,
`Dᵢ vᵢ ≠ 0`, and every `z ∈ L_{i+1}` splits off an integer multiple of
`vᵢ` into `Lᵢ`. -/
def adaptedToFlag (u v : Fin d → Fin d → ℤ) : Prop :=
  (∀ i : Fin d, v i ∈ flagLattice u ((i:ℕ)+1)) ∧
  (∀ i : Fin d, flagDetLin u i (v i) ≠ 0) ∧
  (∀ i : Fin d, ∀ z : Fin d → ℤ, z ∈ flagLattice u ((i:ℕ)+1) →
    ∃ m : ℤ, z - m • v i ∈ flagLattice u (i:ℕ))

/-- An adapted family spans each flag lattice: `Lᵢ` is contained in
(hence equal to) the `ℤ`-span of `v₀,…,v_{i-1}`. -/
theorem adaptedToFlag_span {u v : Fin d → Fin d → ℤ}
    (had : adaptedToFlag u v) (i : ℕ) (hi : i ≤ d) :
    flagLattice u i ≤ Submodule.span ℤ
      (Set.range fun j : {j : Fin d // (j:ℕ) < i} ↦ v (j : Fin d)) := by
  classical
  induction i with
  | zero =>
      rw [flagLattice_zero]
      exact bot_le
  | succ i ih =>
      intro z hz
      have hid : i < d := Nat.lt_of_succ_le hi
      obtain ⟨m, hm⟩ := had.2.2 ⟨i, hid⟩ z hz
      have hsub : z = m • v ⟨i, hid⟩ + (z - m • v ⟨i, hid⟩) := by
        rw [add_comm, sub_add_cancel]
      have hmono : (Set.range fun j : {j : Fin d // (j:ℕ) < i} ↦
            v (j : Fin d)) ⊆
          Set.range fun j : {j : Fin d // (j:ℕ) < (i:ℕ)+1} ↦
            v (j : Fin d) := by
        rintro x ⟨j, rfl⟩
        exact ⟨⟨j.1, Nat.lt_succ_of_lt j.2⟩, rfl⟩
      rw [hsub]
      apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨⟨⟨i, hid⟩, Nat.lt_succ_self _⟩, rfl⟩)
      · exact Submodule.span_mono hmono
          (ih (Nat.le_of_succ_le hi) hm)

/-- An adapted family is `ℤ`-linearly independent: in a relation
`Σ cⱼ vⱼ = 0`, applying `Dᵢ` at the largest index with `cᵢ ≠ 0` yields
`cᵢ · Dᵢ vᵢ = 0`, a contradiction. -/
theorem adaptedToFlag_linearIndependent {u v : Fin d → Fin d → ℤ}
    (had : adaptedToFlag u v) : LinearIndependent ℤ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hgi
  let S := Finset.univ.filter fun j ↦ g j ≠ 0
  have hS : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgi⟩⟩
  set i₀ := S.max' hS
  have hi₀ : i₀ ∈ S := S.max'_mem hS
  have hgi₀ : g i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  have hmap : ∑ j : Fin d, g j • flagDetLin u i₀ (v j) = 0 := by
    have h := map_sum (flagDetLin u i₀)
      (fun j ↦ g j • v j) Finset.univ
    rw [hg, map_zero] at h
    have h' : ∑ j : Fin d, g j • flagDetLin u i₀ (v j) =
        ∑ j : Fin d, flagDetLin u i₀ (g j • v j) :=
      Finset.sum_congr rfl fun j _ ↦ (map_smul _ _ _).symm
    rw [h']
    exact h.symm
  rw [Finset.sum_eq_single i₀
    (fun b _ hb ↦ by
      by_cases hbS : b ∈ S
      · have hle : b ≤ i₀ := Finset.le_max' S b hbS
        have hlt : b < i₀ := lt_of_le_of_ne hle hb
        have hv : v b ∈ flagLattice u (i₀:ℕ) :=
          flagLattice_mono (Nat.succ_le_of_lt hlt) (had.1 b)
        rw [flagDetLin_eq_zero_of_mem_flagLattice hv, smul_zero]
      · have : g b = 0 := by
          by_contra h
          exact hbS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        rw [this, zero_smul])
    (fun h ↦ absurd (Finset.mem_univ _) h)] at hmap
  rw [smul_eq_mul] at hmap
  exact hgi₀ ((mul_eq_zero.mp hmap).resolve_right (had.2.1 i₀))

/-- An adapted family spans `ℤ^d`: `L_d = ℤ^d` since `V_d` contains the
`ℝ`-basis `intVec ∘ u`. -/
theorem adaptedToFlag_span_top {u v : Fin d → Fin d → ℤ}
    (huI : LinearIndependent ℝ fun i ↦ intVec (u i))
    (had : adaptedToFlag u v) :
    Submodule.span ℤ (Set.range v) = ⊤ := by
  classical
  have hfr : Module.finrank ℝ (Fin d → ℝ) = Fintype.card (Fin d) := by
    rw [Module.finrank_fintype_fun_eq_card]
  have htop : flagSpan u d = ⊤ := by
    have hsp := huI.span_eq_top_of_card_eq_finrank' hfr.symm
    rw [flagSpan]
    have hrange : (Set.range fun j : {j : Fin d // (j:ℕ) < d} ↦
        intVec (u j)) = Set.range fun j : Fin d ↦ intVec (u j) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨j.1, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨⟨j, j.isLt⟩, rfl⟩
    rw [hrange]
    exact hsp
  have hd : flagLattice u d = ⊤ := by
    rw [flagLattice, htop, Submodule.comap_top]
  have hrangev : (Set.range fun j : {j : Fin d // (j:ℕ) < d} ↦
      v (j : Fin d)) = Set.range v := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨j.1, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨⟨j, j.isLt⟩, rfl⟩
  rw [eq_top_iff]
  intro z _
  rw [← hrangev]
  exact adaptedToFlag_span had d le_rfl (by
    rw [hd]; exact Submodule.mem_top)

/-- **The adapted `ℤ`-basis (Mahler's basis lemma).**  Iterating
`exists_flag_extension` produces a `ℤ`-basis `v` of `ℤ^d` adapted to
the successive-minima flag: `vᵢ ∈ L_{i+1}` and `Lᵢ` is the `ℤ`-span of
`v₀,…,v_{i-1}`. -/
theorem exists_mahler_zbasis {u : Fin d → Fin d → ℤ}
    (huI : LinearIndependent ℝ fun i ↦ intVec (u i)) :
    ∃ v : Fin d → Fin d → ℤ, adaptedToFlag u v ∧
      LinearIndependent ℤ v ∧ Submodule.span ℤ (Set.range v) = ⊤ := by
  classical
  have hex : ∀ i : Fin d, ∃ w : Fin d → ℤ,
      flagDetLin u i w ≠ 0 ∧ w ∈ flagLattice u ((i:ℕ)+1) ∧
      ∀ z : Fin d → ℤ, z ∈ flagLattice u ((i:ℕ)+1) →
        ∃ m : ℤ, z - m • w ∈ flagLattice u (i:ℕ) :=
    fun i ↦ exists_flag_extension huI i
  choose v hv using hex
  have had : adaptedToFlag u v :=
    ⟨fun i ↦ (hv i).2.1, fun i ↦ (hv i).1, fun i ↦ (hv i).2.2⟩
  exact ⟨v, had, adaptedToFlag_linearIndependent had,
    adaptedToFlag_span_top huI had⟩

/-- The Mahler-shifted basis vector `vᵢ' = vᵢ - Σⱼ ⌈θⱼ⌋ uⱼ`, where `θ`
are the `u`-coordinates of `intVec (v i)` (below index `i+1`). -/
noncomputable def mahlerVec (u v : Fin d → Fin d → ℤ) (i : Fin d)
    (θ : {l : Fin d // (l:ℕ) < (i:ℕ)+1} → ℝ) : Fin d → ℤ :=
  v i - ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
    round (θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩) • u j

/-- The shifted vector has `u`-expansion `θᵢ uᵢ + Σⱼ θⱼ'' uⱼ` with
`|θⱼ''| ≤ 1/2` (nearest-integer rounding). -/
theorem intVec_mahlerVec {u v : Fin d → Fin d → ℤ} {i : Fin d}
    {θ : {l : Fin d // (l:ℕ) < (i:ℕ)+1} → ℝ}
    (hexp : intVec (v i) = ∑ l : {l : Fin d // (l:ℕ) < (i:ℕ)+1},
      θ l • intVec (u l)) :
    intVec (mahlerVec u v i θ) =
      θ ⟨i, Nat.lt_succ_self _⟩ • intVec (u i) +
        ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
          (θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩ -
            ((round (θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩) : ℤ) : ℝ)) •
            intVec (u j) := by
  classical
  have h1 : intVec (∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
      round (θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩) • u j) =
      ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
        ((round (θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩) : ℤ) : ℝ) •
          intVec (u j) := by
    rw [intVec_sum']
    exact Finset.sum_congr rfl fun j _ ↦ intVec_smul _ _
  show intVec (v i - ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
      round (θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩) • u j) = _
  rw [intVec_sub, h1, hexp, sum_flagSnoc, add_sub_assoc,
    ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [sub_smul]

/-- The `uᵢ`-coefficient of `vᵢ` in the `u`-basis has `|θᵢ| ≤ 1`:
`Dᵢ(vᵢ) | det(intMat u)` over `ℤ` (since `uᵢ = Σ_{j≤i} cⱼ vⱼ` with
`cᵢ·Dᵢvᵢ = det`), while `θᵢ·det = Dᵢvᵢ` over `ℝ`. -/
theorem abs_flagCoord_le_one {u v : Fin d → Fin d → ℤ}
    (huI : LinearIndependent ℝ fun i ↦ intVec (u i))
    (had : adaptedToFlag u v) (i : Fin d)
    {θ : {l : Fin d // (l:ℕ) < (i:ℕ)+1} → ℝ}
    (hexp : intVec (v i) = ∑ l, θ l • intVec (u l)) :
    |θ ⟨i, Nat.lt_succ_self _⟩| ≤ 1 := by
  classical
  have huL : u i ∈ Submodule.span ℤ
      (Set.range fun j : {j : Fin d // (j:ℕ) < (i:ℕ)+1} ↦
        v (j : Fin d)) :=
    adaptedToFlag_span had _ (Nat.succ_le_of_lt i.isLt)
      (mem_flagLattice_succ_self u i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp huL
  -- `detU = cᵢ · kᵢ` over `ℤ`
  have hdet : (intMat u).det =
      c ⟨i, Nat.lt_succ_self _⟩ * flagDetLin u i (v i) := by
    have h1 : flagDetLin u i (u i) =
        ∑ j : {j : Fin d // (j:ℕ) < (i:ℕ)+1},
          c j • flagDetLin u i (v j) := by
      conv_lhs => rw [← hc]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ map_smul _ _ _
    rw [flagDetLin_u_self] at h1
    rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_self _⟩] at h1
    · rw [smul_eq_mul] at h1; exact h1
    · intro b _ hb
      have hbv : (b : Fin d).1 ≠ (i : ℕ) := fun h ↦
        hb (Subtype.ext (Fin.ext h))
      have hlt : (b : Fin d).1 < (i : ℕ) := by
        have := b.2; omega
      rw [flagDetLin_eq_zero_of_mem_flagLattice
        (flagLattice_mono (Nat.succ_le_of_lt hlt) (had.1 b)), smul_zero]
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  -- `θᵢ · detU = kᵢ` over `ℝ`
  have hθ : θ ⟨i, Nat.lt_succ_self _⟩ * (intMatCast u).det =
      (flagDetLin u i (v i) : ℝ) := by
    have hD : flagDetLinℝ u i (intVec (v i)) =
        θ ⟨i, Nat.lt_succ_self _⟩ * (intMatCast u).det := by
      rw [hexp, map_sum]
      rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_self _⟩]
      · rw [map_smul, flagDetLinℝ_u_self, smul_eq_mul]
      · intro b _ hb
        have hbv : (b : Fin d) ≠ i := fun h ↦ hb (Subtype.ext h)
        rw [map_smul, flagDetLinℝ_u_of_ne hbv, smul_zero]
      · exact fun h ↦ absurd (Finset.mem_univ _) h
    rw [← flagDetLin_cast] at hD
    exact hD.symm
  have hdetcast : (intMatCast u).det = ((intMat u).det : ℝ) := by
    have h := RingHom.map_det (Int.castRingHom ℝ) (intMat u)
    rw [RingHom.mapMatrix_apply] at h
    exact h.symm
  rw [hdetcast] at hθ
  have hdet0 : (intMat u).det ≠ 0 := intMat_det_ne_zero huI
  have hci : c ⟨i, Nat.lt_succ_self _⟩ ≠ 0 := by
    intro h; rw [h, zero_mul] at hdet; exact hdet0 hdet
  -- `|θᵢ| = |kᵢ| / |detU| = 1/|cᵢ| ≤ 1`
  have hk : flagDetLin u i (v i) ≠ 0 := had.2.1 i
  have hk' : (flagDetLin u i (v i) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hθeq : θ ⟨i, Nat.lt_succ_self _⟩ =
      (flagDetLin u i (v i) : ℝ) / ((intMat u).det : ℝ) :=
    (eq_div_iff (Int.cast_ne_zero.mpr hdet0)).mpr hθ
  have hd' : ((intMat u).det : ℝ) =
      (c ⟨i, Nat.lt_succ_self _⟩ : ℝ) * (flagDetLin u i (v i) : ℝ) := by
    rw [hdet]; push_cast; ring
  rw [hθeq, abs_div, hd', abs_mul]
  have hcan : |(flagDetLin u i (v i) : ℝ)| /
      (|(c ⟨i, Nat.lt_succ_self _⟩ : ℝ)| * |(flagDetLin u i (v i) : ℝ)|) =
      1 / |(c ⟨i, Nat.lt_succ_self _⟩ : ℝ)| := by
    rw [mul_comm (|(c ⟨i, Nat.lt_succ_self _⟩ : ℝ)|), ← div_div,
      div_self (abs_ne_zero.mpr hk')]
  rw [hcan, one_div]
  exact inv_le_one_of_one_le₀
    (by exact_mod_cast Int.one_le_abs hci)

/-! ### Shifted basis: membership bounds and integer duality -/

/-- Triangle inequality for `gauge B` at points of `span B` — no
absorbency hypothesis needed. -/
theorem gauge_add_le_of_mem_span (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) (hBs : ∀ x ∈ B, -x ∈ B)
    {x y : Fin d → ℝ} (hx : x ∈ Submodule.span ℝ B)
    (hy : y ∈ Submodule.span ℝ B) :
    gauge B (x + y) ≤ gauge B x + gauge B y := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have h1 : x ∈ (gauge B x + ε / 2) • B :=
    mem_smul_of_gauge_lt hBc hB0 hBs hx (lt_add_of_pos_right _ (half_pos hε))
  have h2 : y ∈ (gauge B y + ε / 2) • B :=
    mem_smul_of_gauge_lt hBc hB0 hBs hy (lt_add_of_pos_right _ (half_pos hε))
  have hsum : x + y ∈ (gauge B x + gauge B y + ε) • B := by
    have h := mem_smul_add hBc hB0
      (add_nonneg (gauge_nonneg _) (by linarith))
      (add_nonneg (gauge_nonneg _) (by linarith)) h1 h2
    have heq : gauge B x + ε / 2 + (gauge B y + ε / 2) =
        gauge B x + gauge B y + ε := by ring
    rwa [heq] at h
  have hg := gauge_le_of_mem
    (add_nonneg (add_nonneg (gauge_nonneg _) (gauge_nonneg _)) hε.le) hsum
  linarith

/-- Sum version of the gauge triangle inequality on `span B`. -/
theorem gauge_sum_le_of_mem_span (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) (hBs : ∀ x ∈ B, -x ∈ B)
    {ι : Type*} (s : Finset ι) {f : ι → Fin d → ℝ}
    (hf : ∀ j ∈ s, f j ∈ Submodule.span ℝ B) :
    gauge B (∑ j ∈ s, f j) ≤ ∑ j ∈ s, gauge B (f j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [gauge_zero]
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      refine (gauge_add_le_of_mem_span hBc hB0 hBs
        (hf a (Finset.mem_insert_self _ _))
        (Submodule.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))).trans
        (add_le_add_right (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))) _)

/-- The shifted Mahler vector `v'ᵢ` has gauge bounded by
`(1 + i/2)·λᵢ`, hence lies in every larger dilation of `B`. -/
theorem mahlerVec_mem_smul (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    (hBs : ∀ x ∈ B, -x ∈ B) {u v : Fin d → Fin d → ℤ} {i : Fin d}
    {θ : {l : Fin d // (l:ℕ) < (i:ℕ)+1} → ℝ}
    (hexp : intVec (v i) = ∑ l : {l : Fin d // (l:ℕ) < (i:ℕ)+1},
      θ l • intVec (u l))
    (hθi : |θ ⟨i, Nat.lt_succ_self _⟩| ≤ 1)
    (huS : ∀ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
      intVec (u j) ∈ Submodule.span ℝ B)
    (huiS : intVec (u i) ∈ Submodule.span ℝ B)
    (hlam : ∀ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
      gauge B (intVec (u j)) ≤ gauge B (intVec (u i)))
    {t : ℝ} (ht : (1 + (i:ℝ)/2) * gauge B (intVec (u i)) < t) :
    intVec (mahlerVec u v i θ) ∈ t • B := by
  classical
  have hbal := balanced_of_symmetric hBc hB0 hBs
  set cj : {l : Fin d // (l:ℕ) < (i:ℕ)} → ℝ :=
    fun j ↦ θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩ -
      ((round (θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩) : ℤ) : ℝ) with hcj
  have hexp' : intVec (mahlerVec u v i θ) =
      θ ⟨i, Nat.lt_succ_self _⟩ • intVec (u i) +
        ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)}, cj j • intVec (u j) := by
    rw [intVec_mahlerVec hexp]
  have hspan1 : θ ⟨i, Nat.lt_succ_self _⟩ • intVec (u i) ∈
      Submodule.span ℝ B := Submodule.smul_mem _ _ huiS
  have hspan2 : (∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)}, cj j • intVec (u j)) ∈
      Submodule.span ℝ B :=
    Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (huS j)
  have hmem : intVec (mahlerVec u v i θ) ∈ Submodule.span ℝ B := by
    rw [hexp']; exact add_mem hspan1 hspan2
  have hcj_abs : ∀ j : {l : Fin d // (l:ℕ) < (i:ℕ)}, |cj j| ≤ 1/2 := by
    intro j
    show |(θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩ -
      ((round (θ ⟨j.1, Nat.lt_succ_of_lt j.2⟩) : ℤ) : ℝ))| ≤ 1/2
    exact abs_sub_round _
  have hgj : ∀ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
      gauge B (cj j • intVec (u j)) ≤
        (1/2 : ℝ) * gauge B (intVec (u i)) := by
    intro j
    rw [gauge_smul hbal, Real.norm_eq_abs]
    exact mul_le_mul (hcj_abs j) (hlam j) (gauge_nonneg _) (by norm_num)
  have hsum : (∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
        gauge B (cj j • intVec (u j))) ≤
        (i : ℝ)/2 * gauge B (intVec (u i)) := by
    calc _ ≤ ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
          (1/2 : ℝ) * gauge B (intVec (u i)) :=
        Finset.sum_le_sum fun j _ ↦ hgj j
      _ = (i : ℝ) * ((1/2 : ℝ) * gauge B (intVec (u i))) := by
        rw [Finset.sum_const, Finset.card_univ,
          card_flagSubtype i.val i.isLt.le, nsmul_eq_mul]
      _ = (i : ℝ)/2 * gauge B (intVec (u i)) := by ring
  have hgi : gauge B (θ ⟨i, Nat.lt_succ_self _⟩ • intVec (u i)) ≤
      gauge B (intVec (u i)) := by
    rw [gauge_smul hbal, Real.norm_eq_abs]
    calc |θ ⟨i, Nat.lt_succ_self _⟩| * gauge B (intVec (u i))
        ≤ 1 * gauge B (intVec (u i)) :=
          mul_le_mul_of_nonneg_right hθi (gauge_nonneg _)
      _ = gauge B (intVec (u i)) := one_mul _
  have hg : gauge B (intVec (mahlerVec u v i θ)) ≤
      (1 + (i:ℝ)/2) * gauge B (intVec (u i)) := by
    rw [hexp']
    calc gauge B (θ ⟨i, Nat.lt_succ_self _⟩ • intVec (u i) +
            ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)}, cj j • intVec (u j))
        ≤ gauge B (θ ⟨i, Nat.lt_succ_self _⟩ • intVec (u i)) +
            gauge B (∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
              cj j • intVec (u j)) :=
          gauge_add_le_of_mem_span hBc hB0 hBs hspan1 hspan2
      _ ≤ gauge B (θ ⟨i, Nat.lt_succ_self _⟩ • intVec (u i)) +
            ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
              gauge B (cj j • intVec (u j)) :=
          add_le_add le_rfl (gauge_sum_le_of_mem_span hBc hB0 hBs
            (s := Finset.univ) (f := fun j ↦ cj j • intVec (u j))
            (fun j _ ↦ Submodule.smul_mem _ _ (huS j)))
      _ ≤ gauge B (intVec (u i)) +
            (i : ℝ)/2 * gauge B (intVec (u i)) :=
          add_le_add hgi hsum
      _ = (1 + (i:ℝ)/2) * gauge B (intVec (u i)) := by ring
  exact mem_smul_of_gauge_lt hBc hB0 hBs hmem (hg.trans_lt ht)

/-- Shifting `vᵢ` by integer combinations of earlier `uⱼ` preserves
adaptedness to the flag. -/
theorem adaptedToFlag_mahlerVec {u v : Fin d → Fin d → ℤ}
    (had : adaptedToFlag u v)
    (θ : ∀ i : Fin d, {l : Fin d // (l:ℕ) < (i:ℕ)+1} → ℝ) :
    adaptedToFlag u (fun i ↦ mahlerVec u v i (θ i)) := by
  classical
  have hshift : ∀ i : Fin d,
      (∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
        round (θ i ⟨j.1, Nat.lt_succ_of_lt j.2⟩) • u j) ∈
        flagLattice u (i:ℕ) := by
    intro i
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _
      (flagLattice_mono (Nat.succ_le_of_lt j.2)
        (mem_flagLattice_succ_self u j.1))
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact sub_mem (had.1 i)
      (flagLattice_mono (Nat.le_succ _) (hshift i))
  · intro i
    have hD : flagDetLin u i (∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
        round (θ i ⟨j.1, Nat.lt_succ_of_lt j.2⟩) • u j) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul, flagDetLin_u_of_ne, smul_zero]
      intro h
      exact absurd (congrArg Fin.val h) (ne_of_lt j.2)
    show flagDetLin u i (v i - _) ≠ 0
    rw [map_sub, hD, sub_zero]
    exact had.2.1 i
  · intro i z hz
    obtain ⟨m, hm⟩ := had.2.2 i z hz
    refine ⟨m, ?_⟩
    have hEq : z - m • mahlerVec u v i (θ i) =
        (z - m • v i) + m • ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
          round (θ i ⟨j.1, Nat.lt_succ_of_lt j.2⟩) • u j := by
      show z - m • (v i - ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
            round (θ i ⟨j.1, Nat.lt_succ_of_lt j.2⟩) • u j) =
          (z - m • v i) + m • ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
            round (θ i ⟨j.1, Nat.lt_succ_of_lt j.2⟩) • u j
      rw [smul_sub]
      abel
    show z - m • mahlerVec u v i (θ i) ∈ flagLattice u (i:ℕ)
    rw [hEq]
    exact add_mem hm (Submodule.smul_mem _ _ (hshift i))

/-- The shifted Mahler basis: an adapted `ℤ`-basis of `ℤ^d` whose first
`r` vectors lie in every dilation of `B` beyond `(1 + i/2)·λᵢ`. -/
theorem exists_mahler_shift (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    (hBs : ∀ x ∈ B, -x ∈ B) {u : Fin d → Fin d → ℤ}
    (huI : LinearIndependent ℝ fun i ↦ intVec (u i)) {r : ℕ}
    (huV : ∀ i : Fin d, (i:ℕ) < r → intVec (u i) ∈ intSpan B)
    (huMin : ∀ i : Fin d, (i:ℕ) < r → ∀ z : Fin d → ℤ,
      intVec z ∈ intSpan B → intVec z ∉ flagSpan u (i:ℕ) →
      gauge B (intVec (u i)) ≤ gauge B (intVec z)) :
    ∃ v' : Fin d → Fin d → ℤ, adaptedToFlag u v' ∧
      LinearIndependent ℤ v' ∧
      Submodule.span ℤ (Set.range v') = ⊤ ∧
      ∀ i : Fin d, (i:ℕ) < r → ∀ t : ℝ,
        (1 + (i:ℝ)/2) * gauge B (intVec (u i)) < t →
        intVec (v' i) ∈ t • B := by
  classical
  obtain ⟨v, had, hvI, hvspan⟩ := exists_mahler_zbasis huI
  have hexp : ∀ i : Fin d, ∃ θ : {l : Fin d // (l:ℕ) < (i:ℕ)+1} → ℝ,
      intVec (v i) = ∑ l, θ l • intVec (u l) := by
    intro i
    have hvL := had.1 i
    rw [mem_flagLattice, flagSpan] at hvL
    obtain ⟨θ, hθ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hvL
    exact ⟨θ, hθ.symm⟩
  choose θ hθ using hexp
  have had' : adaptedToFlag u (fun i ↦ mahlerVec u v i (θ i)) :=
    adaptedToFlag_mahlerVec had θ
  refine ⟨_, had', adaptedToFlag_linearIndependent had',
    adaptedToFlag_span_top huI had', fun i hi t ht ↦ ?_⟩
  have huNot : ∀ j : Fin d, intVec (u j) ∉ flagSpan u (j:ℕ) := by
    intro j
    rw [flagSpan]
    have hrange : (Set.range fun l : {l : Fin d // (l:ℕ) < (j:ℕ)} ↦
        intVec (u l)) =
        (fun l ↦ intVec (u l)) '' {l : Fin d | (l:ℕ) < (j:ℕ)} := by
      ext x
      constructor
      · rintro ⟨l, rfl⟩; exact ⟨l.1, l.2, rfl⟩
      · rintro ⟨l, hl, rfl⟩; exact ⟨⟨l, hl⟩, rfl⟩
    rw [hrange]
    exact huI.notMem_span_image (by simp)
  apply mahlerVec_mem_smul hBc hB0 hBs (hθ i)
    (abs_flagCoord_le_one huI had i (hθ i))
  · intro j
    exact intSpan_le_span B (huV j.1 (j.2.trans hi))
  · exact intSpan_le_span B (huV i hi)
  · intro j
    exact huMin j.1 (j.2.trans hi) (u i) (huV i hi)
      (fun h ↦ huNot i (flagSpan_mono (Nat.le_of_lt j.2) h))
  · exact ht

/-- The integer dual family `w j k = det(V) · adjugate(V)ⱼₖ`, where
`V` is the integer matrix with columns `v j`.  When `v` is a `ℤ`-basis
of `ℤ^d`, `det V = ±1` and `w` is genuinely dual to `v`. -/
def dualVec (v : Fin d → Fin d → ℤ) (j : Fin d) (k : Fin d) : ℤ :=
  (intMat v).det * (intMat v).adjugate j k

/-- An integer basis of `ℤ^d` has unimodular determinant. -/
theorem intMat_isUnit_det {v : Fin d → Fin d → ℤ}
    (hvI : LinearIndependent ℤ v)
    (hvspan : Submodule.span ℤ (Set.range v) = ⊤) :
    IsUnit (intMat v).det := by
  classical
  have hunit := (Pi.basisFun ℤ (Fin d)).isUnit_det
    (Module.Basis.mk hvI hvspan.ge)
  rw [Pi.basisFun_det_apply, Module.Basis.coe_mk] at hunit
  have hmat : Matrix.of v = (intMat v).transpose := rfl
  rw [hmat, Matrix.det_transpose] at hunit
  exact hunit

/-- `dualVec` is dual to `v` whenever `det V = ±1`:
`∑_k v i k · w j k = δᵢⱼ`. -/
theorem dualVec_dot {v : Fin d → Fin d → ℤ}
    (hunit : IsUnit (intMat v).det) (i j : Fin d) :
    ∑ k, v i k * dualVec v j k = if i = j then (1 : ℤ) else 0 := by
  have hdet2 : (intMat v).det * (intMat v).det = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> norm_num
  have hcalc : (∑ k, v i k * dualVec v j k) =
      (intMat v).det * ∑ k, (intMat v).adjugate j k * intMat v k i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by
      show v i k * ((intMat v).det * (intMat v).adjugate j k) =
        (intMat v).det * ((intMat v).adjugate j k * intMat v k i)
      rw [show intMat v k i = v i k from rfl]
      ring
  rw [hcalc, ← Matrix.mul_apply, Matrix.adjugate_mul, Matrix.smul_apply,
    Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [smul_eq_mul, if_pos rfl, mul_one]
    exact hdet2
  · rw [if_neg (fun h ↦ hij h.symm), if_neg hij, smul_eq_mul, mul_zero,
      mul_zero]

/-- **The remaining geometric input: Minkowski's second theorem.**
For `i < r`, the `i`-th coordinate of an integer point `z ∈ B` in the
adapted basis satisfies `|coord| · λᵢ ≤ C`, where `λᵢ` is the `i`-th
successive minimum `gauge B (uᵢ)` and `C` depends only on the ambient
dimension `d`.

Classically this is the unique step of Mahler's lemma that uses
Minkowski's second theorem `λ₁ ⋯ λ_d · vol(B ∩ V_d) ≤ 2^d` (applied to
the intersection `B ∩ Vᵢ` and the lattice `Lᵢ = Vᵢ ∩ ℤ^d`), together
with the determinant bounds from `adaptedToFlag`.  Mathlib currently
provides only Minkowski's *first* theorem, so this remains the single
intentional `sorry` of the formalization. -/
theorem mahler_coord_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Set (Fin d → ℝ)), Convex ℝ B →
      (0 : Fin d → ℝ) ∈ B → (∀ x ∈ B, -x ∈ B) → Bornology.IsBounded B →
      ∀ (u : Fin d → Fin d → ℤ) (r : ℕ) (v : Fin d → Fin d → ℤ),
        LinearIndependent ℝ (fun i ↦ intVec (u i)) →
        (∀ i : Fin d, (i:ℕ) < r → intVec (u i) ∈ intSpan B) →
        (∀ i : Fin d, (i:ℕ) < r → ∀ z : Fin d → ℤ,
          intVec z ∈ intSpan B → intVec z ∉ flagSpan u (i:ℕ) →
          gauge B (intVec (u i)) ≤ gauge B (intVec z)) →
        flagSpan u r = intSpan B →
        adaptedToFlag u v →
        LinearIndependent ℤ v →
        Submodule.span ℤ (Set.range v) = ⊤ →
        ∀ i : Fin d, (i:ℕ) < r →
          ∀ z : Fin d → ℤ, intVec z ∈ B →
            |(∑ k, (z k : ℝ) * (dualVec v i k : ℝ))| *
              gauge B (intVec (u i)) ≤ C := by
  sorry

/-- **The geometric core of the Mahler basis theorem** — the exact
geometry-of-numbers content needed by `exists_zbasis_mahler`, isolated as a
single input.  Uniformly in the symmetric convex bounded body `B ∋ 0`,
there is a `ℤ`-basis `v` of `ℤ^d` with dual basis `w` such that for every
index `i`, either the dual vector `w i` annihilates all of `B ∩ ℤ^d`, or
there is a scale `r > 0` (classically `r ≍ λᵢ`, the `i`-th successive
minimum) with `|⟨z, w i⟩| · r ≤ C` for every integer point `z ∈ B` and
`v i ∈ t • B` for all `t > r`.

**Proof structure.**  Three parts; the first two are now fully formalized
and the third is isolated as the single remaining `sorry`
(`mahler_coord_bound` above):

1. **Successive minima for a bounded (not necessarily open) `B`** —
   `exists_succMinima_bounded` produces greedy gauge-minimizers
   `u₁,…,u_r` spanning `intSpan B`, using finiteness of integer vectors
   of bounded gauge.

2. **Mahler's basis lemma (pure algebra over `ℤ`, no Minkowski-2nd)** —
   `exists_mahler_zbasis` builds an adapted `ℤ`-basis `v` via the
   principal ideal `flagDetLin`-image argument, and `exists_mahler_shift`
   shifts each `vᵢ` by integer combinations of earlier `uⱼ` so that
   `gauge B (vᵢ) ≤ (1 + i/2)·λᵢ` (`mahlerVec_mem_smul`).

3. **The pairing bound (the Minkowski-2nd step)** — `mahler_coord_bound`:
   for `z ∈ B ∩ ℤ^d` and `i < r`, `|mᵢ|·λᵢ ≤ C` where
   `mᵢ = ⟨z, wᵢ⟩` is the `i`-th `v`-coordinate of `z` (with
   `w = dualVec v`, `dualVec_dot` certifying duality).  Classically this
   uses Cramer's rule plus Minkowski's second theorem
   `∏ⱼ λⱼ · vol_r(B∩V_r) ≤ 2ʳ` — the missing Mathlib input.

For `i ≥ r`, `hflag` puts every `z ∈ B` inside `Lᵢ`, so `wᵢ` annihilates
`B ∩ ℤ^d` outright. -/
theorem exists_zbasis_mahler_core (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Set (Fin d → ℝ)), Convex ℝ B →
      (0 : Fin d → ℝ) ∈ B → (∀ x ∈ B, -x ∈ B) → Bornology.IsBounded B →
      ∃ (v w : Fin d → Fin d → ℤ),
        LinearIndependent ℤ v ∧ Submodule.span ℤ (Set.range v) = ⊤ ∧
        (∀ i j, ∑ k, v i k * w j k = if i = j then (1 : ℤ) else 0) ∧
        (∀ i, (∀ z : Fin d → ℤ, intVec z ∈ B →
                (∑ k, (z k : ℝ) * (w i k : ℝ)) = 0) ∨
              ∃ r : ℝ, 0 < r ∧
                (∀ z : Fin d → ℤ, intVec z ∈ B →
                    |(∑ k, (z k : ℝ) * (w i k : ℝ))| * r ≤ C) ∧
                (∀ t : ℝ, r < t → intVec (v i) ∈ t • B)) := by
  classical
  obtain ⟨C₀, hC₀, hbound⟩ := mahler_coord_bound d
  refine ⟨((d:ℝ) + 1)/2 * C₀, mul_pos (by positivity) hC₀,
    fun B hBc hB0 hBs hBb ↦ ?_⟩
  obtain ⟨r, u, hr, huI, huV, huMin, hflag⟩ :=
    exists_succMinima_bounded hBc hB0 hBs hBb
  obtain ⟨v, had, hvI, hvspan, hvMem⟩ :=
    exists_mahler_shift hBc hB0 hBs huI huV huMin
  have hunit := intMat_isUnit_det hvI hvspan
  refine ⟨v, fun j ↦ dualVec v j, hvI, hvspan,
    fun i j ↦ dualVec_dot hunit i j, fun i ↦ ?_⟩
  by_cases hir : (i:ℕ) < r
  · -- `i < r`: Minkowski bound with scale `rᵢ = (1 + i/2)·λᵢ`.
    right
    refine ⟨(1 + (i:ℝ)/2) * gauge B (intVec (u i)), ?_, ?_, ?_⟩
    · exact mul_pos (by positivity)
        (gauge_pos_of_mem_span hBc hB0 hBs hBb
          (intSpan_le_span B (huV i hir)) (huI.ne_zero i))
    · intro z hz
      have hcz := hbound B hBc hB0 hBs hBb u r v huI huV huMin hflag had
        hvI hvspan i hir z hz
      calc |(∑ k, (z k : ℝ) * (dualVec v i k : ℝ))| *
            ((1 + (i:ℝ)/2) * gauge B (intVec (u i)))
          = (1 + (i:ℝ)/2) * (|(∑ k, (z k : ℝ) *
              (dualVec v i k : ℝ))| * gauge B (intVec (u i))) := by ring
        _ ≤ (1 + (i:ℝ)/2) * C₀ :=
            mul_le_mul_of_nonneg_left hcz (by positivity)
        _ ≤ ((d:ℝ) + 1)/2 * C₀ := by
            apply mul_le_mul_of_nonneg_right _ hC₀.le
            have hid : ((i:ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast i.isLt
            linarith
    · exact fun t ht ↦ hvMem i hir t ht
  · -- `i ≥ r`: every `z ∈ B` lies in `Lᵢ`, so `wᵢ` annihilates `B ∩ ℤ^d`.
    left
    intro z hz
    have hzL : z ∈ flagLattice u (i:ℕ) := by
      have h1 : intVec z ∈ intSpan B := intVec_mem_intSpan hz
      have h2 : intVec z ∈ flagSpan u r := hflag ▸ h1
      exact flagSpan_mono (Nat.le_of_not_gt hir) h2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (adaptedToFlag_span had (i:ℕ) i.isLt.le hzL)
    have hzsum : (∑ k, z k * dualVec v i k : ℤ) = 0 := by
      calc ∑ k, z k * dualVec v i k
          = ∑ k, (∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
              c j • v j) k * dualVec v i k := by rw [← hc]
        _ = ∑ k, ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
              (c j * (v j) k) * dualVec v i k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_apply, Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ ↦ by
              rw [Pi.smul_apply, smul_eq_mul]
        _ = ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
              ∑ k, c j * ((v j) k * dualVec v i k) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ ↦
              Finset.sum_congr rfl fun k _ ↦ by ring
        _ = ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)},
              c j * ∑ k, (v j) k * dualVec v i k := by
            exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.mul_sum]
        _ = ∑ j : {l : Fin d // (l:ℕ) < (i:ℕ)}, c j * 0 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [dualVec_dot hunit j i,
              if_neg (fun h ↦ absurd (congrArg Fin.val h) (ne_of_lt j.2))]
        _ = 0 := by simp
    exact_mod_cast hzsum

theorem exists_zbasis_mahler (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Set (Fin d → ℝ)), Convex ℝ B →
      (0 : Fin d → ℝ) ∈ B → (∀ x ∈ B, -x ∈ B) → Bornology.IsBounded B →
      ∃ (v w : Fin d → Fin d → ℤ) (M : Fin d → ℝ),
        LinearIndependent ℤ v ∧ Submodule.span ℤ (Set.range v) = ⊤ ∧
        (∀ i j, ∑ k, v i k * w j k = if i = j then (1 : ℤ) else 0) ∧
        (∀ i, 0 ≤ M i) ∧
        (∀ z : Fin d → ℤ, intVec z ∈ B → ∀ i,
            |(∑ k, (z k : ℝ) * (w i k : ℝ))| ≤ M i) ∧
        (∀ i, 0 < M i → ∀ t : ℝ, C / M i < t → intVec (v i) ∈ t • B) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := exists_zbasis_mahler_core d
  refine ⟨C, hCpos, fun B hBc hB0 hBs hBb ↦ ?_⟩
  obtain ⟨v, w, hli, hspan, hdual, hdisj⟩ := hC B hBc hB0 hBs hBb
  have h0mem : (0 : Fin d → ℤ) ∈ intPointsFinset B hBb :=
    (mem_intPointsFinset hBb).mpr (by simpa using hB0)
  have hne : (intPointsFinset B hBb).Nonempty := ⟨0, h0mem⟩
  -- `M i` is the supremum of `|⟨z, w i⟩|` over the finitely many integer
  -- points of `B`; being a supremum of nonnegative integers it is either
  -- `0` (the annihilated case) or attained at some `zs ∈ B ∩ ℤ^d`.
  refine ⟨v, w,
    fun i ↦ (intPointsFinset B hBb).sup' hne
      (fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|),
    hli, hspan, hdual, fun i ↦ ?_, fun z hzB i ↦ ?_, fun i hMi t ht ↦ ?_⟩
  · -- `0 ≤ M i`
    show 0 ≤ (intPointsFinset B hBb).sup' hne
      (fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|)
    rw [Finset.le_sup'_iff]
    exact ⟨0, h0mem, abs_nonneg _⟩
  · -- `|⟨z, w i⟩| ≤ M i`
    show |(∑ k, (z k : ℝ) * (w i k : ℝ))| ≤
      (intPointsFinset B hBb).sup' hne
        (fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|)
    rw [Finset.le_sup'_iff]
    exact ⟨z, (mem_intPointsFinset hBb).mpr hzB, le_rfl⟩
  · -- `M i > 0`: the supremum is attained at some `zs ∈ B ∩ ℤ^d`, which
    -- has nonzero pairing, so the second disjunct of `hdisj i` applies.
    have hMi' : 0 < (intPointsFinset B hBb).sup' hne
        (fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|) := hMi
    have ht' : C / (intPointsFinset B hBb).sup' hne
        (fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|) < t := ht
    obtain ⟨zs, hzsmem, hzseq⟩ := Finset.exists_mem_eq_sup'
      (s := intPointsFinset B hBb) (H := hne)
      (f := fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|)
    have hzsB : intVec zs ∈ B := (mem_intPointsFinset hBb).mp hzsmem
    have hpair : |(∑ k, (zs k : ℝ) * (w i k : ℝ))| ≠ 0 := by
      intro h0
      have hz0 : (intPointsFinset B hBb).sup' hne
          (fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|) = 0 := hzseq.trans h0
      exact hMi'.ne' hz0
    rcases hdisj i with hann | ⟨r, hrpos, hbound, hmem⟩
    · exfalso
      exact hpair (abs_eq_zero.mpr (hann zs hzsB))
    · -- `M i · r ≤ C` from `|⟨z,w i⟩| · r ≤ C` at every integer point.
      have hMle : (intPointsFinset B hBb).sup' hne
            (fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|) ≤ C / r := by
        rw [Finset.sup'_le_iff]
        intro z hz
        rw [le_div_iff₀ hrpos]
        exact hbound z ((mem_intPointsFinset hBb).mp hz)
      have hMr : (intPointsFinset B hBb).sup' hne
            (fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|) * r ≤ C := by
        have h := mul_le_mul_of_nonneg_right hMle hrpos.le
        rwa [div_mul_cancel₀ _ hrpos.ne'] at h
      have hrC : r ≤ C / ((intPointsFinset B hBb).sup' hne
            (fun z ↦ |(∑ k, (z k : ℝ) * (w i k : ℝ))|)) := by
        rw [le_div_iff₀ hMi']
        rwa [mul_comm]
      exact hmem t (hrC.trans_lt ht')

/-- **The adapted integer basis lemma** — the geometry-of-numbers input
behind Lemma 7 (discrete John): uniformly in the symmetric convex bounded
body `B ∋ 0`, there is a `ℤ`-basis `v` of `ℤ^d` and "successive-minima
widths" `λᵢ ≥ 0` such that

* each `vᵢ` with `λᵢ > 0` lies in every dilation `t • B`, `t > K·λᵢ`, and
* every `z ∈ B ∩ ℤ^d` has `v`-coordinates `m` with `|mᵢ| ≤ K / λᵢ`;
  with `K / 0 = 0` this forces `mᵢ = 0` in directions outside `span B`,
  where `λᵢ` is set to `0`.

The proof is a reduction to the Mahler-form input
`exists_zbasis_mahler` (the missing Minkowski-second-theorem content):
given a basis `v` with dual basis `w` and pairing bound
`|⟨z, w i⟩| ≤ M i`, the `v`-coordinate `m i` of `z` equals `⟨z, w i⟩`
by `∑_k v j k · w i k = δⱼᵢ`, and one takes `K = C + 1` and
`λᵢ = C / (K · Mᵢ)` — then `K·λᵢ = C / Mᵢ` and
`K / λᵢ = K²·Mᵢ / C ≥ Mᵢ` (with `Mᵢ = 0` giving `λᵢ = 0`, hence the
required `mᵢ = 0`). -/
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
  classical
  obtain ⟨C, hCpos, hC⟩ := exists_zbasis_mahler d
  refine ⟨C + 1, by linarith, fun B hBc hB0 hBs hBb ↦ ?_⟩
  obtain ⟨v, w, M, hli, hspan, hdual, hMnn, hMbound, hMem⟩ :=
    hC B hBc hB0 hBs hBb
  have hKpos : (0 : ℝ) < C + 1 := by linarith
  -- `K² ≥ C` since `K = C + 1 > 0`.
  have hK2 : C ≤ (C + 1) ^ 2 := by nlinarith [hCpos.le, sq_nonneg C]
  refine ⟨v, fun i ↦ C / ((C + 1) * M i), hli, hspan,
    fun i ↦ div_nonneg hCpos.le (mul_nonneg hKpos.le (hMnn i)), ?_, ?_⟩
  · -- `K * lam i = C / M i` when `lam i > 0` (forcing `M i > 0`).
    intro i hlam t ht
    dsimp only at hlam ht
    have hMi : 0 < M i := by
      rcases (hMnn i).eq_or_lt with h | h
      · exfalso
        have h0 : C / ((C + 1) * M i) = 0 := by rw [← h]; simp
        rw [h0] at hlam
        exact absurd hlam (lt_irrefl _)
      · exact h
    have hKl : (C + 1) * (C / ((C + 1) * M i)) = C / M i := by
      rw [← mul_div_assoc, mul_comm (C + 1) C, mul_comm (C + 1) (M i)]
      exact mul_div_mul_right _ _ hKpos.ne'
    rw [hKl] at ht
    exact hMem i hMi t ht
  · intro z hzB
    -- `v` is a `ℤ`-basis; take `m i` = the `v`-coordinates of `z`.
    set b : Module.Basis (Fin d) ℤ (Fin d → ℤ) :=
      Module.Basis.mk hli hspan.ge
    have hbv : ∀ i, b i = v i :=
      fun i ↦ congrFun (Module.Basis.coe_mk hli hspan.ge) i
    have hsum : z = ∑ j, (b.repr z j) • v j := by
      conv_lhs => rw [← b.sum_repr z]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hbv j]
    refine ⟨fun i ↦ b.repr z i, hsum, fun i ↦ ?_⟩
    -- `b.repr z i = ⟨z, w i⟩` by duality.
    have hzk : ∀ k, z k = ∑ j, b.repr z j * v j k := fun k ↦ by
      have hk := congrFun hsum k
      rw [hk]
      simp [Finset.sum_apply]
    have hcoord : (∑ k, z k * w i k) = b.repr z i := by
      calc ∑ k, z k * w i k
          = ∑ k, (∑ j, b.repr z j * v j k) * w i k :=
            Finset.sum_congr rfl fun k _ ↦ by rw [hzk k]
        _ = ∑ k, ∑ j, b.repr z j * v j k * w i k :=
            Finset.sum_congr rfl fun k _ ↦ Finset.sum_mul _ _ _
        _ = ∑ j, ∑ k, b.repr z j * v j k * w i k := Finset.sum_comm
        _ = ∑ j, b.repr z j * (∑ k, v j k * w i k) :=
            Finset.sum_congr rfl fun j _ ↦ by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun k _ ↦ mul_assoc _ _ _
        _ = ∑ j, b.repr z j * (if j = i then (1 : ℤ) else 0) :=
            Finset.sum_congr rfl fun j _ ↦ by rw [hdual j i]
        _ = b.repr z i := by
            simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
              Finset.mem_univ, ite_true]
    have hcoordR : ((b.repr z i : ℤ) : ℝ) =
        ∑ k, (z k : ℝ) * (w i k : ℝ) := by
      rw [← hcoord]; push_cast; rfl
    -- `|⟨z, w i⟩| ≤ M i ≤ K / lam i` (also when `M i = 0`, as `K/0 = 0`).
    have hle : |(∑ k, (z k : ℝ) * (w i k : ℝ))| ≤ M i := hMbound z hzB i
    have hRHS : (C + 1) / (C / ((C + 1) * M i)) = (C + 1) * ((C + 1) * M i) / C :=
      div_div_eq_mul_div _ _ _
    have hMle : M i ≤ (C + 1) / (C / ((C + 1) * M i)) := by
      rw [hRHS, le_div_iff₀ hCpos]
      calc M i * C ≤ M i * (C + 1) ^ 2 :=
            mul_le_mul_of_nonneg_left hK2 (hMnn i)
        _ = (C + 1) * ((C + 1) * M i) := by ring
    show |(b.repr z i : ℝ)| ≤ (C + 1) / (C / ((C + 1) * M i))
    rw [hcoordR]
    exact hle.trans hMle
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
`exists_zbasis_adapted` (itself reduced to the missing
Minkowski-second-theorem input `exists_zbasis_mahler`, the only
remaining gap): with `K` and `v`, `λ` from that lemma one takes
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
  classical
  obtain ⟨K, hKpos, hK⟩ := exists_zbasis_adapted d
  -- The uniform constant `c = (4dK² + 1)⁻¹`.
  set c : ℝ := (4 * (d : ℝ) * K ^ 2 + 1)⁻¹ with hc
  have hK2nn : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
  have hdnn : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hden : (1 : ℝ) ≤ 4 * (d : ℝ) * K ^ 2 + 1 := by nlinarith
  have hdenpos : (0 : ℝ) < 4 * (d : ℝ) * K ^ 2 + 1 := by linarith
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcle : c ≤ 1 := by rw [hc]; exact inv_le_one_of_one_le₀ hden
  refine ⟨c, hcpos, hcle, fun B hBc hB0 hBs hBb ↦ ?_⟩
  obtain ⟨v, lam, hli, hspan, hlamnn, hvt, hcoord⟩ := hK B hBc hB0 hBs hBb
  refine ⟨v, fun i ↦ ⌊K / lam i⌋₊, hli, hspan, ?_, ?_⟩
  · -- Inner inclusion: `z = ∑ rᵢ • vᵢ` with `|rᵢ| ≤ ⌊c·Nᵢ⌋` lies in `B`.
    intro z hz
    obtain ⟨r, hr, rfl⟩ := GAP.mem_centered.mp hz
    -- `|rᵢ| ≤ c·Nᵢ` (real bound).
    have hrc : ∀ i, |(r i : ℝ)| ≤ c * (⌊K / lam i⌋₊ : ℝ) := by
      intro i
      have h := hr i
      have h2 : |(r i : ℝ)| ≤ (⌊c * (⌊K / lam i⌋₊ : ℝ)⌋₊ : ℝ) := by
        exact_mod_cast h
      exact h2.trans (Nat.floor_le (mul_nonneg hcpos.le (Nat.cast_nonneg _)))
    -- The `vᵢ` with `lam i > 0` come with a point `y i ∈ B` and scale
    -- `t i = 2K·lam i`; when `lam i = 0`, `N i = 0` forces `r i = 0`.
    have hv_smul : ∀ i, 0 < lam i →
        ∃ y : Fin d → ℝ, y ∈ B ∧ intVec (v i) = (2 * K * lam i) • y := by
      intro i hpos
      have hlt : K * lam i < 2 * K * lam i := by nlinarith [hKpos, hpos]
      obtain ⟨y, hyB, hvy⟩ := Set.mem_smul_set.mp (hvt i hpos _ hlt)
      exact ⟨y, hyB, hvy.symm⟩
    -- Each summand `(r i : ℝ) • intVec (v i)` lies in `w i • B` where
    -- `w i = |r i| · 2K·lam i`.
    have hpmem : ∀ i, (r i : ℝ) • intVec (v i) ∈
        (|(r i : ℝ)| * (2 * K * lam i)) • B := by
      intro i
      rcases eq_or_lt_of_le (hlamnn i) with h0 | hpos
      · -- `lam i = 0` forces `r i = 0`, so the summand is `0 ∈ 0 • B`.
        have hNi : (⌊K / lam i⌋₊ : ℝ) = 0 := by
          rw [← h0]; simp
        have hri : r i = 0 := by
          have h1 := hrc i
          rw [hNi, mul_zero] at h1
          have : (r i : ℝ) = 0 :=
            abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
          exact_mod_cast this
        rw [hri]
        simp only [Int.cast_zero, zero_smul, abs_zero]
        exact ⟨0, hB0, by simp⟩
      · obtain ⟨y, hyB, hvy⟩ := hv_smul i hpos
        rcases le_or_gt (0 : ℝ) (r i) with hrnn | hrn
        · refine ⟨y, hyB, ?_⟩
          rw [hvy, smul_smul, abs_of_nonneg hrnn]
        · refine ⟨-y, hBs y hyB, ?_⟩
          rw [hvy, smul_smul, abs_of_neg hrn]
          show (-(r i : ℝ) * (2 * K * lam i)) • (-y) = _
          rw [smul_neg, ← neg_smul, neg_mul, neg_neg]
    -- Summing: `intVec z ∈ (∑ wᵢ) • B ⊆ B` since `∑ wᵢ ≤ 1`.
    have hsum_mem : (∑ i, (r i : ℝ) • intVec (v i)) ∈
        (∑ i, |(r i : ℝ)| * (2 * K * lam i)) • B :=
      sum_mem_smul hBc hB0
        (fun i _ ↦ mul_nonneg (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hKpos.le) (hlamnn i)))
        (fun i _ ↦ hpmem i)
    have hsum_eq : intVec (∑ i, r i • v i) = ∑ i, (r i : ℝ) • intVec (v i) := by
      rw [intVec_sum]
      exact Finset.sum_congr rfl fun i _ ↦ intVec_smul _ _
    rw [← hsum_eq] at hsum_mem
    have hWle : ∀ i, |(r i : ℝ)| * (2 * K * lam i) ≤ 2 * c * K ^ 2 := by
      intro i
      rcases eq_or_lt_of_le (hlamnn i) with h0 | hpos
      · rw [← h0]; simp; positivity
      · have hNi : (⌊K / lam i⌋₊ : ℝ) ≤ K / lam i :=
          Nat.floor_le (div_nonneg hKpos.le (hlamnn i))
        calc |(r i : ℝ)| * (2 * K * lam i)
            ≤ (c * (K / lam i)) * (2 * K * lam i) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact (hrc i).trans (mul_le_mul_of_nonneg_left hNi hcpos.le)
          _ = 2 * c * K * (K / lam i * lam i) := by ring
          _ = 2 * c * K * K := by rw [div_mul_cancel₀ _ hpos.ne']
          _ = 2 * c * K ^ 2 := by ring
    have hWsum : (∑ i, |(r i : ℝ)| * (2 * K * lam i)) ≤ 1 := by
      calc ∑ i, |(r i : ℝ)| * (2 * K * lam i)
          ≤ ∑ _i : Fin d, 2 * c * K ^ 2 :=
            Finset.sum_le_sum fun i _ ↦ hWle i
        _ = (d : ℝ) * (2 * c * K ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
        _ = 2 * (d : ℝ) * K ^ 2 * (4 * (d : ℝ) * K ^ 2 + 1)⁻¹ := by
            rw [hc]; ring
        _ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one hdenpos]
            nlinarith
    exact smul_self_subset hBc hB0
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (abs_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) hKpos.le) (hlamnn i)))
      hWsum hsum_mem
  · -- Outer inclusion: `z ∈ B ∩ ℤ^d` has `v`-coordinates `≤ N i`.
    intro z hzB
    obtain ⟨m, hzm, hm⟩ := hcoord z hzB
    rw [GAP.mem_centered]
    refine ⟨m, fun i ↦ ?_, hzm⟩
    have hle : |(m i : ℝ)| ≤ K / lam i := hm i
    have hnn : (0 : ℝ) ≤ K / lam i := div_nonneg hKpos.le (hlamnn i)
    have h1 : |m i| ≤ ⌊K / lam i⌋ :=
      Int.le_floor.mpr (by rw [Int.cast_abs]; exact hle)
    have h2 : ((⌊K / lam i⌋₊ : ℕ) : ℤ) = ⌊K / lam i⌋ := by
      rw [← Int.floor_toNat]
      exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr hnn)
    exact h1.trans_eq h2.symm
end DiscreteJohn

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
