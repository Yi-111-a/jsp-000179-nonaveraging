import Nonaveraging.ConvexComb

/-!
# Geometry-of-numbers and balancing helpers for Theorem 4

Helpers for the proof of `embedded_in_mu_convex_position` (Pham–Zakharov,
arXiv:2410.14624v2, §3.3, Lemmas 11–14):

* `exists_ne_zero_mem_span_range_of_volume_lt` /
  `exists_ne_zero_mem_span_range_of_volume_le` — Minkowski's convex body
  theorem for the lattice `span ℤ (Set.range b)` in `ι → ℝ`, whose covolume is
  `|det b|`.
* `volume_pi_Icc` / `volume_pi_Icc_neg` — volumes of coordinate boxes.
* `mem_span_range_basisFun_iff` — the lattice `span ℤ (Set.range
  (Pi.basisFun ℝ ι))` is exactly the set of integer-valued vectors.
* `exists_ne_zero_int_mem_box` — the classical consequence: a nonzero integer
  vector inside a coordinate box `∏ [−rᵢ, rᵢ]` as soon as `∏ rᵢ ≥ 1`.
  This is the basic counting input of Lemma 12 (applied there inside the GAP
  lattice).
* `exists_subset_sum_abs_sub_le` — the greedy balancing lemma: the elements of
  a weighted finite set can be split into two parts whose total weights differ
  by at most the largest weight.
* `balanced_convex_combination_split` — equation (13) of the paper: a balanced
  convex combination `Σ c_x (x − a) = 0`, `Σ c_x = 1`, `c_x ≤ w` splits
  `A₀ ∖ {a}` into two disjoint parts `A₁, A₂`, each of weight
  `≥ (1 − 2w)/2` (hence of size `≥ (1 − 2w)/(2w)`), with
  `Σ_{A₁} c_x (x − a) = −Σ_{A₂} c_x (x − a)`.
-/

open Finset MeasureTheory
open scoped ENNReal Pointwise Topology

namespace Nonaveraging

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Minkowski's convex body theorem** for the lattice `span ℤ (Set.range b)`
in `ι → ℝ` (covolume `|det b|`): a symmetric convex set of volume strictly
larger than `2^d · |det b|` contains a nonzero lattice point. -/
theorem exists_ne_zero_mem_span_range_of_volume_lt
    (b : Module.Basis ι ℝ (ι → ℝ)) {s : Set (ι → ℝ)}
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h : ENNReal.ofReal |(Matrix.of b).det| * 2 ^ Fintype.card ι < volume s) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ x ∈ s ∧ x ∈ Submodule.span ℤ (Set.range b) := by
  classical
  have : Countable ↥(Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable ↥(Submodule.span ℤ (Set.range b)))
  have hvol : volume (ZSpan.fundamentalDomain b)
      * 2 ^ Module.finrank ℝ (ι → ℝ) < volume s := by
    rw [ZSpan.volume_fundamentalDomain, Module.finrank_fintype_fun_eq_card]
    exact h
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (μ := volume) (L := (Submodule.span ℤ (Set.range (⇑b))).toAddSubgroup)
      (F := ZSpan.fundamentalDomain b)
      (ZSpan.isAddFundamentalDomain' b volume) h_symm h_conv hvol
  exact ⟨(x : ι → ℝ), fun h0 ↦ hx0 (Subtype.ext h0), hxs, x.2⟩

/-- **Minkowski's convex body theorem, compact/weak-inequality form**: a
symmetric convex *compact* set of volume at least `2^d · |det b|` contains a
nonzero lattice point. -/
theorem exists_ne_zero_mem_span_range_of_volume_le [Nonempty ι]
    (b : Module.Basis ι ℝ (ι → ℝ)) {s : Set (ι → ℝ)}
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_cpt : IsCompact s)
    (h : ENNReal.ofReal |(Matrix.of b).det| * 2 ^ Fintype.card ι ≤ volume s) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ x ∈ s ∧ x ∈ Submodule.span ℤ (Set.range b) := by
  classical
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have : Nontrivial (ι → ℝ) := by
    refine nontrivial_of_ne 0 (Pi.single i 1) ?_
    intro h
    have h2 := congrFun h i
    simp [Pi.single_eq_same] at h2
  have : Countable ↥(Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable ↥(Submodule.span ℤ (Set.range b)))
  have hvol : volume (ZSpan.fundamentalDomain b)
      * 2 ^ Module.finrank ℝ (ι → ℝ) ≤ volume s := by
    rw [ZSpan.volume_fundamentalDomain, Module.finrank_fintype_fun_eq_card]
    exact h
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (μ := volume) (L := (Submodule.span ℤ (Set.range (⇑b))).toAddSubgroup)
      (F := ZSpan.fundamentalDomain b)
      (ZSpan.isAddFundamentalDomain' b volume) h_symm h_conv h_cpt hvol
  exact ⟨(x : ι → ℝ), fun h0 ↦ hx0 (Subtype.ext h0), hxs, x.2⟩

omit [DecidableEq ι] in
/-- The volume of the coordinate box `∏ᵢ [aᵢ, bᵢ]` in `ι → ℝ`. -/
theorem volume_pi_Icc (a b : ι → ℝ) :
    volume (Set.pi Set.univ fun i ↦ Set.Icc (a i) (b i)) =
      ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [volume_pi_pi]
  exact Finset.prod_congr rfl fun i _ ↦ Real.volume_Icc

omit [DecidableEq ι] in
/-- The volume of the symmetric coordinate box `∏ᵢ [−rᵢ, rᵢ]` is
`2^d · ∏ rᵢ`. -/
theorem volume_pi_Icc_neg (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    volume (Set.pi Set.univ fun i ↦ Set.Icc (-r i) (r i)) =
      ENNReal.ofReal (2 ^ Fintype.card ι * ∏ i, r i) := by
  rw [volume_pi_Icc,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ by linarith [hr i])]
  congr 1
  have e : ∏ i, (r i - -r i) = ∏ i, (2 : ℝ) * r i :=
    Finset.prod_congr rfl fun i _ ↦ by ring
  rw [e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

omit [DecidableEq ι] in
/-- A point of `span ℤ (Set.range (Pi.basisFun ℝ ι))` has integer coordinates,
and conversely. -/
theorem mem_span_range_basisFun_iff {x : ι → ℝ} :
    x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔
      ∀ i, ∃ n : ℤ, x i = n := by
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ x]
  refine forall_congr' fun i ↦ ?_
  rw [Pi.basisFun_repr]
  exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, hn.symm⟩, fun ⟨n, hn⟩ ↦ ⟨n, hn.symm⟩⟩

/-- **Minkowski for coordinate boxes**: if `r i ≥ 0` and `∏ rᵢ ≥ 1`, the
symmetric box `∏ᵢ [−rᵢ, rᵢ]` contains a nonzero integer vector.  This is the
counting principle used throughout §3.3 of the paper (applied there inside
the GAP lattice via the discrete John lemma). -/
theorem exists_ne_zero_int_mem_box {d : ℕ} [NeZero d] {r : Fin d → ℝ}
    (hr : ∀ i, 0 ≤ r i) (hprod : 1 ≤ ∏ i, r i) :
    ∃ z : Fin d → ℤ, z ≠ 0 ∧ ∀ i, |(z i : ℝ)| ≤ r i := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, NeZero.pos d⟩⟩
  set s : Set (Fin d → ℝ) := Set.pi Set.univ fun i ↦ Set.Icc (-r i) (r i)
      with hs
  have hconv : Convex ℝ s := convex_pi fun i _ ↦ convex_Icc _ _
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    rw [hs, Set.mem_univ_pi] at hx ⊢
    intro i
    have hxi := hx i
    exact ⟨by rw [Pi.neg_apply]; linarith [hxi.2],
      by rw [Pi.neg_apply]; linarith [hxi.1]⟩
  have hcpt : IsCompact s := isCompact_univ_pi fun i ↦ isCompact_Icc
  have hvolF : ENNReal.ofReal |(Matrix.of (Pi.basisFun ℝ (Fin d))).det|
      = 1 := by
    rw [← ZSpan.volume_fundamentalDomain, ZSpan.fundamentalDomain_pi_basisFun,
      volume_pi_pi]
    simp
  have hvol : ENNReal.ofReal |(Matrix.of (Pi.basisFun ℝ (Fin d))).det|
      * 2 ^ Fintype.card (Fin d) ≤ volume s := by
    rw [hvolF, one_mul, hs, volume_pi_Icc]
    have e : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        ENNReal.ofReal (r i - -r i) = 2 * ENNReal.ofReal (r i) := fun i _ ↦ by
      rw [show r i - -r i = 2 * r i by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
    have h1 : (1 : ℝ≥0∞) ≤ ∏ i, ENNReal.ofReal (r i) := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hr i)]
      exact ENNReal.ofReal_le_ofReal hprod
    exact le_mul_of_one_le_right' h1
  obtain ⟨x, hx0, hxs, hxspan⟩ :=
    exists_ne_zero_mem_span_range_of_volume_le (Pi.basisFun ℝ (Fin d))
      hsymm hconv hcpt hvol
  choose z hz using fun i ↦ (mem_span_range_basisFun_iff.mp hxspan) i
  refine ⟨z, ?_, fun i ↦ ?_⟩
  · intro hzz
    apply hx0
    funext i
    rw [hz i, hzz]
    simp
  · have hxi := Set.mem_univ_pi.mp (hs ▸ hxs) i
    rw [← hz i, abs_le]
    exact ⟨hxi.1, hxi.2⟩

section Balancing

variable {α : Type*} [DecidableEq α]

/-- **Greedy balancing lemma**: given nonnegative weights `f x ≤ w` on a
finset `S`, some `T ⊆ S` has `|Σ_T f − Σ_{S∖T} f| ≤ w`.  (Process the
elements one at a time, always adding to the currently lighter side.) -/
theorem exists_subset_sum_abs_sub_le (S : Finset α) {f : α → ℝ}
    (hf : ∀ x ∈ S, 0 ≤ f x) {w : ℝ} (hw : ∀ x ∈ S, f x ≤ w) (hw0 : 0 ≤ w) :
    ∃ T : Finset α, T ⊆ S ∧ |∑ x ∈ T, f x - ∑ x ∈ S \ T, f x| ≤ w := by
  classical
  induction S using Finset.induction with
  | empty =>
      exact ⟨∅, Finset.empty_subset _, by simpa using hw0⟩
  | insert a s has ih =>
      obtain ⟨T, hTS, hT⟩ := ih (fun x hx ↦ hf x (Finset.mem_insert_of_mem hx))
        (fun x hx ↦ hw x (Finset.mem_insert_of_mem hx))
      rw [abs_le] at hT
      have haT : a ∉ T := fun h ↦ has (hTS h)
      have haST : a ∉ s \ T := fun h ↦ has (Finset.mem_sdiff.mp h).1
      have hfa0 : 0 ≤ f a := hf a (Finset.mem_insert_self _ _)
      have hfaw : f a ≤ w := hw a (Finset.mem_insert_self _ _)
      by_cases hd : 0 ≤ ∑ x ∈ T, f x - ∑ x ∈ s \ T, f x
      · -- `a` joins the right-hand side; the difference `d − f a` stays in
        -- `[−w, w]` since `0 ≤ d ≤ w` and `0 ≤ f a ≤ w`.
        refine ⟨T, hTS.trans (Finset.subset_insert _ _), ?_⟩
        rw [Finset.insert_sdiff_of_notMem _ haT, Finset.sum_insert haST]
        rw [abs_le]
        exact ⟨by linarith [hd, hfaw], by linarith [hT.2, hfa0]⟩
      · -- `a` joins the left-hand side; the difference `d + f a` stays in
        -- `[−w, w]` since `−w ≤ d < 0` and `0 ≤ f a ≤ w`.
        push Not at hd
        refine ⟨insert a T, Finset.insert_subset_insert _ hTS, ?_⟩
        rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem has,
          Finset.sum_insert haT]
        rw [abs_le]
        exact ⟨by linarith [hT.1, hfa0], by linarith [hd, hfaw]⟩

/-- **Equation (13) of Pham–Zakharov**: a balanced convex combination
`Σ c_x (x − a) = 0` on `A₀` with `0 ≤ c_x ≤ w` and `Σ c_x = 1` yields a
partition `A₁ ⊔ A₂ = A₀ ∖ {a}` in which both parts have total weight at least
`(1 − 2w)/2` (hence size at least `(1 − 2w)/(2w)`), and the two weighted
displacement sums are opposite:
`Σ_{A₁} c_x • (x − a) = − Σ_{A₂} c_x • (x − a)`. -/
theorem balanced_convex_combination_split {d : ℕ} {A₀ : Finset (Fin d → ℝ)}
    {a : Fin d → ℝ} {c : (Fin d → ℝ) → ℝ} {w : ℝ} (hw : 0 < w)
    (hc0 : ∀ x ∈ A₀, 0 ≤ c x) (hcw : ∀ x ∈ A₀, c x ≤ w)
    (hcsum : ∑ x ∈ A₀, c x = 1)
    (hczero : ∑ x ∈ A₀, c x • (x - a) = 0) :
    ∃ A₁ A₂ : Finset (Fin d → ℝ),
      A₁ ⊆ A₀.erase a ∧ A₂ ⊆ A₀.erase a ∧ Disjoint A₁ A₂ ∧
      A₁ ∪ A₂ = A₀.erase a ∧
      (1 - 2 * w) / 2 ≤ (A₁.card : ℝ) * w ∧
      (1 - 2 * w) / 2 ≤ (A₂.card : ℝ) * w ∧
      (∑ x ∈ A₁, c x • (x - a)) = -(∑ x ∈ A₂, c x • (x - a)) := by
  classical
  have hSS : A₀.erase a ⊆ A₀ := Finset.erase_subset _ _
  have hSsum : 1 - w ≤ ∑ x ∈ A₀.erase a, c x := by
    by_cases ha : a ∈ A₀
    · have e := Finset.add_sum_erase A₀ c ha
      rw [hcsum] at e
      linarith [hcw a ha]
    · rw [Finset.erase_eq_self.mpr ha, hcsum]
      linarith [hw]
  obtain ⟨T, hTS, hbal⟩ := exists_subset_sum_abs_sub_le (A₀.erase a)
    (fun x hx ↦ hc0 x (hSS hx)) (fun x hx ↦ hcw x (hSS hx)) hw.le
  rw [abs_le] at hbal
  have hpq : ∑ x ∈ T, c x + ∑ x ∈ A₀.erase a \ T, c x
      = ∑ x ∈ A₀.erase a, c x := by
    have h := Finset.sum_sdiff hTS (f := c)
    linarith [h]
  have hTle : ∑ x ∈ T, c x ≤ (T.card : ℝ) * w := by
    calc ∑ x ∈ T, c x ≤ ∑ _x ∈ T, w :=
          Finset.sum_le_sum fun x hx ↦ hcw x (hSS (hTS hx))
      _ = (T.card : ℝ) * w := by rw [Finset.sum_const, nsmul_eq_mul]
  have hSle : ∑ x ∈ A₀.erase a \ T, c x
      ≤ ((A₀.erase a \ T).card : ℝ) * w := by
    calc ∑ x ∈ A₀.erase a \ T, c x ≤ ∑ _x ∈ A₀.erase a \ T, w :=
          Finset.sum_le_sum fun x hx ↦
            hcw x (hSS (Finset.mem_sdiff.mp hx).1)
      _ = ((A₀.erase a \ T).card : ℝ) * w := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine ⟨T, A₀.erase a \ T, hTS, Finset.sdiff_subset, Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset hTS, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have hSzero : ∑ x ∈ A₀.erase a, c x • (x - a) = 0 := by
      by_cases ha : a ∈ A₀
      · have e := Finset.add_sum_erase A₀ (fun x ↦ c x • (x - a)) ha
        rw [sub_self, smul_zero, zero_add] at e
        exact e.trans hczero
      · rw [Finset.erase_eq_self.mpr ha, hczero]
    have hvec : (∑ x ∈ A₀.erase a \ T, c x • (x - a))
        + (∑ x ∈ T, c x • (x - a)) = 0 :=
      (Finset.sum_sdiff hTS (f := fun x ↦ c x • (x - a))).trans hSzero
    exact add_eq_zero_iff_eq_neg.mp ((add_comm _ _).trans hvec)

end Balancing

section DiscreteJohn

/-! ### Successive minima and the discrete John theorem

This section develops the geometry-of-numbers input for the "discrete John
theorem" (Pham–Zakharov, arXiv:2410.14624v2, Lemma 7; cf. Tao–Vu,
Lemma 3.36): for a symmetric convex body `B ⊆ ℝ^d` there exist
`ℝ`-linearly independent integer vectors `w₁, …, w_d` (realizing the
successive minima `λᵢ` of `B` with respect to `ℤ^d`, in the sense of
Minkowski) such that `B ∩ ℤ^d` is contained in a box of side lengths
`≍ 1/λᵢ` in the basis `w`, while the box of side lengths `≍ c_d/λᵢ` is
contained in `B`.

We follow the proof of Minkowski's second theorem
`λ₁ ⋯ λ_d · vol(B) ≤ 2^d` given in Henk, *Successive minima and lattice
points* (Bull. Braz. Math. Soc. 33 (2002)), which is a finite counting
argument with translates of `λᵢ/2 · B`. -/

variable {d : ℕ} {B : Set (Fin d → ℝ)}

/-- The embedding `z ↦ (z i : ℝ)` of integer vectors into `Fin d → ℝ`. -/
def intVec {d : ℕ} (z : Fin d → ℤ) : Fin d → ℝ := fun i ↦ (z i : ℝ)

theorem intVec_apply (z : Fin d → ℤ) (i : Fin d) : intVec z i = (z i : ℝ) := rfl

@[simp] theorem intVec_zero : intVec (0 : Fin d → ℤ) = 0 := by
  funext i
  simp [intVec]

theorem intVec_add (z z' : Fin d → ℤ) : intVec (z + z') = intVec z + intVec z' := by
  funext i
  simp only [intVec, Pi.add_apply, Int.cast_add]

theorem intVec_neg (z : Fin d → ℤ) : intVec (-z) = -intVec z := by
  funext i
  simp only [intVec, Pi.neg_apply, Int.cast_neg]

theorem intVec_smul (n : ℤ) (z : Fin d → ℤ) : intVec (n • z) = (n : ℝ) • intVec z := by
  funext i
  simp only [intVec, Pi.smul_apply, smul_eq_mul, Int.cast_mul]

theorem intVec_injective : Function.Injective (intVec : (Fin d → ℤ) → Fin d → ℝ) := by
  intro z z' h
  funext i
  have := congrFun h i
  simpa [intVec] using this

theorem intVec_mem_span_basisFun (z : Fin d → ℤ) :
    intVec z ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d))) := by
  rw [mem_span_range_basisFun_iff]
  exact fun i ↦ ⟨z i, rfl⟩

theorem exists_intVec_of_mem_span_basisFun {x : Fin d → ℝ}
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))) :
    ∃ z : Fin d → ℤ, intVec z = x := by
  rw [mem_span_range_basisFun_iff] at hx
  choose z hz using hx
  exact ⟨z, funext fun i ↦ (hz i).symm⟩

/-- A symmetric convex set containing `0` is balanced. -/
theorem balanced_of_symmetric (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    (hBs : ∀ x ∈ B, -x ∈ B) : Balanced ℝ B := by
  intro a ha x hx
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
  rw [Real.norm_eq_abs, abs_le] at ha
  rcases le_total (0 : ℝ) a with ha0 | ha0
  · have := hBc hy hB0 ha0 (sub_nonneg.mpr ha.2) (by ring)
    simpa using this
  · have hneg : (-a) • (-y) ∈ B := by
      have := hBc (hBs _ hy) hB0 (neg_nonneg.mpr ha0)
        (by linarith : (0 : ℝ) ≤ 1 - -a) (by ring)
      simpa using this
    have hswap : a • y = (-a) • (-y) := by rw [smul_neg, neg_smul, neg_neg]
    rw [hswap]
    exact hneg

/-- The gauge of a symmetric convex open body containing `0` agrees with
membership in dilations: `x ∈ r • B ↔ gauge B x < r` for `r > 0`. -/
theorem mem_smul_iff_gauge_lt (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) {r : ℝ} (hr : 0 < r) (x : Fin d → ℝ) :
    x ∈ r • B ↔ gauge B x < r := by
  have hz : (0 : Fin d → ℝ) ∈ r • B := by
    have := Set.smul_mem_smul_set hB0 (a := r)
    rwa [smul_zero] at this
  have h1 : {x : Fin d → ℝ | gauge (r • B) x < 1} = r • B :=
    setOfPred_gauge_lt_one_eq_self_of_isOpen (hBc.smul r) hz (hBo.smul₀ hr.ne')
  rw [← h1]
  simp only [Set.mem_ofPred_eq]
  rw [gauge_smul_left_of_nonneg hr.le, Pi.smul_apply, smul_eq_mul,
    inv_mul_lt_iff₀ hr, mul_one]

/-- `x ∈ closure (r • B)` iff `gauge B x ≤ r`, for `r > 0`. -/
theorem mem_closure_smul_iff_gauge_le (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) {r : ℝ} (hr : 0 < r) (x : Fin d → ℝ) :
    x ∈ closure (r • B) ↔ gauge B x ≤ r := by
  have hz : (0 : Fin d → ℝ) ∈ r • B := by
    have := Set.smul_mem_smul_set hB0 (a := r)
    rwa [smul_zero] at this
  have h_nhds : r • B ∈ 𝓝 (0 : Fin d → ℝ) :=
    (hBo.smul₀ hr.ne').mem_nhds hz
  rw [← gauge_le_one_iff_mem_closure (hBc.smul r) h_nhds,
    gauge_smul_left_of_nonneg hr.le, Pi.smul_apply, smul_eq_mul,
    inv_mul_le_iff₀ hr, mul_one]

/-- There are only finitely many integer vectors of bounded gauge. -/
theorem finite_intVec_gauge_le (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) (hBb : Bornology.IsBounded B) (C : ℝ) :
    Set.Finite {z : Fin d → ℤ | gauge B (intVec z) ≤ C} := by
  obtain ⟨R, hR⟩ := hBb.subset_closedBall (0 : Fin d → ℝ)
  have hR0 : 0 ≤ R := Metric.nonempty_closedBall.mp ⟨0, hR hB0⟩
  set D : ℝ := max C 0 + 1 with hD
  have hDpos : (0 : ℝ) < D := by rw [hD]; linarith [le_max_right C 0]
  have hCD : C ≤ D := by rw [hD]; linarith [le_max_left C 0]
  have hsub : D • B ⊆ Metric.closedBall (0 : Fin d → ℝ) (D * R) := by
    calc D • B ⊆ D • Metric.closedBall 0 R := fun x hx ↦ by
          obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
          exact Set.smul_mem_smul_set (hR hy)
      _ = Metric.closedBall (D • (0 : Fin d → ℝ)) (‖D‖ * R) := smul_closedBall D _ hR0
      _ = Metric.closedBall 0 (D * R) := by rw [smul_zero, Real.norm_of_nonneg hDpos.le]
  refine Set.Finite.subset
    (Set.Finite.pi (fun i ↦ Set.finite_Icc (-(⌈D * R⌉₊ : ℤ)) ⌈D * R⌉₊)) ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  rw [Set.mem_univ_pi]
  intro i
  have hx : intVec z ∈ Metric.closedBall (0 : Fin d → ℝ) (D * R) := by
    have h1 : intVec z ∈ closure (D • B) := by
      rw [mem_closure_smul_iff_gauge_le hBo hBc hB0 hDpos]
      exact hz.trans hCD
    have h2 := closure_mono hsub h1
    rwa [Metric.closure_closedBall] at h2
  have h3 : |(z i : ℝ)| ≤ D * R := by
    calc |(z i : ℝ)| = ‖intVec z i‖ := by rw [intVec_apply, Real.norm_eq_abs]
      _ ≤ ‖intVec z‖ := norm_le_pi_norm (intVec z) i
      _ ≤ D * R := mem_closedBall_zero_iff.mp hx
  have h4 : |z i| ≤ ⌈D * R⌉₊ := by
    have h5 : ((|z i| : ℤ) : ℝ) ≤ ((⌈D * R⌉₊ : ℤ) : ℝ) := by
      rw [Int.cast_abs, Int.cast_natCast]
      exact h3.trans (Nat.le_ceil _)
    exact Int.cast_le.mp h5
  rw [Set.mem_Icc, ← abs_le]
  exact h4

/-- The standard basis vectors are integer vectors. -/
theorem basisFun_eq_intVec_single (i : Fin d) :
    Pi.basisFun ℝ (Fin d) i = intVec (Pi.single i 1) := by
  rw [Pi.basisFun_apply]
  funext j
  simp [intVec, Pi.single_apply]

/-- **Greedy minimization over integer vectors**: if `S` is a proper
subspace of `ℝ^d`, some integer vector `z ∉ S` minimizes `gauge B` among
all integer vectors outside `S`. -/
theorem exists_intVec_min_gauge_of_ne_top
    (hBo : IsOpen B) (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    (hBb : Bornology.IsBounded B)
    (S : Submodule ℝ (Fin d → ℝ)) (hS : S ≠ ⊤) :
    ∃ z : Fin d → ℤ, intVec z ∉ S ∧
      ∀ z' : Fin d → ℤ, intVec z' ∉ S → gauge B (intVec z) ≤ gauge B (intVec z') := by
  classical
  obtain ⟨u, hu⟩ : ∃ u : Fin d → ℤ, intVec u ∉ S := by
    by_contra h
    push_neg at h
    have hsub : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ S := by
      rw [← (Pi.basisFun ℝ (Fin d)).span_eq, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      rw [basisFun_eq_intVec_single]
      exact h _
    exact hS (top_unique hsub)
  set F : Set (Fin d → ℤ) :=
    {z | intVec z ∉ S ∧ gauge B (intVec z) ≤ gauge B (intVec u)} with hF
  have hFfin : F.Finite :=
    (finite_intVec_gauge_le hBo hBc hB0 hBb _).subset fun z hz ↦ hz.2
  obtain ⟨z, hzF, hzmin⟩ :=
    Set.exists_min_image F (fun z ↦ gauge B (intVec z)) hFfin ⟨u, hu, le_rfl⟩
  refine ⟨z, hzF.1, fun z' hz' ↦ ?_⟩
  by_cases hzz : gauge B (intVec z') ≤ gauge B (intVec u)
  · exact hzmin z' ⟨hz', hzz⟩
  · exact (hzF.2).trans (not_le.mp hzz).le

/-- **Existence of successive-minima vectors** (greedy construction):
there are `d` integer vectors `w₀, …, w_{d-1}`, linearly independent over
`ℝ`, such that `wᵢ` minimizes `gauge B` among all integer vectors outside
the span of `w₀, …, w_{i-1}`.  This is the qualitative heart of the
discrete John theorem. -/
theorem exists_succMinima
    (hBo : IsOpen B) (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    (hBb : Bornology.IsBounded B) :
    ∃ w : Fin d → (Fin d → ℤ),
      LinearIndependent ℝ (fun i ↦ intVec (w i)) ∧
      ∀ i : Fin d, ∀ z : Fin d → ℤ,
        intVec z ∉ Submodule.span ℝ
            (Set.range fun j : {j : Fin d // j < i} ↦ intVec (w j)) →
        gauge B (intVec (w i)) ≤ gauge B (intVec z) := by
  -- induction: build `w : Fin k → Fin d → ℤ` for `k ≤ d`
  suffices ∀ k : ℕ, k ≤ d → ∃ w : Fin k → (Fin d → ℤ),
      LinearIndependent ℝ (fun i ↦ intVec (w i)) ∧
      ∀ i : Fin k, ∀ z : Fin d → ℤ,
        intVec z ∉ Submodule.span ℝ
            (Set.range fun j : {j : Fin k // j < i} ↦ intVec (w j)) →
        gauge B (intVec (w i)) ≤ gauge B (intVec z) by
    obtain ⟨w, h1, h2⟩ := this d le_rfl
    exact ⟨w, h1, h2⟩
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨fun i ↦ i.elim0, linearIndependent_empty_type, fun i ↦ i.elim0⟩
  | succ k ih =>
      intro hk
      obtain ⟨w, hwI, hwMin⟩ := ih (Nat.le_of_succ_le hk)
      -- the span of the first `k` vectors is a proper subspace
      set W := fun i : Fin k ↦ intVec (w i) with hW
      have hS : Submodule.span ℝ (Set.range W) ≠ ⊤ := by
        intro htop
        have hle : Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ k := by
          calc Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ))
              = Module.finrank ℝ (Submodule.span ℝ (Set.range W)) := by
                rw [htop]
            _ ≤ (Set.range W).toFinset.card := finrank_span_le_card _
            _ ≤ Fintype.card (Fin k) := by
                rw [Set.toFinset_range]
                exact Finset.card_image_le
            _ = k := Fintype.card_fin _
        simp [Module.finrank_fintype_fun_eq_card] at hle
        omega
      obtain ⟨v, hvNot, hvMin⟩ :=
        exists_intVec_min_gauge_of_ne_top hBo hBc hB0 hBb _ hS
      refine ⟨Fin.snoc w v, ?_, ?_⟩
      · -- `intVec ∘ snoc w v = snoc (intVec ∘ w) (intVec v)`
        have hcomp : Fin.snoc (fun i ↦ intVec (w i)) (intVec v) =
            fun i ↦ intVec ((Fin.snoc w v : Fin (k+1) → Fin d → ℤ) i) :=
          (Fin.comp_snoc intVec w v).symm
        rw [← hcomp, linearIndependent_finSnoc]
        exact ⟨hwI, hvNot⟩
      · intro i z hz
        -- split on whether `i` is the last index
        by_cases hi : (i : ℕ) < k
        · -- the predecessors of `i` in `Fin (k+1)` are the `Fin.castSucc`s of
          -- the predecessors of `⟨i, hi⟩` in `Fin k`, and `Fin.snoc` agrees
          -- with `w` on them
          have hr : (Set.range fun j : {j : Fin (k+1) // j < i} ↦
                intVec ((Fin.snoc w v : Fin (k+1) → Fin d → ℤ) j)) =
              Set.range fun j : {j : Fin k // j < (⟨(i : ℕ), hi⟩ : Fin k)} ↦
                intVec (w j) := by
            ext x
            constructor
            · rintro ⟨j, rfl⟩
              have hjk : (j : Fin (k+1)).1 < k :=
                lt_trans (show (j : Fin (k+1)).1 < (i : ℕ) from j.2) hi
              refine ⟨⟨⟨(j : Fin (k+1)).1, hjk⟩, j.2⟩, ?_⟩
              show intVec (w ⟨(j : Fin (k+1)).1, hjk⟩) =
                  intVec ((Fin.snoc w v : Fin (k+1) → Fin d → ℤ) ↑j)
              conv_rhs =>
                rw [show (j : Fin (k+1)) = Fin.castSucc ⟨(j : Fin (k+1)).1, hjk⟩
                      from Fin.ext rfl]
              rw [Fin.snoc_castSucc]
            · rintro ⟨j, rfl⟩
              refine ⟨⟨Fin.castSucc j.1, j.2⟩, ?_⟩
              show intVec ((Fin.snoc w v : Fin (k+1) → Fin d → ℤ)
                    (Fin.castSucc j.1)) = intVec (w j.1)
              rw [Fin.snoc_castSucc]
          rw [hr] at hz
          have hi' : (Fin.snoc w v : Fin (k+1) → Fin d → ℤ) i =
              w ⟨(i : ℕ), hi⟩ := by
            conv_lhs =>
              rw [show i = Fin.castSucc ⟨(i : ℕ), hi⟩ from Fin.ext rfl]
            rw [Fin.snoc_castSucc]
          rw [hi']
          exact hwMin _ z hz
        · -- `i = last k`: its predecessors are exactly the `Fin.castSucc`s of
          -- all of `Fin k`, so the spanning set is `Set.range W`
          have hik : (i : ℕ) = k := by
            have := i.isLt
            omega
          have hi' : i = Fin.last k :=
            Fin.ext (hik.trans (Fin.val_last k).symm)
          subst hi'
          have hr : (Set.range fun j : {j : Fin (k+1) // j < Fin.last k} ↦
                intVec ((Fin.snoc w v : Fin (k+1) → Fin d → ℤ) j)) =
              Set.range fun j : Fin k ↦ intVec (w j) := by
            ext x
            constructor
            · rintro ⟨j, rfl⟩
              have hjk : (j : Fin (k+1)).1 < k := by
                have h : (j : Fin (k+1)) < Fin.last k := j.2
                rwa [Fin.lt_def, Fin.val_last] at h
              refine ⟨⟨(j : Fin (k+1)).1, hjk⟩, ?_⟩
              show intVec (w ⟨(j : Fin (k+1)).1, hjk⟩) =
                  intVec ((Fin.snoc w v : Fin (k+1) → Fin d → ℤ) ↑j)
              conv_rhs =>
                rw [show (j : Fin (k+1)) = Fin.castSucc ⟨(j : Fin (k+1)).1, hjk⟩
                      from Fin.ext rfl]
              rw [Fin.snoc_castSucc]
            · rintro ⟨j, rfl⟩
              refine ⟨⟨Fin.castSucc j, j.isLt⟩, ?_⟩
              show intVec ((Fin.snoc w v : Fin (k+1) → Fin d → ℤ)
                    (Fin.castSucc j)) = intVec (w j)
              rw [Fin.snoc_castSucc]
          rw [hr] at hz
          rw [Fin.snoc_last]
          rw [← hW] at hz
          exact hvMin z hz

/-- `intVec` of a finite sum is the sum of the images. -/
theorem intVec_sum {d : ℕ} (s : Finset (Fin d)) (f : Fin d → (Fin d → ℤ)) :
    intVec (∑ i ∈ s, f i) = ∑ i ∈ s, intVec (f i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, intVec_add, ih]

/-- The gauge of a finite sum is at most the sum of the gauges. -/
theorem gauge_sum_le (hBc : Convex ℝ B) (habs : Absorbent ℝ B)
    (s : Finset (Fin d)) (f : Fin d → (Fin d → ℝ)) :
    gauge B (∑ i ∈ s, f i) ≤ ∑ i ∈ s, gauge B (f i) := by
  induction s using Finset.induction with
  | empty => simp [gauge_zero]
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      exact (gauge_add_le hBc habs _ _).trans (add_le_add_right ih _)

/-- Points of gauge `< 1` lie in `B` (for `B` open, convex, containing `0`). -/
theorem mem_of_gauge_lt_one (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hB0 : (0 : Fin d → ℝ) ∈ B) {x : Fin d → ℝ} (hx : gauge B x < 1) :
    x ∈ B := by
  rw [← setOfPred_gauge_lt_one_eq_self_of_isOpen hBc hB0 hBo]
  exact hx

/-- The **inner box inclusion** of the discrete John theorem
(Pham–Zakharov, arXiv:2410.14624v2, Lemma 7): for the successive-minima
vectors `v` of `B` with `λᵢ = gauge B (intVec (v i))`, every integer
combination `Σᵢ zᵢ • vᵢ` with `|zᵢ| ≤ Nᵢ/(4d)` lies in `B`, where
`Nᵢ = ⌈λᵢ⁻¹⌉₊`.  Proof: `gauge` is subadditive and positively homogeneous
(`gauge_smul`), so `gauge (Σᵢ zᵢ vᵢ) ≤ Σᵢ |zᵢ|·λᵢ ≤ 2d·(4d)⁻¹ = 1/2`. -/
theorem exists_succMinima_box_subset
    (hBo : IsOpen B) (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    (hBs : ∀ x ∈ B, -x ∈ B) (hBb : Bornology.IsBounded B) :
    ∃ v : Fin d → (Fin d → ℤ), LinearIndependent ℝ (fun i ↦ intVec (v i)) ∧
      ∃ N : Fin d → ℕ, (∀ i, 0 < N i) ∧
        ∀ z : Fin d → ℤ,
          (∀ i, |(z i : ℝ)| ≤ (4 * (d : ℝ))⁻¹ * (N i : ℝ)) →
          intVec (∑ i, z i • v i) ∈ B := by
  classical
  obtain ⟨v, hvI, _hvMin⟩ := exists_succMinima hBo hBc hB0 hBb
  have hbal : Balanced ℝ B := balanced_of_symmetric hBc hB0 hBs
  have habs : Absorbent ℝ B := absorbent_nhds_zero (hBo.mem_nhds hB0)
  have hvN : Bornology.IsVonNBounded ℝ B :=
    (NormedSpace.isVonNBounded_iff ℝ).mpr hBb
  have hgauge : ∀ i : Fin d, 0 < gauge B (intVec (v i)) :=
    fun i ↦ (gauge_pos habs hvN).mpr (hvI.ne_zero i)
  have hc14 : (4 * (d : ℝ))⁻¹ ≤ 1 / 4 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd]; norm_num
    · have h4d : (4 : ℝ) ≤ 4 * d := by
        have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have h4pos : (0 : ℝ) < 4 * d := by linarith
      calc (4 * (d : ℝ))⁻¹ ≤ (4 : ℝ)⁻¹ :=
            (inv_le_inv₀ h4pos (by norm_num)).mpr h4d
        _ = 1 / 4 := by norm_num
  have hc1 : (4 * (d : ℝ))⁻¹ < 1 := hc14.trans_lt (by norm_num)
  refine ⟨v, hvI, fun i ↦ ⌈(gauge B (intVec (v i)))⁻¹⌉₊,
    fun i ↦ Nat.ceil_pos.mpr (inv_pos.mpr (hgauge i)), ?_⟩
  intro z hz
  have hmap : intVec (∑ i, z i • v i) = ∑ i, (z i : ℝ) • intVec (v i) := by
    rw [intVec_sum]
    exact Finset.sum_congr rfl fun i _ ↦ intVec_smul _ _
  have hterm : ∀ i : Fin d,
      |(z i : ℝ)| * gauge B (intVec (v i)) ≤ 2 * (4 * (d : ℝ))⁻¹ := by
    intro i
    have hgi := hgauge i
    have hzi : |(z i : ℝ)| ≤
        (4 * (d : ℝ))⁻¹ * (⌈(gauge B (intVec (v i)))⁻¹⌉₊ : ℝ) := hz i
    rcases le_total (gauge B (intVec (v i))) 1 with h1 | h1
    · have hNi : (⌈(gauge B (intVec (v i)))⁻¹⌉₊ : ℝ) ≤
          (gauge B (intVec (v i)))⁻¹ + 1 :=
        (Nat.ceil_lt_add_one (inv_nonneg.mpr hgi.le)).le
      calc |(z i : ℝ)| * gauge B (intVec (v i))
          ≤ ((4 * (d : ℝ))⁻¹ * ⌈(gauge B (intVec (v i)))⁻¹⌉₊) *
              gauge B (intVec (v i)) :=
            mul_le_mul_of_nonneg_right hzi hgi.le
        _ = (4 * (d : ℝ))⁻¹ *
              (⌈(gauge B (intVec (v i)))⁻¹⌉₊ * gauge B (intVec (v i))) := by
            ring
        _ ≤ (4 * (d : ℝ))⁻¹ *
              (((gauge B (intVec (v i)))⁻¹ + 1) * gauge B (intVec (v i))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hNi hgi.le)
              (inv_nonneg.mpr (by positivity))
        _ = (4 * (d : ℝ))⁻¹ * (1 + gauge B (intVec (v i))) := by
            congr 1
            rw [add_mul, inv_mul_cancel₀ hgi.ne', one_mul]
        _ ≤ (4 * (d : ℝ))⁻¹ * 2 :=
            mul_le_mul_of_nonneg_left (by linarith)
              (inv_nonneg.mpr (by positivity))
        _ = 2 * (4 * (d : ℝ))⁻¹ := by ring
    · have hNi1 : ⌈(gauge B (intVec (v i)))⁻¹⌉₊ = 1 := by
        apply le_antisymm
        · rw [Nat.ceil_le, Nat.cast_one]
          exact (inv_le_one₀ hgi).mpr h1
        · exact Nat.ceil_pos.mpr (inv_pos.mpr hgi)
      have hzi0 : z i = 0 := by
        rw [hNi1, Nat.cast_one, mul_one] at hzi
        have hzi' : |(z i : ℝ)| < 1 := hzi.trans_lt hc1
        have habs' : |z i| < 1 := by
          have h2 : ((|z i| : ℤ) : ℝ) < 1 := by rwa [Int.cast_abs]
          exact_mod_cast h2
        exact Int.abs_lt_one_iff.mp habs'
      rw [hzi0, Int.cast_zero, abs_zero, zero_mul]
      positivity
  have hgsum : gauge B (intVec (∑ i, z i • v i)) ≤
      ∑ i, |(z i : ℝ)| * gauge B (intVec (v i)) := by
    rw [hmap]
    calc gauge B (∑ i, (z i : ℝ) • intVec (v i))
        ≤ ∑ i, gauge B ((z i : ℝ) • intVec (v i)) := gauge_sum_le hBc habs _ _
      _ = ∑ i, |(z i : ℝ)| * gauge B (intVec (v i)) :=
          Finset.sum_congr rfl fun i _ ↦ by
            rw [gauge_smul hbal, Real.norm_eq_abs]
  have htot : ∑ i, |(z i : ℝ)| * gauge B (intVec (v i)) ≤ 1 / 2 := by
    calc ∑ i, |(z i : ℝ)| * gauge B (intVec (v i))
        ≤ ∑ _i : Fin d, 2 * (4 * (d : ℝ))⁻¹ :=
          Finset.sum_le_sum fun i _ ↦ hterm i
      _ = (d : ℝ) * (2 * (4 * (d : ℝ))⁻¹) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ ≤ 1 / 2 := by
          rcases Nat.eq_zero_or_pos d with hd | hd
          · rw [hd]; norm_num
          · have h4d : (4 : ℝ) * d ≠ 0 := by
              have hd' : (0 : ℝ) < d := by exact_mod_cast hd
              positivity
            have e : (d : ℝ) * (2 * (4 * (d : ℝ))⁻¹) = 1 / 2 := by
              field_simp
              ring
            exact e.le
  exact mem_of_gauge_lt_one hBo hBc hB0
    (hgsum.trans_lt (htot.trans_lt (by norm_num)))

/-- **Discrete John theorem, qualitative form** (cf. Pham–Zakharov,
arXiv:2410.14624v2, Lemma 7): for an open convex symmetric bounded body
`B ⊆ ℝ^d` containing `0`, there is a constant `c > 0`, `d` linearly
independent integer vectors `vᵢ` and positive naturals `Nᵢ` such that the
coefficient box `P(v, c·N) = {Σᵢ zᵢ vᵢ : |zᵢ| ≤ c Nᵢ}` is contained in
`B ∩ ℤ^d`, while `B ∩ ℤ^d` is contained in `P(v, N)`.  Here we take the
standard basis `vᵢ = eᵢ` and `Nᵢ = ⌈R⌉₊ + 1` where `B ⊆ closedBall 0 R`;
the quantitative form of Lemma 7 uses successive-minima vectors and
`Nᵢ ≍ λᵢ⁻¹`. -/
theorem discrete_john
    (hBo : IsOpen B) (hBc : Convex ℝ B) (hB0 : (0 : Fin d → ℝ) ∈ B)
    (hBs : ∀ x ∈ B, -x ∈ B) (hBb : Bornology.IsBounded B) :
    ∃ (c : ℝ) (v : Fin d → (Fin d → ℤ)) (N : Fin d → ℕ),
      0 < c ∧ LinearIndependent ℝ (fun i ↦ intVec (v i)) ∧
      (∀ i, 0 < N i) ∧
      (∀ z : Fin d → ℤ, (∀ i, |(z i : ℝ)| ≤ c * (N i : ℝ)) →
          intVec (∑ i, z i • v i) ∈ B) ∧
      (∀ z : Fin d → ℤ, intVec z ∈ B →
          ∃ z' : Fin d → ℤ, (∀ i, |(z' i : ℝ)| ≤ (N i : ℝ)) ∧
            z = ∑ i, z' i • v i) := by
  classical
  obtain ⟨R, hR⟩ := hBb.subset_closedBall (0 : Fin d → ℝ)
  have hbal : Balanced ℝ B := balanced_of_symmetric hBc hB0 hBs
  have habs : Absorbent ℝ B := absorbent_nhds_zero (hBo.mem_nhds hB0)
  -- the coefficient bound is `Nᵢ = ⌈R⌉₊ + 1`; the constant `c` is chosen so
  -- that `c · Σᵢ Nᵢ λᵢ < 1`, where `λᵢ = gauge B eᵢ`
  have hterm0 : ∀ i : Fin d,
      0 ≤ ((⌈R⌉₊ + 1 : ℕ) : ℝ) * gauge B (Pi.basisFun ℝ (Fin d) i) :=
    fun i ↦ mul_nonneg (Nat.cast_nonneg _) (gauge_nonneg _)
  set S : ℝ := ∑ i : Fin d,
    ((⌈R⌉₊ + 1 : ℕ) : ℝ) * gauge B (Pi.basisFun ℝ (Fin d) i) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ hterm0 i
  have h2S : (0 : ℝ) < 2 * (1 + S) := by positivity
  refine ⟨(2 * (1 + S))⁻¹, fun i ↦ Pi.single i 1, fun _ ↦ ⌈R⌉₊ + 1,
    inv_pos.mpr h2S, ?_, fun _ ↦ Nat.succ_pos _, ?_, ?_⟩
  · -- the `vᵢ` are the standard basis vectors
    have hb : LinearIndependent ℝ (fun i ↦ Pi.basisFun ℝ (Fin d) i) :=
      (Pi.basisFun ℝ (Fin d)).linearIndependent
    simpa only [basisFun_eq_intVec_single] using hb
  · intro z hz
    have hmap : intVec (∑ i, z i •
          ((fun j ↦ Pi.single j (1 : ℤ)) : Fin d → Fin d → ℤ) i) =
        ∑ i, (z i : ℝ) • intVec (Pi.single i (1 : ℤ)) := by
      rw [intVec_sum]
      exact Finset.sum_congr rfl fun i _ ↦ intVec_smul _ _
    have hgsum : gauge B (intVec (∑ i, z i •
          ((fun j ↦ Pi.single j (1 : ℤ)) : Fin d → Fin d → ℤ) i)) ≤
        (2 * (1 + S))⁻¹ * S := by
      rw [hmap]
      calc gauge B (∑ i, (z i : ℝ) • intVec (Pi.single i 1))
          ≤ ∑ i, gauge B ((z i : ℝ) • intVec (Pi.single i 1)) :=
            gauge_sum_le hBc habs _ _
        _ = ∑ i, |(z i : ℝ)| * gauge B (intVec (Pi.single i 1)) :=
            Finset.sum_congr rfl fun i _ ↦ by
              rw [gauge_smul hbal, Real.norm_eq_abs]
        _ ≤ ∑ i, (2 * (1 + S))⁻¹ *
              (((⌈R⌉₊ + 1 : ℕ) : ℝ) * gauge B (Pi.basisFun ℝ (Fin d) i)) :=
            Finset.sum_le_sum fun i _ ↦ by
              rw [← basisFun_eq_intVec_single, ← mul_assoc]
              exact mul_le_mul_of_nonneg_right (hz i) (gauge_nonneg _)
        _ = (2 * (1 + S))⁻¹ * S := by rw [← Finset.mul_sum, ← hS]
    exact mem_of_gauge_lt_one hBo hBc hB0 (hgsum.trans_lt (by
      rw [inv_mul_eq_div, div_lt_one h2S]
      linarith))
  · intro z hzB
    refine ⟨z, fun i ↦ ?_, ?_⟩
    · have hzi : |(z i : ℝ)| ≤ R := by
        calc |(z i : ℝ)| = ‖intVec z i‖ := by
              rw [intVec_apply, Real.norm_eq_abs]
          _ ≤ ‖intVec z‖ := norm_le_pi_norm (intVec z) i
          _ ≤ R := mem_closedBall_zero_iff.mp (hR hzB)
      exact hzi.trans (by
        have h1 : (R : ℝ) ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
        have h2 : ((⌈R⌉₊ : ℝ)) ≤ ((⌈R⌉₊ + 1 : ℕ) : ℝ) := by
          rw [Nat.cast_add, Nat.cast_one]; linarith
        exact h1.trans h2)
    · funext j
      simp [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
end DiscreteJohn

end Nonaveraging
