import Mathlib

/-!
# Convex bodies, slabs, and the density-increment reduction

Auxiliary lemmas supporting `Nonaveraging.ConvexPosition.density_increment`
(Lemma 1 of Pham–Zakharov, arXiv:2410.14624v2, §2).

The main contents:

* `DensityIncrementGoal` — the existential conclusion of `density_increment`
  packaged as a standalone predicate, so that case analyses can produce it.
* Degenerate / easy-case eliminations (`of_empty`, `of_volume_eq_top`,
  `of_convexHull_volume_le`, `of_cover`, `of_subset`): the only genuinely
  remaining case of Lemma 1 is a *bounded* `Ω` (finite volume) containing a
  *nonempty* `A` whose convex hull has volume `> δ · vol Ω`.
* `Real.rpow` bookkeeping for the exponent `(d-1)/(d+1) + ε`.
* Convexity of slabs and graph-slabs (`Convex.inter_slab`,
  `Convex.inter_graph_slab`, `convex_graphSlab`) — the shape of the convex
  subregion `Ω'` used in the paper.
* Coordinate projections `projFin`, `lastCoord` on `Fin d → ℝ`.

The remaining mathematical content (documented in the proof of
`density_increment`) is: the dyadic-box decomposition of `A`, the fact that the
relevant boxes are again in convex position, a covering/averaging argument on
`𝕊^{d-1}` replacing the random rotation, the concave upper-envelope function,
an application of `convex_linear_approx`, and the volume estimate of the
resulting slab via `MeasureTheory.volume_pi_pi` / Fubini.
-/

open Finset MeasureTheory

open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Nonaveraging

section RpowBounds

/-- For `0 < δ ≤ 1` and `τ ≤ 1` we have `δ ≤ δ ^ τ`. -/
theorem le_rpow_self_of_le_one {δ τ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) (hτ : τ ≤ 1) :
    δ ≤ δ ^ τ := by
  have h := Real.rpow_le_rpow_of_exponent_ge h0 h1 hτ
  rwa [Real.rpow_one] at h

/-- For `0 < δ < 1` and `0 < τ` we have `δ ^ τ < 1`. -/
theorem rpow_lt_one_of_pos {δ τ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) (hτ : 0 < τ) :
    δ ^ τ < 1 := by
  have h := Real.rpow_lt_rpow h0.le h1 hτ
  rwa [Real.one_rpow] at h

/-- For `0 < δ` and `0 ≤ τ` we have `δ ^ τ ≤ 1` provided `δ ≤ 1`. -/
theorem rpow_le_one_of_pos {δ τ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) (hτ : 0 ≤ τ) :
    δ ^ τ ≤ 1 := by
  have h := Real.rpow_le_rpow h0.le h1 hτ
  rwa [Real.one_rpow] at h

/-- For `0 ≤ η ≤ 1` and `0 ≤ p` we have `η ^ p ≤ 1`. -/
theorem rpow_le_one' {η p : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hp : 0 ≤ p) :
    η ^ p ≤ 1 := by
  have h := Real.rpow_le_rpow h0 h1 hp
  rwa [Real.one_rpow] at h

/-- For `0 < η ≤ 1` and `p ≤ q` we have `η ^ q ≤ η ^ p`
(the base is at most `1`, so larger exponents give smaller values). -/
theorem rpow_le_rpow_exponent {η p q : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) (hpq : p ≤ q) :
    η ^ q ≤ η ^ p :=
  Real.rpow_le_rpow_of_exponent_ge h0 h1 hpq

/-- The exponent `(d-1)/(d+1) + ε` is nonnegative for `d ≥ 1`, `ε ≥ 0`. -/
theorem density_exponent_nonneg {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ (d - 1 : ℝ) / (d + 1) + ε := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnn : (0 : ℝ) ≤ ((d : ℝ) - 1) / (d + 1) := div_nonneg (by linarith) (by linarith)
  linarith

/-- The exponent `(d-1)/(d+1) + ε` is strictly positive for `d ≥ 1`, `ε > 0`. -/
theorem density_exponent_pos {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    0 < (d - 1 : ℝ) / (d + 1) + ε := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnn : (0 : ℝ) ≤ ((d : ℝ) - 1) / (d + 1) := div_nonneg (by linarith) (by linarith)
  linarith

end RpowBounds

/-!
## The packaged conclusion

`DensityIncrementGoal d δ τ ε Ω A` is exactly the existential statement
produced by `density_increment` once `Ω` and `A` are fixed.
-/

/-- The conclusion of `density_increment` for fixed `d, δ, τ, ε, Ω, A`:
there is `η ∈ [δ, δ^τ]` and a convex `Ω' ⊆ Ω` with `vol Ω' ≤ η·vol Ω` and
`|A ∩ Ω'| ≥ η^{(d-1)/(d+1)+ε}·|A|`. -/
def DensityIncrementGoal (d : ℕ) (δ τ ε : ℝ) (Ω : Set (Fin d → ℝ))
    (A : Finset (Fin d → ℝ)) : Prop :=
  ∃ η : ℝ, δ ≤ η ∧ η ≤ δ ^ τ ∧ ∃ Ω' : Set (Fin d → ℝ),
    Convex ℝ Ω' ∧ Ω' ⊆ Ω ∧
      volume Ω' ≤ ENNReal.ofReal η * volume Ω ∧
      η ^ ((d - 1 : ℝ) / (d + 1) + ε) * A.card ≤
        ((A.filter fun a ↦ (a : Fin d → ℝ) ∈ Ω').card : ℝ)

namespace DensityIncrementGoal

/-- Repackaging: to prove the goal it suffices to find `η` and `Ω'` with the
listed properties. -/
theorem of_exists {d : ℕ} {δ τ ε : ℝ} {Ω : Set (Fin d → ℝ)}
    {A : Finset (Fin d → ℝ)} {η : ℝ} (hδη : δ ≤ η) (hηδ : η ≤ δ ^ τ)
    {Ω' : Set (Fin d → ℝ)} (hconv : Convex ℝ Ω') (hsub : Ω' ⊆ Ω)
    (hvol : volume Ω' ≤ ENNReal.ofReal η * volume Ω)
    (hcount : η ^ ((d - 1 : ℝ) / (d + 1) + ε) * A.card ≤
      ((A.filter fun a ↦ (a : Fin d → ℝ) ∈ Ω').card : ℝ)) :
    DensityIncrementGoal d δ τ ε Ω A :=
  ⟨η, hδη, hηδ, Ω', hconv, hsub, hvol, hcount⟩

/-- **Main reduction.** To prove the goal it suffices to find
`η ∈ [δ, δ^τ]`, a convex set `Ω' ⊆ Ω` of volume `≤ η·vol Ω`, and a sub-finset
`A' ⊆ A` of size `≥ η^{(d-1)/(d+1)+ε}·|A|` contained in `Ω'`. -/
theorem of_subset {d : ℕ} {δ τ ε : ℝ} {Ω : Set (Fin d → ℝ)}
    {A A' : Finset (Fin d → ℝ)} {η : ℝ} (hδη : δ ≤ η) (hηδ : η ≤ δ ^ τ)
    {Ω' : Set (Fin d → ℝ)} (hconv : Convex ℝ Ω') (hsub : Ω' ⊆ Ω)
    (hvol : volume Ω' ≤ ENNReal.ofReal η * volume Ω)
    (hA'A : A' ⊆ A) (hA'Ω : ∀ a ∈ A', (a : Fin d → ℝ) ∈ Ω')
    (hcount : η ^ ((d - 1 : ℝ) / (d + 1) + ε) * A.card ≤ (A'.card : ℝ)) :
    DensityIncrementGoal d δ τ ε Ω A := by
  refine ⟨η, hδη, hηδ, Ω', hconv, hsub, hvol, ?_⟩
  refine hcount.trans ?_
  rw [Nat.cast_le]
  exact Finset.card_le_card (Finset.subset_iff.mpr fun a ha ↦
    Finset.mem_filter.mpr ⟨hA'A ha, hA'Ω a ha⟩)

/-- **Cover case.** If a convex `Ω' ⊆ Ω` contains *all* of `A` and
`0 ≤ η ≤ 1`, the counting bound is automatic since `η^p ≤ 1`. -/
theorem of_cover {d : ℕ} {δ τ ε : ℝ} {Ω : Set (Fin d → ℝ)}
    {A : Finset (Fin d → ℝ)} {η : ℝ}
    (hδη : δ ≤ η) (hηδ : η ≤ δ ^ τ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hp : 0 ≤ (d - 1 : ℝ) / (d + 1) + ε)
    {Ω' : Set (Fin d → ℝ)} (hconv : Convex ℝ Ω') (hsub : Ω' ⊆ Ω)
    (hcov : ∀ a ∈ A, (a : Fin d → ℝ) ∈ Ω')
    (hvol : volume Ω' ≤ ENNReal.ofReal η * volume Ω) :
    DensityIncrementGoal d δ τ ε Ω A := by
  refine ⟨η, hδη, hηδ, Ω', hconv, hsub, hvol, ?_⟩
  have hf : A.filter (fun a ↦ (a : Fin d → ℝ) ∈ Ω') = A :=
    Finset.filter_eq_self.mpr hcov
  rw [hf]
  have h1 : η ^ ((d - 1 : ℝ) / (d + 1) + ε) ≤ 1 := rpow_le_one' hη0 hη1 hp
  calc η ^ _ * (A.card : ℝ) ≤ 1 * A.card :=
        mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
    _ = _ := one_mul _

/-- **Empty case.** The goal is trivial when `A = ∅`, taking `Ω' = ∅` and any
`η` in the allowed range. -/
theorem of_empty {d : ℕ} {δ τ ε : ℝ} {Ω : Set (Fin d → ℝ)}
    {A : Finset (Fin d → ℝ)} {η : ℝ} (hδη : δ ≤ η) (hηδ : η ≤ δ ^ τ)
    (hA : A = ∅) :
    DensityIncrementGoal d δ τ ε Ω A := by
  refine ⟨η, hδη, hηδ, ∅, convex_empty, Set.empty_subset Ω, ?_, ?_⟩
  · rw [measure_empty]
    exact bot_le
  · subst hA
    simp

/-- **Infinite-volume case.** If `volume Ω = ⊤` the volume bound is automatic;
take `Ω' = Ω` and any `η ∈ (0,1]` in the allowed range. -/
theorem of_volume_eq_top {d : ℕ} {δ τ ε : ℝ} {Ω : Set (Fin d → ℝ)}
    {A : Finset (Fin d → ℝ)} {η : ℝ}
    (hconv : Convex ℝ Ω) (hsub : ∀ a ∈ A, (a : Fin d → ℝ) ∈ Ω)
    (hvol : volume Ω = ⊤) (hδη : δ ≤ η) (hηδ : η ≤ δ ^ τ)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hp : 0 ≤ (d - 1 : ℝ) / (d + 1) + ε) :
    DensityIncrementGoal d δ τ ε Ω A := by
  refine of_cover hδη hηδ hη0.le hη1 hp hconv (fun a ha ↦ ha) hsub ?_
  rw [hvol, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hη0).ne']

/-- **Small-hull case.** If `convexHull A` already has volume `≤ η·vol Ω` for
some `η ∈ (0,1]` in the allowed range, take `Ω' = convexHull A`. In particular
this disposes of the case `vol (convexHull A) ≤ δ·vol Ω` (take `η = δ`) and of
degenerate `A` (hull has volume `0`). -/
theorem of_convexHull_volume_le {d : ℕ} {δ τ ε : ℝ} {Ω : Set (Fin d → ℝ)}
    {A : Finset (Fin d → ℝ)} {η : ℝ}
    (hconvΩ : Convex ℝ Ω) (hsub : ∀ a ∈ A, (a : Fin d → ℝ) ∈ Ω)
    (hvol : volume (convexHull ℝ (A : Set (Fin d → ℝ))) ≤
      ENNReal.ofReal η * volume Ω)
    (hδη : δ ≤ η) (hηδ : η ≤ δ ^ τ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hp : 0 ≤ (d - 1 : ℝ) / (d + 1) + ε) :
    DensityIncrementGoal d δ τ ε Ω A := by
  refine of_cover hδη hηδ hη0.le hη1 hp (convex_convexHull ℝ _)
    (convexHull_min (fun x hx ↦ hsub x (Finset.mem_coe.mp hx)) hconvΩ)
    (fun a ha ↦ subset_convexHull ℝ _ (Finset.mem_coe.mpr ha)) hvol

/-- **Monotonicity in `ε`.** Since `η ≤ δ^τ < 1`, a larger `ε` makes `η^p`
*smaller*, so the statement for a smaller `ε` implies the one for a larger
`ε` — i.e. it suffices to prove `density_increment` for small `ε`
(the paper uses `ε ≤ 1/(d+1)`). -/
theorem of_mono_exponent {d : ℕ} {δ τ ε ε' : ℝ} {Ω : Set (Fin d → ℝ)}
    {A : Finset (Fin d → ℝ)} (hεε : ε ≤ ε')
    (h : DensityIncrementGoal d δ τ ε Ω A)
    (hη : ∀ η : ℝ, δ ≤ η → η ≤ δ ^ τ → 0 < η ∧ η ≤ 1) :
    DensityIncrementGoal d δ τ ε' Ω A := by
  obtain ⟨η, hδη, hηδ, Ω', hconv, hsub, hvol, hcount⟩ := h
  refine ⟨η, hδη, hηδ, Ω', hconv, hsub, hvol, ?_⟩
  obtain ⟨hη0, hη1⟩ := hη η hδη hηδ
  have hle : η ^ ((d - 1 : ℝ) / (d + 1) + ε') * A.card ≤
      η ^ ((d - 1 : ℝ) / (d + 1) + ε) * A.card := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact rpow_le_rpow_exponent hη0 hη1 (add_le_add_right hεε _)
  linarith

end DensityIncrementGoal

/-!
## Slab convexity

The convex subregion `Ω'` in the proof of Lemma 1 is the intersection of `Ω`
with a two-sided slab for a linear functional (after a change of coordinates,
the region `{x | π x ∈ Q ∧ |x_d − ℓ (π x)| ≤ c}`).
-/

section Slabs

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Intersecting a convex set with a lower half-space of a linear functional
preserves convexity. -/
theorem Convex.inter_halfSpace_le {Ω : Set E} (hΩ : Convex ℝ Ω)
    (f : E →ₗ[ℝ] ℝ) (t : ℝ) :
    Convex ℝ (Ω ∩ {x | f x ≤ t}) := by
  have hset : {x : E | f x ≤ t} = f ⁻¹' Set.Iic t := rfl
  rw [hset]
  exact hΩ.inter ((convex_Iic t).linear_preimage f)

/-- Intersecting a convex set with an upper half-space of a linear functional
preserves convexity. -/
theorem Convex.inter_halfSpace_ge {Ω : Set E} (hΩ : Convex ℝ Ω)
    (f : E →ₗ[ℝ] ℝ) (t : ℝ) :
    Convex ℝ (Ω ∩ {x | t ≤ f x}) := by
  have hset : {x : E | t ≤ f x} = f ⁻¹' Set.Ici t := rfl
  rw [hset]
  exact hΩ.inter ((convex_Ici t).linear_preimage f)

/-- Intersecting a convex set with a two-sided slab `{x | a ≤ f x ≤ b}` of a
linear functional preserves convexity. -/
theorem Convex.inter_slab {Ω : Set E} (hΩ : Convex ℝ Ω)
    (f : E →ₗ[ℝ] ℝ) (a b : ℝ) :
    Convex ℝ (Ω ∩ {x | a ≤ f x ∧ f x ≤ b}) := by
  have hset : {x : E | a ≤ f x ∧ f x ≤ b} = f ⁻¹' Set.Icc a b := by
    ext x
    simp [Set.mem_Icc]
  rw [hset]
  exact hΩ.inter ((convex_Icc a b).linear_preimage f)

/-- A "graph-slab" region `{x ∈ Ω | a ≤ g x − ℓ x ≤ b}` cut out of a convex
set by a band around a linear functional `g` relative to a linear functional
`ℓ` is convex.  Affine `ℓ` (as in the paper, `ℓ = b + ⟨l,·⟩`) is subsumed by
absorbing the constant into `a, b`. -/
theorem Convex.inter_graph_slab {Ω : Set E} (hΩ : Convex ℝ Ω)
    (g ℓ : E →ₗ[ℝ] ℝ) (a b : ℝ) :
    Convex ℝ (Ω ∩ {x | a ≤ g x - ℓ x ∧ g x - ℓ x ≤ b}) := by
  have hset : {x : E | a ≤ g x - ℓ x ∧ g x - ℓ x ≤ b}
      = {x : E | a ≤ (g - ℓ) x ∧ (g - ℓ) x ≤ b} := by
    simp [LinearMap.sub_apply]
  rw [hset]
  exact Convex.inter_slab hΩ (g - ℓ) a b

end Slabs

/-!
## Coordinate projections on `Fin d → ℝ`

For `d ≥ 1`, the projection `projFin` onto the first `d − 1` coordinates and
the last-coordinate functional `lastCoord`, used to describe the slab region
in the rotated frame.
-/

section Projections

/-- Projection `π : ℝ^d → ℝ^{d-1}` onto the first `d−1` coordinates,
as a linear map. -/
def projFin (d : ℕ) (hd : 1 ≤ d) : (Fin d → ℝ) →ₗ[ℝ] (Fin (d - 1) → ℝ) where
  toFun x := fun i ↦ x (Fin.castLT i (by have h := i.isLt; omega))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The last-coordinate functional `ℝ^d → ℝ`, as a linear map. -/
def lastCoord (d : ℕ) (hd : 1 ≤ d) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x ⟨d - 1, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem projFin_apply (d : ℕ) (hd : 1 ≤ d) (x : Fin d → ℝ) (i : Fin (d - 1)) :
    projFin d hd x i = x (Fin.castLT i (by have h := i.isLt; omega)) := rfl

@[simp]
theorem lastCoord_apply (d : ℕ) (hd : 1 ≤ d) (x : Fin d → ℝ) :
    lastCoord d hd x = x ⟨d - 1, by omega⟩ := rfl

/-- The "slab over a base" region
`{x | π x ∈ Q, a ≤ x_d − ℓ (π x) ≤ b}` in `ℝ^d`, the shape of the good
subregion in the proof of `density_increment` (in the rotated frame, with
`Q = Q_v` a small cube and `ℓ` the linear approximation of the upper
envelope `h`). -/
def graphSlab (d : ℕ) (hd : 1 ≤ d) (Q : Set (Fin (d - 1) → ℝ))
    (ℓ : (Fin (d - 1) → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ) : Set (Fin d → ℝ) :=
  {x | projFin d hd x ∈ Q ∧
    a ≤ lastCoord d hd x - ℓ (projFin d hd x) ∧
    lastCoord d hd x - ℓ (projFin d hd x) ≤ b}

/-- The graph-slab region is convex whenever the base `Q` is convex:
it is the preimage of the convex set `Q × [a,b]` under the linear map
`x ↦ (π x, x_d − ℓ (π x))`. -/
theorem convex_graphSlab (d : ℕ) (hd : 1 ≤ d) {Q : Set (Fin (d - 1) → ℝ)}
    (hQ : Convex ℝ Q) (ℓ : (Fin (d - 1) → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ) :
    Convex ℝ (graphSlab d hd Q ℓ a b) := by
  set T : (Fin d → ℝ) →ₗ[ℝ] (Fin (d - 1) → ℝ) × ℝ :=
    LinearMap.prod (projFin d hd) (lastCoord d hd - ℓ.comp (projFin d hd)) with hT
  have hset : graphSlab d hd Q ℓ a b = T ⁻¹' (Q ×ˢ Set.Icc a b) := by
    ext x
    simp [graphSlab, hT, LinearMap.sub_apply, LinearMap.comp_apply, Set.mem_Icc]
  rw [hset]
  exact (hQ.prod (convex_Icc a b)).linear_preimage T

end Projections

/-!
## Volume of products and boxes
-/

/-- The volume of a product box `∏ᵢ [aᵢ, bᵢ]` in `ℝ^k` is `∏ᵢ (bᵢ − aᵢ)`
(as an extended nonnegative real). -/
theorem volume_box_pi {k : ℕ} (a b : Fin k → ℝ) :
    volume (Set.pi Set.univ fun i ↦ Set.Icc (a i) (b i)) =
      ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [volume_pi_pi]
  exact Finset.prod_congr rfl fun i _ ↦ Real.volume_Icc

/-- In particular the closed cube `[t, t+r]^k` has volume `(ofReal r)^k`. -/
theorem volume_cube_pi {k : ℕ} (t : Fin k → ℝ) (r : ℝ) :
    volume (Set.pi Set.univ fun i ↦ Set.Icc (t i) (t i + r)) =
      ENNReal.ofReal r ^ k := by
  rw [volume_box_pi,
    Finset.prod_congr rfl (fun i _ ↦
      show ENNReal.ofReal (t i + r - t i) = ENNReal.ofReal r by congr 1; ring),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-!
## Zonotopes and the rounding lemma (paper Lemma 13 / CFP23)

The *zonotope* `𝒵_A` of a finite `A ⊆ ℝ^d` is the Minkowski sum of the
segments `[0, a]` for `a ∈ A`, i.e. the set of fractional subset sums
`∑ a ∈ A, θ a • a` with `θ a ∈ [0,1]`.  Lemma 13 of the paper (quoted from
CFP23) says every `z ∈ 𝒵_A` is within `√(d|A|)·wᵢ` of a subset sum of `A`.

We prove a *sharper* version (`exists_subset_sum_sub_le`): the error is at
most `d · wᵢ` in coordinate `i`, by the classical "vertex purification"
argument: the fibre `{θ ∈ [0,1]^A : Σ θ_a a = z}` is a polytope cut out by `d`
equations, and sliding along a kernel direction of the `d × |A|` matrix
`a ↦ a` always lets one drive a fractional coordinate to `0` or `1`.
-/

section Zonotope

/-- The zonotope of a finite set `A ⊆ ℝ^d`:
`{∑ a ∈ A, θ a • a | θ : A → [0,1]}`. -/
def zonotope {d : ℕ} (A : Finset (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {z | ∃ θ : (Fin d → ℝ) → ℝ,
    (∀ a ∈ A, θ a ∈ Set.Icc 0 1) ∧ z = ∑ a ∈ A, θ a • a}

theorem mem_zonotope {d : ℕ} {A : Finset (Fin d → ℝ)} {z : Fin d → ℝ} :
    z ∈ zonotope A ↔ ∃ θ : (Fin d → ℝ) → ℝ,
      (∀ a ∈ A, θ a ∈ Set.Icc 0 1) ∧ z = ∑ a ∈ A, θ a • a :=
  Iff.rfl

theorem zero_mem_zonotope {d : ℕ} (A : Finset (Fin d → ℝ)) :
    (0 : Fin d → ℝ) ∈ zonotope A :=
  ⟨0, fun _ _ ↦ ⟨le_rfl, zero_le_one⟩, by simp⟩

theorem zonotope_mono {d : ℕ} {A B : Finset (Fin d → ℝ)} (h : A ⊆ B) :
    zonotope A ⊆ zonotope B := by
  classical
  rintro z ⟨θ, hθ, rfl⟩
  refine ⟨fun a ↦ if a ∈ A then θ a else 0, fun a ha ↦ ?_, ?_⟩
  · show (if a ∈ A then θ a else 0) ∈ Set.Icc 0 1
    by_cases haA : a ∈ A
    · rw [ite_eq_left haA]; exact hθ a haA
    · rw [ite_eq_right haA]; exact ⟨le_rfl, zero_le_one⟩
  · show ∑ a ∈ A, θ a • a = ∑ a ∈ B, (if a ∈ A then θ a else 0) • a
    calc ∑ a ∈ A, θ a • a
        = ∑ a ∈ A, (if a ∈ A then θ a • a else 0) :=
          (Finset.sum_congr rfl fun a ha ↦ by rw [ite_eq_left ha]).symm
      _ = ∑ a ∈ B, (if a ∈ A then θ a • a else 0) :=
          Finset.sum_subset h fun a _ ha ↦ by rw [ite_eq_right ha]
      _ = ∑ a ∈ B, (if a ∈ A then θ a else 0) • a :=
          Finset.sum_congr rfl fun a _ ↦ by split_ifs <;> simp

/-- The zonotope is convex: it is the linear image of the cube `[0,1]^A`. -/
theorem convex_zonotope {d : ℕ} (A : Finset (Fin d → ℝ)) :
    Convex ℝ (zonotope A) := by
  rintro z₁ ⟨θ₁, hθ₁, rfl⟩ z₂ ⟨θ₂, hθ₂, rfl⟩ α β hα hβ hαβ
  refine ⟨fun a ↦ α * θ₁ a + β * θ₂ a, fun a ha ↦ ?_, ?_⟩
  · have h1 := hθ₁ a ha
    have h2 := hθ₂ a ha
    exact ⟨by nlinarith [hα, hβ, h1.1, h2.1],
      by nlinarith [hα, hβ, h1.2, h2.2, hαβ]⟩
  · have e : ∀ a ∈ A, (fun a ↦ α * θ₁ a + β * θ₂ a) a • a
        = α • (θ₁ a • a) + β • (θ₂ a • a) := fun a _ ↦ by
        show (α * θ₁ a + β * θ₂ a) • a = α • (θ₁ a • a) + β • (θ₂ a • a)
        rw [add_smul, mul_smul, mul_smul]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib,
      Finset.smul_sum, Finset.smul_sum]

/-- **Iterative rounding**: a weighted sum `∑ θ_a • a` with `θ_a ∈ [0,1]`
equals a weighted sum `∑ φ_a • a` with `φ_a ∈ [0,1]` in which at most `d`
coefficients are fractional.  If the fractional support `F` has size `> d`,
the vectors `a ∈ F` are linearly dependent, and perturbing `θ` along the
relation until some coefficient hits `0` or `1` strictly shrinks `F`. -/
theorem exists_rounded_weights {d : ℕ} {A : Finset (Fin d → ℝ)}
    (θ : (Fin d → ℝ) → ℝ) (hθ : ∀ a ∈ A, θ a ∈ Set.Icc 0 1) :
    ∃ φ : (Fin d → ℝ) → ℝ,
      (∀ a ∈ A, φ a ∈ Set.Icc 0 1) ∧
      (A.filter fun a ↦ φ a ∈ Set.Ioo 0 1).card ≤ d ∧
      (∑ a ∈ A, φ a • a) = ∑ a ∈ A, θ a • a := by
  classical
  suffices key : ∀ n : ℕ, ∀ θ : (Fin d → ℝ) → ℝ,
      (∀ a ∈ A, θ a ∈ Set.Icc 0 1) →
      (A.filter fun a ↦ θ a ∈ Set.Ioo 0 1).card ≤ n + d →
      ∃ φ : (Fin d → ℝ) → ℝ,
        (∀ a ∈ A, φ a ∈ Set.Icc 0 1) ∧
        (A.filter fun a ↦ φ a ∈ Set.Ioo 0 1).card ≤ d ∧
        (∑ a ∈ A, φ a • a) = ∑ a ∈ A, θ a • a by
    exact key ((A.filter fun a ↦ θ a ∈ Set.Ioo 0 1).card) θ hθ
      (Nat.le_add_right _ _)
  intro n
  induction n with
  | zero =>
      intro θ hθ hcard
      exact ⟨θ, hθ, by simpa using hcard, rfl⟩
  | succ n ih =>
      intro θ hθ hcard
      by_cases hsmall : (A.filter fun a ↦ θ a ∈ Set.Ioo 0 1).card ≤ d
      · exact ⟨θ, hθ, hsmall, rfl⟩
      push Not at hsmall
      -- The fractional support `F` of `θ` has more than `d` elements.
      set F : Finset (Fin d → ℝ) := A.filter fun a ↦ θ a ∈ Set.Ioo 0 1 with hF
      have hFsub : F ⊆ A := Finset.filter_subset _ _
      have hFmem : ∀ a ∈ F, θ a ∈ Set.Ioo 0 1 :=
        fun a ha ↦ (Finset.mem_filter.mp ha).2
      -- `F` has `> d` vectors in `d` dimensions, so there is a nontrivial
      -- linear relation `∑ δ₀ a • a = 0` among them.
      obtain ⟨δ₀, hδ₀sum, a₁, ha₁F, hδa₁⟩ :=
        Module.exists_nontrivial_relation_of_finrank_lt_card
          (R := ℝ) (M := Fin d → ℝ) (t := F) (by
            rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
            exact hsmall)
      -- Extend `δ₀` by `0` outside `F` to `δ`.
      set δ : (Fin d → ℝ) → ℝ := fun a ↦ if a ∈ F then δ₀ a else 0 with hδ
      have hδ0 : ∀ a : Fin d → ℝ, a ∉ F → δ a = 0 := fun a ha ↦ by
        rw [hδ]; exact ite_eq_right ha
      have hδF : ∀ (a : Fin d → ℝ) (ha : a ∈ F), δ a = δ₀ a :=
        fun a ha ↦ by rw [hδ]; exact ite_eq_left ha
      have hδex : ∃ a ∈ F, δ a ≠ 0 :=
        ⟨a₁, ha₁F, by rw [hδF a₁ ha₁F]; exact hδa₁⟩
      have hδsum : ∑ a ∈ A, δ a • a = 0 := by
        have e : (∑ a ∈ A, δ a • a) = ∑ a ∈ F, δ a • a :=
          (Finset.sum_subset hFsub fun a _ haF ↦ by
            rw [hδ0 a haF, zero_smul]).symm
        rw [e]
        have e2 : (∑ a ∈ F, δ a • a) = ∑ a ∈ F, δ₀ a • a :=
          Finset.sum_congr rfl fun a ha ↦ by rw [hδF a ha]
        rw [e2]; exact hδ₀sum
      -- The largest admissible step before a coefficient leaves `[0,1]`.
      set bound : (Fin d → ℝ) → ℝ := fun a ↦
        if 0 < δ a then (1 - θ a) / δ a else θ a / (-δ a) with hbound
      have hboundpos : ∀ a ∈ F, δ a ≠ 0 → 0 < bound a := by
        intro a ha hδa
        have hθa := hFmem a ha
        simp only [hbound]
        rcases lt_or_gt_of_ne hδa with hneg | hpos
        · rw [ite_eq_right (not_lt_of_gt hneg)]
          exact div_pos hθa.1 (by linarith : (0 : ℝ) < -δ a)
        · rw [ite_eq_left hpos]
          exact div_pos (by linarith [hθa.2] : (0 : ℝ) < 1 - θ a) hpos
      set F' : Finset (Fin d → ℝ) := F.filter fun a ↦ δ a ≠ 0 with hF'
      have hF'ne : F'.Nonempty := by
        obtain ⟨a, ha, hδa⟩ := hδex
        exact ⟨a, Finset.mem_filter.mpr ⟨ha, hδa⟩⟩
      obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image F' bound hF'ne
      set t : ℝ := bound a₀ with ht
      have htpos : 0 < t := by
        rw [ht]; exact hboundpos a₀ (Finset.mem_filter.mp ha₀).1
          (Finset.mem_filter.mp ha₀).2
      set θ' : (Fin d → ℝ) → ℝ := fun a ↦ θ a + t * δ a with hθ'
      -- `θ'` stays in `[0,1]` on `A`.
      have hθ'Icc : ∀ a ∈ A, θ' a ∈ Set.Icc 0 1 := by
        intro a ha
        have hθa := Set.mem_Icc.mp (hθ a ha)
        simp only [hθ']
        by_cases haF : a ∈ F
        · by_cases hδa : δ a = 0
          · rw [hδa, mul_zero, add_zero]
            exact Set.mem_Icc.mpr hθa
          · have haF' : a ∈ F' := Finset.mem_filter.mpr ⟨haF, hδa⟩
            have hle : t ≤ bound a := hmin a haF'
            rcases lt_or_gt_of_ne hδa with hneg | hpos
            · -- `δ a < 0`: `t ≤ θ a / (-δ a)` gives `θ a + t·δ a ≥ 0`.
              have hb : bound a = θ a / (-δ a) := by
                simp only [hbound]; rw [ite_eq_right (not_lt_of_gt hneg)]
              have htδ : -θ a ≤ t * δ a := by
                have h := (le_div_iff₀ (by linarith : (0 : ℝ) < -δ a)).mp
                  (hb ▸ hle)
                linarith
              exact Set.mem_Icc.mpr ⟨by linarith,
                by have hnn : t * δ a ≤ 0 :=
                     mul_nonpos_of_nonneg_of_nonpos htpos.le hneg.le
                   linarith⟩
            · -- `δ a > 0`: `t ≤ (1 - θ a) / δ a` gives `θ a + t·δ a ≤ 1`.
              have hb : bound a = (1 - θ a) / δ a := by
                simp only [hbound]; rw [ite_eq_left hpos]
              have htδ : t * δ a ≤ 1 - θ a := by
                have h := (le_div_iff₀ hpos).mp (hb ▸ hle)
                linarith
              exact Set.mem_Icc.mpr
                ⟨by have hnn : 0 ≤ t * δ a :=
                      mul_nonneg htpos.le hpos.le
                    linarith, by linarith⟩
        · rw [hδ0 a haF, mul_zero, add_zero]
          exact Set.mem_Icc.mpr hθa
      -- `a₀` is pushed to the boundary: `θ' a₀ ∈ {0, 1}`.
      obtain ⟨ha₀F, hδa₀⟩ := Finset.mem_filter.mp ha₀
      have hθ'a₀ : θ' a₀ = 0 ∨ θ' a₀ = 1 := by
        rcases lt_or_gt_of_ne hδa₀ with hneg | hpos
        · left
          have hb : bound a₀ = θ a₀ / (-δ a₀) := by
            simp only [hbound]; rw [ite_eq_right (not_lt_of_gt hneg)]
          have hmul : t * δ a₀ = -θ a₀ := by
            rw [ht, hb]
            have hne : (-δ a₀) ≠ 0 := neg_ne_zero.mpr hδa₀
            calc (θ a₀ / (-δ a₀)) * δ a₀
                = -(θ a₀ / (-δ a₀) * (-δ a₀)) := by ring
              _ = -(θ a₀) := by rw [div_mul_cancel₀ _ hne]
              _ = -θ a₀ := rfl
          simp only [hθ']; rw [hmul]; ring
        · right
          have hb : bound a₀ = (1 - θ a₀) / δ a₀ := by
            simp only [hbound]; rw [ite_eq_left hpos]
          have hmul : t * δ a₀ = 1 - θ a₀ := by
            rw [ht, hb]; exact div_mul_cancel₀ _ hδa₀
          simp only [hθ']; rw [hmul]; ring
      -- The new fractional support is strictly contained in `F`.
      have hsub : (A.filter fun a ↦ θ' a ∈ Set.Ioo 0 1) ⊆ F := by
        intro a ha
        rw [Finset.mem_filter] at ha ⊢
        obtain ⟨haA, hIoo⟩ := ha
        refine ⟨haA, ?_⟩
        by_contra hnot
        have hδa : δ a = 0 :=
          hδ0 a (fun haF ↦ hnot (Finset.mem_filter.mp haF).2)
        simp only [hθ', hδa, mul_zero, add_zero] at hIoo
        exact hnot hIoo
      have ha₀F'' : a₀ ∉ A.filter fun a ↦ θ' a ∈ Set.Ioo 0 1 := by
        intro hmem
        have hIoo := Set.mem_Ioo.mp (Finset.mem_filter.mp hmem).2
        rcases hθ'a₀ with h | h <;> rw [h] at hIoo
        · exact absurd hIoo.1 (lt_irrefl 0)
        · exact absurd hIoo.2 (lt_irrefl 1)
      have hcardlt : (A.filter fun a ↦ θ' a ∈ Set.Ioo 0 1).card < F.card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset hsub]
        exact ⟨a₀, ha₀F, ha₀F''⟩
      -- The weighted sum is preserved.
      have hsumθ' : (∑ a ∈ A, θ' a • a) = ∑ a ∈ A, θ a • a := by
        have e : ∀ a ∈ A, θ' a • a = θ a • a + (t * δ a) • a :=
          fun a _ ↦ by rw [hθ']; exact add_smul _ _ _
        rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
        have h2 : (∑ a ∈ A, (t * δ a) • a) = t • ∑ a ∈ A, δ a • a := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun a _ ↦ mul_smul t (δ a) a
        rw [h2, hδsum, smul_zero, add_zero]
      -- Apply the induction hypothesis to `θ'`.
      obtain ⟨φ, hφIcc, hφcard, hφsum⟩ := ih θ' hθ'Icc (by omega)
      exact ⟨φ, hφIcc, hφcard, hφsum.trans hsumθ'⟩

/-- **The CFP zonotope rounding lemma** (a sharpening of Lemma 13 of
Pham–Zakharov, quoted there from CFP23): every point `z` of the zonotope
`𝒵_A` is within `d · wᵢ` of a subset sum of `A` in coordinate `i`, whenever
all `a ∈ A` satisfy `|aᵢ| ≤ wᵢ`.  (The paper only needs the weaker bound
`√(d|A|)·wᵢ`.) -/
theorem exists_subset_sum_sub_le {d : ℕ} {A : Finset (Fin d → ℝ)}
    {z : Fin d → ℝ} (hz : z ∈ zonotope A) {w : Fin d → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ a ∈ A, ∀ i, |a i| ≤ w i) :
    ∃ S : Finset (Fin d → ℝ), S ⊆ A ∧
      ∀ i, |(∑ a ∈ S, a) i - z i| ≤ d * w i := by
  classical
  obtain ⟨θ, hθ, rfl⟩ := hz
  obtain ⟨φ, hφIcc, hφcard, hφsum⟩ := exists_rounded_weights θ hθ
  set F := A.filter fun a ↦ φ a ∈ Set.Ioo 0 1 with hF
  set S := A.filter fun a ↦ φ a = 1 with hS
  -- Split `A` into `S` (coefficient `1`), `F` (fractional), `Z`
  -- (coefficient `0`).
  set Z := A.filter fun a ↦ φ a = 0 with hZ
  have hdec : ∀ a ∈ A, φ a = 1 ∨ φ a ∈ Set.Ioo 0 1 ∨ φ a = 0 := by
    intro a ha
    have hφa := Set.mem_Icc.mp (hφIcc a ha)
    rcases eq_or_lt_of_le hφa.2 with h1 | h1
    · exact Or.inl h1
    · rcases eq_or_lt_of_le hφa.1 with h0 | h0
      · exact Or.inr (Or.inr h0.symm)
      · exact Or.inr (Or.inl ⟨h0, h1⟩)
  have hpart : A = S ∪ F ∪ Z := by
    ext a
    simp only [hS, hF, hZ, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ha
      rcases hdec a ha with h | h | h
      · exact Or.inl (Or.inl ⟨ha, h⟩)
      · exact Or.inl (Or.inr ⟨ha, h⟩)
      · exact Or.inr ⟨ha, h⟩
    · rintro ((⟨ha, -⟩ | ⟨ha, -⟩) | ⟨ha, -⟩) <;> exact ha
  have hdj₁ : Disjoint S F := by
    rw [Finset.disjoint_left]
    rintro a hmemS hmemF
    have h1 := (Finset.mem_filter.mp hmemS).2
    have hIoo := (Finset.mem_filter.mp hmemF).2
    rw [h1] at hIoo
    exact absurd (Set.mem_Ioo.mp hIoo).2 (lt_irrefl 1)
  have hdj₂ : Disjoint (S ∪ F) Z := by
    rw [Finset.disjoint_left]
    rintro a ha hmemZ
    have h0 := (Finset.mem_filter.mp hmemZ).2
    rw [Finset.mem_union] at ha
    rcases ha with haS | haF
    · have h1 := (Finset.mem_filter.mp haS).2
      rw [h1] at h0; exact one_ne_zero h0
    · have hIoo := (Finset.mem_filter.mp haF).2
      exact (Set.mem_Ioo.mp hIoo).1.ne' h0
  have hsum_split : (∑ a ∈ A, φ a • a)
      = (∑ a ∈ S, a) + ∑ a ∈ F, φ a • a := by
    rw [hpart, Finset.sum_union hdj₂, Finset.sum_union hdj₁]
    have hS' : (∑ a ∈ S, φ a • a) = ∑ a ∈ S, a :=
      Finset.sum_congr rfl fun a ha ↦ by
        rw [(Finset.mem_filter.mp ha).2, one_smul]
    have hZ0 : (∑ a ∈ Z, φ a • a) = 0 :=
      Finset.sum_eq_zero fun a ha ↦ by
        rw [(Finset.mem_filter.mp ha).2, zero_smul]
    rw [hS', hZ0, add_zero]
  refine ⟨S, Finset.filter_subset _ _, fun i ↦ ?_⟩
  -- Goal: |(∑ a ∈ S, a) i - (∑ a ∈ A, θ a • a) i| ≤ d * w i
  have hzi : (∑ a ∈ A, θ a • a) i - (∑ a ∈ S, a) i
      = ∑ a ∈ F, φ a * a i := by
    have h1 : (∑ a ∈ A, θ a • a) i = ∑ a ∈ A, φ a * a i := by
      rw [congrFun hφsum.symm i, Finset.sum_apply]
      exact Finset.sum_congr rfl fun a _ ↦ by
        rw [Pi.smul_apply, smul_eq_mul]
    have hφA : ∑ a ∈ A, φ a * a i
        = ∑ a ∈ S, a i + ∑ a ∈ F, φ a * a i := by
      rw [hpart, Finset.sum_union hdj₂, Finset.sum_union hdj₁]
      have hS' : ∑ a ∈ S, φ a * a i = ∑ a ∈ S, a i :=
        Finset.sum_congr rfl fun a ha ↦ by
          rw [(Finset.mem_filter.mp ha).2, one_mul]
      have hZ0 : ∑ a ∈ Z, φ a * a i = 0 :=
        Finset.sum_eq_zero fun a ha ↦ by
          rw [(Finset.mem_filter.mp ha).2, zero_mul]
      rw [hS', hZ0, add_zero]
    rw [h1, Finset.sum_apply, hφA]; ring
  have hbound : |(∑ a ∈ A, θ a • a) i - (∑ a ∈ S, a) i|
      ≤ ∑ a ∈ F, w i := by
    rw [hzi]
    calc |∑ a ∈ F, φ a * a i| ≤ ∑ a ∈ F, |φ a * a i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ F, w i := by
          apply Finset.sum_le_sum
          intro a ha
          have hφa : |φ a| ≤ 1 := by
            have h := Set.mem_Icc.mp
              (hφIcc a ((Finset.mem_filter.mp ha).1))
            rw [abs_le]
            exact ⟨by linarith [h.1], h.2⟩
          have haA : a ∈ A := (Finset.mem_filter.mp ha).1
          calc |φ a * a i| = |φ a| * |a i| := abs_mul _ _
            _ ≤ 1 * w i := mul_le_mul hφa (hw a haA i)
                (abs_nonneg _) zero_le_one
            _ = w i := one_mul _
  calc |(∑ a ∈ S, a) i - (∑ a ∈ A, θ a • a) i|
      = |(∑ a ∈ A, θ a • a) i - (∑ a ∈ S, a) i| := abs_sub_comm _ _
    _ ≤ ∑ a ∈ F, w i := hbound
    _ = F.card * w i := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ d * w i := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hφcard) (hw0 i)

/-- Integer-valued version: for `A ⊆ ℤ^d` and a point `z` of the zonotope of
the embedded `A`, some `S ⊆ A` has `Σ_{S} a` within `d·wᵢ` of `z` in every
coordinate. -/
theorem exists_subset_sum_sub_le_int {d : ℕ} {A : Finset (Fin d → ℤ)}
    {z : Fin d → ℤ}
    (hz : (fun i ↦ (z i : ℝ)) ∈ zonotope (A.image fun x i ↦ (x i : ℝ)))
    {w : Fin d → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ a ∈ A, ∀ i, |(a i : ℝ)| ≤ w i) :
    ∃ S : Finset (Fin d → ℤ), S ⊆ A ∧
      ∀ i, |((∑ a ∈ S, a) i : ℝ) - z i| ≤ d * w i := by
  classical
  obtain ⟨S', hS', hSw⟩ := exists_subset_sum_sub_le hz hw0 (fun b hb ↦ by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hw a ha)
  obtain ⟨S, hSA, hSeq⟩ := Finset.subset_image_iff.mp hS'
  refine ⟨S, hSA, fun i ↦ ?_⟩
  have hsum : (∑ b ∈ S', b) i = ((∑ a ∈ S, a) i : ℝ) := by
    rw [← hSeq]
    have e1 : (∑ b ∈ S.image (fun x i ↦ (x i : ℝ)), b) i
        = ∑ a ∈ S, ((a i : ℤ) : ℝ) := by
      rw [Finset.sum_apply,
        Finset.sum_image (fun x _ y _ h ↦
          funext fun j ↦ Int.cast_injective (congrFun h j))]
    rw [e1, Finset.sum_apply]
    exact (Int.cast_sum S (fun a ↦ a i)).symm
  rw [← hsum]
  exact hSw i

end Zonotope

end Nonaveraging
