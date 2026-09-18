import Nonaveraging.GAP

/-!
# Sets in δ-convex position and the density-increment lemma

Paper references (arXiv:2410.14624v2, §2):

* `InDeltaConvexPosition` — `A ⊂ ℝ^d` is in δ-convex position if every point
  of `A` lies in a half-space containing at most `δ|A|` points of `A`.
* **Lemma 1** (`density_increment`) — given `A ⊂ Ω` in δ-convex position,
  some smaller convex `Ω' ⊂ Ω` has a substantially denser intersection:
  `Vol(Ω') ≤ η·Vol(Ω)` and `|A ∩ Ω'| ≥ η^{(d−1)/(d+1)+ε}|A|` for some
  `η ∈ [δ, δ^τ]`.
* **Lemma 2** (`convex_linear_approx`) — a bounded convex function on a box in
  `ℝ^{d−1}` is well-approximated by a linear function on one of many
  prescribed sub-cubes.
-/

open Finset MeasureTheory

attribute [local instance] Classical.propDecidable

namespace Nonaveraging

variable {d : ℕ}

/-- The standard dot product on `Fin d → ℝ`. -/
def dot (u x : Fin d → ℝ) : ℝ := ∑ i, u i * x i

/-- `A ⊂ ℝ^d` is in *δ-convex position* if for every `a ∈ A` some half-space
containing `a` contains at most `δ|A|` points of `A`. -/
def InDeltaConvexPosition (A : Finset (Fin d → ℝ)) (δ : ℝ) : Prop :=
  ∀ a ∈ A, ∃ u : Fin d → ℝ, ∃ t : ℝ,
    t ≤ dot u a ∧
    ((A.filter fun x ↦ t ≤ dot u x).card : ℝ) ≤ δ * A.card

/-- The open box `(−c, 1+c)^k` in `ℝ^k`. -/
def openBox {k : ℕ} (c : ℝ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun _ ↦ Set.Ioo (-c) (1 + c)

/-- The sub-cube `v/m + [0,1/m]^k` for `v : Fin k → ℕ`. -/
def cubeOf {k : ℕ} (m : ℕ) (v : Fin k → ℕ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun i ↦ Set.Icc ((v i : ℝ) / m) (((v i : ℝ) + 1) / m)

/-- **Lemma 2**: a convex `H : (−c, 1+c)^{d−1} → [0,1]` has, for any
`I ⊆ [m]^{d−1}`, a cube `Q_v` with `v ∈ I` on which `H` is approximated to
within `4d⁴m^{d−3}/(c|I|)` by an affine linear function. -/
theorem convex_linear_approx (m d : ℕ) (hm : 0 < m) (hd : 0 < d) {c : ℝ}
    (hc : 2 * (d : ℝ) / m < c) (H : (Fin (d - 1) → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (openBox c) H)
    (hbdd : ∀ x ∈ openBox c, H x ∈ Set.Icc 0 1)
    (I : Finset (Fin (d - 1) → ℕ)) (hI : ∀ v ∈ I, ∀ i, v i < m)
    (hIne : I.Nonempty) :
    ∃ v ∈ I, ∃ b : ℝ, ∃ l : Fin (d - 1) → ℝ,
      ∀ x ∈ cubeOf m v,
        |H x - (b + dot l x)| ≤
          4 * (d : ℝ) ^ 4 * (m : ℝ) ^ ((d : ℤ) - 3) / (c * I.card) := by
  sorry

/-- **Lemma 1 (density increment)**.  For `d ≥ 1` and `ε > 0` there exist
`τ ∈ (0,1)` and `δ₀ > 0` such that for every `δ ∈ (0, δ₀)` the following
holds.  Let `Ω ⊂ ℝ^d` be a convex body with nonempty interior and let
`A ⊂ Ω` be a finite set in δ-convex position, sufficiently large in `δ`.
Then for some `η ∈ [δ, δ^τ]` there is a convex `Ω' ⊂ Ω` with
`Vol(Ω') ≤ η·Vol(Ω)` and `|A ∩ Ω'| ≥ η^{(d−1)/(d+1)+ε}|A|`. -/
theorem density_increment (d : ℕ) (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ M : ℕ, ∀ (Ω : Set (Fin d → ℝ)) (A : Finset (Fin d → ℝ)),
        Convex ℝ Ω → (interior Ω).Nonempty →
        (∀ a ∈ A, (a : Fin d → ℝ) ∈ Ω) →
        InDeltaConvexPosition A δ → M ≤ A.card →
        ∃ η : ℝ, δ ≤ η ∧ η ≤ δ ^ τ ∧ ∃ Ω' : Set (Fin d → ℝ),
          Convex ℝ Ω' ∧ Ω' ⊆ Ω ∧
          volume Ω' ≤ ENNReal.ofReal η * volume Ω ∧
          η ^ ((d - 1 : ℝ) / (d + 1) + ε) * A.card ≤
            ((A.filter fun a ↦ (a : Fin d → ℝ) ∈ Ω').card : ℝ) := by
  sorry

end Nonaveraging
