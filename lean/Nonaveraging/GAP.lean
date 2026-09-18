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

open Finset

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
        (d' : ℝ) ≤ d ∧
        (Â ∪ {0}) ⊆ P.toFinset ∧
        ∃ A' ⊆ Â, A'.card ≤ s ∧
          ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ c * s ∧
            ∃ t : Fin ℓ → ℤ,
              ((k • P).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
              (k • P).Proper := by
  sorry

/-- **Corollary 5**: Theorem 3 at `s = m / log² m`; `P` may be taken symmetric
and `csP` proper. -/
theorem cfp_structure_cor (ℓ : ℕ) {β : ℝ} (hβ : 1 < β) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ (A : Finset (Fin ℓ → ℤ)) (B : GAP.Box ℓ),
      A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
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
  sorry

end Nonaveraging
