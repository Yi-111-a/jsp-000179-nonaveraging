import Nonaveraging.ConvexPosition

/-!
# Subset-sum dimension, irreducibility, and the intersection theorem

Paper references (arXiv:2410.14624v2, §3.1–3.2):

* `SubSumWitness` — the data supplied by the structure theorem (Corollary 5):
  `Ah ⊆ A`, `A' ⊆ Ah`, a `d'`-dimensional GAP `P ⊇ Ah ∪ {0}`, and a homogeneous
  translate of the proper GAP `kP` inside `Σ(A')`.  The *subset-sum
  dimension* `d(A)` of an `(ℓ,β)`-set is a `d'` for which such a witness
  exists.
* `GAP.imageCoeff` — the embedded image `ϕ_P(Ah) ⊆ ℤ^{d'}` under the
  coefficient map of `P`.
* `Irreducible` — the `(δ,γ)`-irreducibility of Definition 9.
* **Lemma 10** (`irreduciblization`) — every non-averaging `(ℓ,β)`-set can be
  replaced by a large `(δ,γ)`-irreducible non-averaging subset.
* **Theorem 4** (`embedded_in_mu_convex_position`) — an irreducible
  non-averaging set whose embedded image is not in μ-convex position
  produces a nontrivial relation `Σ(At₁ − a) = Σ(a − At₂)`.
-/

open Finset MeasureTheory

namespace Nonaveraging

namespace GAP

variable {ℓ d : ℕ} (P : GAP ℓ d)

/-- The identification map `φ_P`: the coefficient tuple of a point of `P`,
chosen via `Classical.choose`. -/
noncomputable def coeffOf (x : Fin ℓ → ℤ) (hx : x ∈ P.toFinset) : Fin d → ℕ :=
  Classical.choose (Finset.mem_image.mp hx)

theorem coeffOf_spec (x : Fin ℓ → ℤ) (hx : x ∈ P.toFinset) :
    P.eval (P.coeffOf x hx) = x :=
  (Classical.choose_spec (Finset.mem_image.mp hx)).2

theorem coeffOf_mem (x : Fin ℓ → ℤ) (hx : x ∈ P.toFinset) :
    P.coeffOf x hx ∈ P.coeffs :=
  (Classical.choose_spec (Finset.mem_image.mp hx)).1

theorem coeffOf_injective {x y : Fin ℓ → ℤ} (hx : x ∈ P.toFinset)
    (hy : y ∈ P.toFinset) (h : P.coeffOf x hx = P.coeffOf y hy) : x = y := by
  have hx' := P.coeffOf_spec x hx
  have hy' := P.coeffOf_spec y hy
  rw [← hx', ← hy', h]

/-- The embedded image `ϕ_P(A)` of a set of points of `P`, as a finset of
`ℤ^d`. -/
noncomputable def imageCoeff (A : Finset (Fin ℓ → ℤ)) (hsub : A ⊆ P.toFinset) :
    Finset (Fin d → ℤ) :=
  A.attach.image fun x ↦ fun i ↦ (P.coeffOf x.1 (hsub x.2) i : ℤ)

theorem card_imageCoeff (A : Finset (Fin ℓ → ℤ)) (hsub : A ⊆ P.toFinset) :
    (P.imageCoeff A hsub).card = A.card := by
  unfold imageCoeff
  have hinj : Function.Injective
      (fun x : {x // x ∈ A} ↦ fun i ↦ (P.coeffOf x.1 (hsub x.2) i : ℤ)) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have hxy : P.coeffOf x (hsub hx) = P.coeffOf y (hsub hy) := by
      funext i
      have h' : (P.coeffOf x (hsub hx) i : ℤ) = (P.coeffOf y (hsub hy) i : ℤ) :=
        congrFun h i
      exact_mod_cast h'
    exact Subtype.ext (P.coeffOf_injective (hsub hx) (hsub hy) hxy)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]

end GAP

variable {ℓ : ℕ}

/-- The witness data of the structure theorem applied to `A` with subset-sum
dimension `d'`: `Ah ⊆ A`, `A' ⊆ Ah`, a `d'`-dimensional `P ⊇ Ah ∪ {0}`, and a
homogeneous translate of the proper `kP` contained in `Σ(A')`. -/
structure SubSumWitness {ℓ : ℕ} (A : Finset (Fin ℓ → ℤ)) (β : ℝ) (d' : ℕ) where
  c : ℝ
  s : ℝ
  Ah : Finset (Fin ℓ → ℤ)
  A' : Finset (Fin ℓ → ℤ)
  P : GAP ℓ d'
  k : ℕ
  t : Fin ℓ → ℤ
  cpos : 0 < c
  kpos : 0 < k
  hk : (k : ℝ) ≤ c * s
  hAh : Ah ⊆ A
  hA' : A' ⊆ Ah
  hA'card : (A'.card : ℝ) ≤ s
  hAhcard : (A.card : ℝ) - c⁻¹ * s * Real.log A.card ≤ (Ah.card : ℝ)
  hsub : (Ah ∪ {0}) ⊆ P.toFinset
  htranslate : ((k • P).translate t).toFinset ⊆ GAP.subsetSumsL A'
  hproper : (k • P).Proper

/-- `A` *has subset-sum dimension* `d'` (with parameter `β`). -/
def HasSubSumDim (A : Finset (Fin ℓ → ℤ)) (β : ℝ) (d' : ℕ) : Prop :=
  GAP.IsLBSet A β ∧ Nonempty (SubSumWitness A β d')

namespace SubSumWitness

variable {d : ℕ} {β : ℝ} {A : Finset (Fin ℓ → ℤ)} (W : SubSumWitness A β d)

/-- The embedded image `ϕ_P(Ah) ⊆ ℤ^d`. -/
noncomputable def imageAh : Finset (Fin d → ℤ) :=
  W.P.imageCoeff W.Ah (fun _ ha ↦ W.hsub (Finset.mem_union_left _ ha))

/-- The embedded box `ϕ_P(P) ⊆ ℤ^d`. -/
noncomputable def imageP : Finset (Fin d → ℤ) :=
  W.P.imageCoeff W.P.toFinset (Subset.refl _)

end SubSumWitness

/-- `(δ,γ)`-irreducibility (Definition 9): for every subset `A'` of `ϕ_P(Ah)`
of size `≥ δ|A|` and every `x ∈ ϕ_P(P)`, every structure witness for
`A' − x` has dimension `d` (that of `A`) and GAP size `≥ γ|P(A)|`. -/
def Irreducible {d : ℕ} {β : ℝ} {A : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness A β d) (β' δ γ : ℝ) : Prop :=
  ∀ (A' : Finset (Fin d → ℤ)) (x : Fin d → ℤ),
    A' ⊆ W.imageAh → (δ : ℝ) * A.card ≤ A'.card → x ∈ W.imageP →
    ∀ (d'' : ℕ) (W' : SubSumWitness (A'.image (· - x)) β' d''),
      d'' = d ∧ (γ : ℝ) * W.P.toFinset.card ≤ W'.P.toFinset.card

/-- **Lemma 10 (irreduciblization)**.  A non-averaging `A ⊆ B ⊆ ℤ^ℓ` with
`|B| ≤ |A|^β` admits, for `ε < 1/3`, `γ ≤ δ^K`, `K ≥ C_{β,ε}` and
`γ ≥ |A|^{-1/3}`, a non-averaging `(δ,γ)`-irreducible `At` with
`|At| ≥ |A|^{1−ε}` whose GAP `Pt` satisfies the size bounds of Lemma 10
(the two `|Pt|` cases are folded into the witness). -/
theorem irreduciblization {d : ℕ} {β ε δ γ : ℝ} (hε : 0 < ε) (hε3 : ε < 1 / 3)
    {A : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ}
    (hA : NonAveraging A) (hsub : A ⊆ B.toFinset)
    (hB : (B.card : ℝ) ≤ (A.card : ℝ) ^ β) :
    ∃ (At : Finset (Fin ℓ → ℤ)) (dt : ℕ) (Wt : SubSumWitness At β dt) (β' : ℝ),
      NonAveraging At ∧ (A.card : ℝ) ^ (1 - ε) ≤ (At.card : ℝ) ∧
      Irreducible Wt β' δ γ := by
  sorry

/-- **Theorem 4** (contrapositive form used in §4).  If `A ⊆ B ⊆ ℤ^ℓ` is
non-averaging, `(δ,γ)`-irreducible via witness `W`, and `|A|` is sufficiently
large, then the embedded image `ϕ_P(Ah)` (viewed in `ℝ^d`) is in `μ`-convex
position. -/
theorem embedded_in_mu_convex_position {d : ℕ} {β β' δ γ μ : ℝ}
    {A Ah : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ} (W : SubSumWitness A β d)
    (hA : NonAveraging A) (hsub : A ⊆ B.toFinset)
    (hB : (B.card : ℝ) ≤ (A.card : ℝ) ^ β)
    (hirr : Irreducible W β' δ γ) :
    ∃ N : ℕ, N ≤ A.card →
      InDeltaConvexPosition
        (W.imageAh.image fun x i ↦ ((x i : ℤ) : ℝ)) μ := by
  sorry

end Nonaveraging
