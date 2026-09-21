import Nonaveraging.ConvexPosition
import Nonaveraging.GeoNumbers

/-!
# Subset-sum dimension, irreducibility, and the intersection theorem

Paper references (arXiv:2410.14624v2, §3.1–3.2):

* `SubSumWitness` — the data supplied by the structure theorem applied with
  the choice `s = s(A) = |A| / log² |A|` (Corollary 5): `Ah ⊆ A`,
  `|Ah| ≥ |A| − c⁻¹·|A|/log|A|`, `A' ⊆ Ah`, `|A'| ≤ s(A)`, a `d'`-dimensional
  GAP `P ⊇ Ah ∪ {0}`, and a homogeneous translate of the proper `kP` inside
  `Σ(A')` with `k ≤ c·s(A)`.  The constant `c` is a *parameter* of the
  structure (the Corollary-5 constant), not a per-witness choice.
* `GAP.ptCoeffImage` — the embedded image `ϕ_P(Ah) ⊆ ℤ^{d'}` under the
  coefficient map of `P`.
* `SubSumDim` — the subset-sum dimension `d(A)`: the *least* `d'` for which a
  `d'`-dimensional witness exists.
* `DerivedFrom` — reachability of a set from `A` by the down/up/shrink moves
  of Lemma 10.
* `Irreducible` — the `(δ,γ)`-irreducibility of Definition 9.
* **Lemma 10** (`irreduciblization`) — every non-averaging `(ℓ,β)`-set can be
  replaced by a large `(δ,γ)`-irreducible non-averaging subset `Ã ⊆ ℤ^{d̃}`
  (in a possibly different ambient dimension), with the `|P̃|` bounds of
  Lemma 10.
* **Theorem 4** (`embedded_in_mu_convex_position`) — an irreducible
  non-averaging set whose embedded image is not in μ-convex position
  produces a nontrivial relation `Σ(At₁ − a) = Σ(a − At₂)`; contrapositively,
  the embedded image is in μ-convex position once `|A|` is large.
-/

open Finset MeasureTheory

namespace Nonaveraging

namespace GAP

variable {ℓ d : ℕ} (P : GAP ℓ d)

/-- The identification map `φ_P`: the coefficient tuple of a point of `P`,
chosen via `Classical.choose`. -/
noncomputable def ptCoeff (x : Fin ℓ → ℤ) (hx : x ∈ P.toFinset) : Fin d → ℕ :=
  Classical.choose (Finset.mem_image.mp hx)

theorem eval_ptCoeff (x : Fin ℓ → ℤ) (hx : x ∈ P.toFinset) :
    P.eval (P.ptCoeff x hx) = x :=
  (Classical.choose_spec (Finset.mem_image.mp hx)).2

theorem ptCoeff_mem (x : Fin ℓ → ℤ) (hx : x ∈ P.toFinset) :
    P.ptCoeff x hx ∈ P.coeffs :=
  (Classical.choose_spec (Finset.mem_image.mp hx)).1

theorem ptCoeff_injective {x y : Fin ℓ → ℤ} (hx : x ∈ P.toFinset)
    (hy : y ∈ P.toFinset) (h : P.ptCoeff x hx = P.ptCoeff y hy) : x = y := by
  have hx' := P.eval_ptCoeff x hx
  have hy' := P.eval_ptCoeff y hy
  rw [← hx', ← hy', h]

/-- The embedded image `ϕ_P(A)` of a set of points of `P`, as a finset of
`ℤ^d`. -/
noncomputable def ptCoeffImage (A : Finset (Fin ℓ → ℤ)) (hsub : A ⊆ P.toFinset) :
    Finset (Fin d → ℤ) :=
  A.attach.image fun x ↦ fun i ↦ (P.ptCoeff x.1 (hsub x.2) i : ℤ)

theorem card_ptCoeffImage (A : Finset (Fin ℓ → ℤ)) (hsub : A ⊆ P.toFinset) :
    (P.ptCoeffImage A hsub).card = A.card := by
  unfold ptCoeffImage
  have hinj : Function.Injective
      (fun x : {x // x ∈ A} ↦ fun i ↦ (P.ptCoeff x.1 (hsub x.2) i : ℤ)) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have hxy : P.ptCoeff x (hsub hx) = P.ptCoeff y (hsub hy) := by
      funext i
      have h' : (P.ptCoeff x (hsub hx) i : ℤ) = (P.ptCoeff y (hsub hy) i : ℤ) :=
        congrFun h i
      exact_mod_cast h'
    exact Subtype.ext (P.ptCoeff_injective (hsub hx) (hsub hy) hxy)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]

/-- The embedded image of a non-averaging set is non-averaging: a relation
`|S| • b = Σ S` among coefficient vectors evaluates, via `P.eval`, to the
same relation `|S| • a = Σ S'` among the corresponding points of `A`.
This is the mechanism by which the moves of Lemma 10 preserve
non-averaging. -/
theorem nonAveraging_ptCoeffImage {A : Finset (Fin ℓ → ℤ)}
    (hsub : A ⊆ P.toFinset) (hA : NonAveraging A) :
    NonAveraging (P.ptCoeffImage A hsub) := by
  classical
  intro b hb T hT hTne hsum
  -- `b` is the coefficient vector of some `a ∈ A`.
  obtain ⟨⟨a, ha⟩, -, rfl⟩ := Finset.mem_image.mp hb
  -- Pull `T` back to a finset `T''` of `{x // x ∈ A}`.
  have hTsub : T ⊆ A.attach.image
      (fun x : {x // x ∈ A} ↦ fun i ↦ (P.ptCoeff x.1 (hsub x.2) i : ℤ)) :=
    hT.trans (Finset.erase_subset _ _)
  obtain ⟨T'', -, hT''eq⟩ := Finset.subset_image_iff.mp hTsub
  -- The coefficient map is injective on `A`.
  have hinj : ∀ x y : {x // x ∈ A},
      (fun i ↦ (P.ptCoeff x.1 (hsub x.2) i : ℤ)) =
        (fun i ↦ (P.ptCoeff y.1 (hsub y.2) i : ℤ)) → x = y := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have hxy : P.ptCoeff x (hsub hx) = P.ptCoeff y (hsub hy) := by
      funext i
      have h' : (P.ptCoeff x (hsub hx) i : ℤ)
          = (P.ptCoeff y (hsub hy) i : ℤ) := congrFun h i
      exact_mod_cast h'
    exact Subtype.ext (P.ptCoeff_injective (hsub hx) (hsub hy) hxy)
  have hcard : T.card = T''.card := by
    rw [← hT''eq, Finset.card_image_of_injective _ hinj]
  -- The underlying subset `S' ⊆ A`.
  set S' := T''.image Subtype.val with hS'def
  have hS'A : S' ⊆ A := by
    intro y hy
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hy
    exact z.2
  have hS'card : S'.card = T''.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hS'ne : S'.Nonempty := by
    obtain ⟨t, ht⟩ := hTne
    rw [← hT''eq] at ht
    obtain ⟨z, hz, -⟩ := Finset.mem_image.mp ht
    exact ⟨z.1, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  have hS'erase : S' ⊆ A.erase a := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_erase]
    refine ⟨?_, z.2⟩
    intro hza
    -- then `⟨a, ha⟩ ∈ T''`, so `b ∈ T ⊆ image.erase b`: contradiction.
    have hzT'' : (⟨a, ha⟩ : {x // x ∈ A}) ∈ T'' := by
      have hz'a : (⟨a, ha⟩ : {x // x ∈ A}) = z := Subtype.ext hza.symm
      rw [hz'a]; exact hz
    have hmem : (fun i ↦ (P.ptCoeff a (hsub ha) i : ℤ)) ∈ T := by
      rw [← hT''eq]
      exact Finset.mem_image.mpr ⟨⟨a, ha⟩, hzT'', rfl⟩
    exact (Finset.mem_erase.mp (hT hmem)).1 rfl
  -- The coefficientwise relation, evaluated coordinatewise.
  have hcoord : ∀ i : Fin d,
      T.card • ((P.ptCoeff a (hsub ha) i : ℤ)) = ∑ t ∈ T, t i := by
    intro i
    have h1 := congrFun hsum i
    rw [Finset.sum_apply] at h1
    exact h1
  have htsum : ∀ i : Fin d, ∑ t ∈ T, t i
      = ∑ z ∈ T'', ((P.ptCoeff z.1 (hsub z.2) i : ℤ)) := by
    intro i
    rw [← hT''eq, Finset.sum_image (fun x _ y _ h ↦ hinj x y h)]
  have hsumz : ∀ i : Fin d, (∑ z ∈ T'', (P.ptCoeff z.1 (hsub z.2) i : ℤ))
      = T.card • (P.ptCoeff a (hsub ha) i : ℤ) := by
    intro i
    rw [← htsum i, ← hcoord i]
  -- Evaluating coefficient vectors gives `Σ_{z ∈ T''} z.1 = |T''| • a`.
  have hzev : ∀ z : {x // x ∈ A},
      z.1 = P.eval (P.ptCoeff z.1 (hsub z.2)) :=
    fun z ↦ (P.eval_ptCoeff z.1 (hsub z.2)).symm
  have key : (∑ z ∈ T'', z.1) = T''.card • a := by
    funext j
    rw [Finset.sum_apply]
    have hzj : ∀ z : {x // x ∈ A}, z.1 j
        = P.base j + ∑ i, (P.ptCoeff z.1 (hsub z.2) i : ℤ) * P.step i j := by
      intro z
      conv_lhs => rw [hzev z]
      show (P.base + ∑ i, (P.ptCoeff z.1 (hsub z.2) i : ℤ) • P.step i) j = _
      rw [Pi.add_apply, Finset.sum_apply]
      rfl
    calc ∑ z ∈ T'', z.1 j
        = ∑ z ∈ T'', (P.base j + ∑ i,
            (P.ptCoeff z.1 (hsub z.2) i : ℤ) * P.step i j) :=
          Finset.sum_congr rfl fun z _ ↦ hzj z
      _ = (∑ z ∈ T'', P.base j) + ∑ z ∈ T'', ∑ i,
            (P.ptCoeff z.1 (hsub z.2) i : ℤ) * P.step i j :=
          Finset.sum_add_distrib
      _ = T''.card • P.base j + ∑ i, ∑ z ∈ T'',
            (P.ptCoeff z.1 (hsub z.2) i : ℤ) * P.step i j := by
          rw [Finset.sum_const, Finset.sum_comm]
      _ = T''.card • P.base j + ∑ i,
            (∑ z ∈ T'', (P.ptCoeff z.1 (hsub z.2) i : ℤ)) * P.step i j := by
          congr 1
          exact Finset.sum_congr rfl fun i _ ↦ (Finset.sum_mul _ _ _).symm
      _ = T''.card • P.base j + ∑ i,
            (T.card • (P.ptCoeff a (hsub ha) i : ℤ)) * P.step i j := by
          congr 1
          exact Finset.sum_congr rfl fun i _ ↦
            congrArg (· * P.step i j) (hsumz i)
      _ = (T''.card : ℤ) * (P.base j + ∑ i,
            (P.ptCoeff a (hsub ha) i : ℤ) * P.step i j) := by
          rw [hcard]
          simp only [nsmul_eq_mul]
          rw [mul_add, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ ↦ mul_assoc _ _ _
      _ = (T''.card : ℤ) * a j :=
          congrArg ((T''.card : ℤ) * ·) (hzj ⟨a, ha⟩).symm
      _ = (T''.card • a) j := by rw [Pi.smul_apply, nsmul_eq_mul]
  have hsumS' : S'.sum id = S'.card • a := by
    rw [hS'def, Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.sum_image (fun x _ y _ h ↦ Subtype.val_injective h)]
    change (∑ z ∈ T'', z.1) = T''.card • a
    exact key
  exact hA a ha S' hS'erase hS'ne hsumS'.symm

end GAP

variable {ℓ : ℕ}

/-- Translating a non-averaging set preserves non-averaging (the shift step
of the moves in Lemma 10). -/
theorem NonAveraging.translate {α : Type*} [DecidableEq α] [AddCommGroup α]
    {A : Finset α} (hA : NonAveraging A) (t : α) :
    NonAveraging (A.image (· + t)) := by
  classical
  intro b hb S hS hSne hsum
  rw [Finset.mem_image] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have hsub : S ⊆ A.image (· + t) := hS.trans (Finset.erase_subset _ _)
  obtain ⟨S', hS'A, hS'eq⟩ := Finset.subset_image_iff.mp hsub
  have hinj : Function.Injective (· + t) := fun x y h ↦
    add_right_cancel_iff.mp h
  have hcard : S.card = S'.card := by
    rw [← hS'eq, Finset.card_image_of_injective _ hinj]
  have hsumS : S.sum id = S'.sum id + S'.card • t := by
    rw [← hS'eq, Finset.sum_image (fun x _ y _ h ↦ hinj h)]
    simp only [id_eq]
    rw [Finset.sum_add_distrib, Finset.sum_const]
  rw [hcard, hsumS, smul_add] at hsum
  have key : S'.card • a = S'.sum id := add_right_cancel_iff.mp hsum
  have hS'erase : S' ⊆ A.erase a := by
    intro y hy
    rw [Finset.mem_erase]
    have hym : y + t ∈ S := by
      rw [← hS'eq]
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have h2 := Finset.mem_erase.mp (hS hym)
    exact ⟨fun h ↦ h2.1 (congrArg (· + t) h), hS'A hy⟩
  have hS'ne : S'.Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    rw [← hS'eq] at hs
    obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hs
    exact ⟨y, hy⟩
  exact hA a ha S' hS'erase hS'ne key

/-- The witness data of the structure theorem applied to `A` with the
Corollary-5 choice `s = s(A) = |A| / log² |A|` and constant `c` (a parameter
of the structure, not a per-witness choice): `Ah ⊆ A` with
`|Ah| ≥ |A| − c⁻¹·|A|/log|A|`, `A' ⊆ Ah` with `|A'| ≤ s(A)`, a
`d'`-dimensional GAP `P ⊇ Ah ∪ {0}`, and a homogeneous translate of the
proper `kP` contained in `Σ(A')` with `k ≤ c·s(A)`. -/
structure SubSumWitness {ℓ : ℕ} (A : Finset (Fin ℓ → ℤ)) (c : ℝ) (d' : ℕ) where
  Ah : Finset (Fin ℓ → ℤ)
  A' : Finset (Fin ℓ → ℤ)
  P : GAP ℓ d'
  k : ℕ
  t : Fin ℓ → ℤ
  cpos : 0 < c
  kpos : 0 < k
  hk : (k : ℝ) ≤ c * ((A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2)
  hAh : Ah ⊆ A
  hA' : A' ⊆ Ah
  hA'card : (A'.card : ℝ) ≤ (A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2
  hAhcard : (A.card : ℝ) - c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ)
      ≤ (Ah.card : ℝ)
  hsub : (Ah ∪ {0}) ⊆ P.toFinset
  htranslate : ((k • P).translate t).toFinset ⊆ GAP.subsetSumsL A'
  hproper : (k • P).Proper

/-- `A` *has subset-sum dimension* `d'` (as an `(ℓ,β)`-set, with
Corollary-5 constant `c`). -/
def HasSubSumDim (A : Finset (Fin ℓ → ℤ)) (β c : ℝ) (d' : ℕ) : Prop :=
  GAP.IsLBSet A β ∧ Nonempty (SubSumWitness A c d')

namespace SubSumWitness

variable {d : ℕ} {c : ℝ} {A : Finset (Fin ℓ → ℤ)} (W : SubSumWitness A c d)

/-- The embedded image `ϕ_P(Ah) ⊆ ℤ^d`. -/
noncomputable def imageAh : Finset (Fin d → ℤ) :=
  W.P.ptCoeffImage W.Ah (fun _ ha ↦ W.hsub (Finset.mem_union_left _ ha))

/-- The embedded box `ϕ_P(P) ⊆ ℤ^d`. -/
noncomputable def imageP : Finset (Fin d → ℤ) :=
  W.P.ptCoeffImage W.P.toFinset (Subset.refl _)

end SubSumWitness

/-- The *subset-sum dimension* `d(A)` of `A` (with Corollary-5 constant
`c`): the least `d'` for which a `d'`-dimensional structure witness exists.
It is `0` (a junk value) when no witness exists; applications only use
`(ℓ,β)`-sets, for which Corollary 5 supplies witnesses. -/
noncomputable def SubSumDim (A : Finset (Fin ℓ → ℤ)) (c : ℝ) : ℕ :=
  sInf {d' | Nonempty (SubSumWitness A c d')}

/-- Any witnessed dimension bounds `d(A)` from above. -/
theorem subSumDim_le {A : Finset (Fin ℓ → ℤ)} {c : ℝ} {d' : ℕ}
    (h : Nonempty (SubSumWitness A c d')) : SubSumDim A c ≤ d' :=
  Nat.sInf_le h

/-- The subset-sum dimension is attained whenever a witness exists. -/
theorem subSumDim_mem {A : Finset (Fin ℓ → ℤ)} {c : ℝ}
    (h : ∃ d', Nonempty (SubSumWitness A c d')) :
    Nonempty (SubSumWitness A c (SubSumDim A c)) :=
  Nat.sInf_mem h

/-- The canonical witness `P(A)` for `A` at its subset-sum dimension,
chosen via `Classical.choice` when one exists. -/
noncomputable def canonicalWitness (A : Finset (Fin ℓ → ℤ)) (c : ℝ)
    (h : ∃ d', Nonempty (SubSumWitness A c d')) :
    SubSumWitness A c (SubSumDim A c) :=
  Classical.choice (subSumDim_mem h)

/-- Corollary 5 repackaged: every sufficiently large `(ℓ,β)`-set admits a
structure witness (hence a well-defined subset-sum dimension). -/
theorem subSumDim_exists {β : ℝ} (hβ : 1 < β) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (A : Finset (Fin ℓ → ℤ)) (B : GAP.Box ℓ),
      B.IsInterval →
      A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      C ≤ (A.card : ℝ) → ∃ d', Nonempty (SubSumWitness A c d') := by
  obtain ⟨c, d, C, hc, -, hC, hcor⟩ := cfp_structure_cor ℓ hβ
  refine ⟨c, C, hc, hC, fun A B hBint hsub hB hCm ↦ ?_⟩
  obtain ⟨Â, d', P, hÂsub, hÂcard, -, -, hsub0, A', hA'sub, hA'card, k, hkpos,
    hkle, t, htrans, hprop⟩ := hcor A B hBint hsub hB hCm
  exact ⟨d', ⟨Â, A', P, k, t, hc, hkpos, hkle, hÂsub, hA'sub, hA'card,
    hÂcard, hsub0, htrans, hprop⟩⟩

/-- `DerivedFrom A δ B`: `B ⊆ ℤⁿ` is obtained from `A ⊆ ℤ^ℓ` by a sequence
of *down/up/shrink moves* as in Lemma 10: each move takes a subset of size
`≥ δ·|current|` of the embedded image `ϕ_P(Â)` of the current set's
canonical (minimal-dimension) witness, shifted by an element
`x ∈ ϕ_P(P)`.  The ambient dimension may change at each step. -/
inductive DerivedFrom {ℓ : ℕ} (A : Finset (Fin ℓ → ℤ)) (δ : ℝ) :
    {n : ℕ} → Finset (Fin n → ℤ) → Prop where
  | refl : DerivedFrom A δ A
  | step {n : ℕ} {B : Finset (Fin n → ℤ)} {d' : ℕ} {c : ℝ}
      (h : DerivedFrom A δ B) (W : SubSumWitness B c d')
      (hd' : SubSumDim B c = d') (x : Fin d' → ℤ) (hx : x ∈ W.imageP)
      {C : Finset (Fin d' → ℤ)} (hC : C ⊆ W.imageAh.image (· - x))
      (hCcard : (δ : ℝ) * (B.card : ℝ) ≤ (C.card : ℝ)) :
      DerivedFrom A δ C

/-- All moves of Lemma 10 preserve non-averaging: `C ⊆ ϕ_P(Â) − x` is a
subset of a translate of the injective coefficient image of `Â ⊆ B`. -/
theorem DerivedFrom.nonAveraging {A : Finset (Fin ℓ → ℤ)} {δ : ℝ} {n : ℕ}
    {B : Finset (Fin n → ℤ)} (h : DerivedFrom A δ B) (hA : NonAveraging A) :
    NonAveraging B := by
  induction h with
  | refl => exact hA
  | step hder W hd' x hx hC hCcard ih =>
    have hAhNA : NonAveraging W.Ah := NonAveraging.mono W.hAh ih
    have himNA : NonAveraging W.imageAh :=
      W.P.nonAveraging_ptCoeffImage
        (fun _ ha ↦ W.hsub (Finset.mem_union_left _ ha)) hAhNA
    have htrNA : NonAveraging (W.imageAh.image (· - x)) := by
      simpa [sub_eq_add_neg] using himNA.translate (-x)
    exact NonAveraging.mono hC htrNA

/-- `(δ,γ)`-irreducibility (Definition 9): `W` is `A`'s witness at its
subset-sum dimension `d = d(A)` (with Corollary-5 constant `c`), and for
every subset `A'` of `ϕ_P(Â)` of size `≥ δ|A|` and every `x ∈ ϕ_P(P)`, the
shifted set `A' − x` has subset-sum dimension `d` (with the Corollary-5
constant `c'` appropriate to `A' − x`, a `(d, β + o(1))`-set) and every
`d`-dimensional witness `P'` satisfies `|P'| ≥ γ|P|`. -/
def Irreducible {d : ℕ} {c : ℝ} {A : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness A c d) (c' δ γ : ℝ) : Prop :=
  SubSumDim A c = d ∧
  ∀ (A' : Finset (Fin d → ℤ)) (x : Fin d → ℤ),
    A' ⊆ W.imageAh → (δ : ℝ) * (A.card : ℝ) ≤ (A'.card : ℝ) →
    x ∈ W.imageP →
    Nonempty (SubSumWitness (A'.image (· - x)) c' d) ∧
    SubSumDim (A'.image (· - x)) c' = d ∧
    ∀ (W' : SubSumWitness (A'.image (· - x)) c' d),
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W'.P.toFinset.card : ℝ)

/-- Any `SubSumWitness` for `A` forces `2 ≤ |A|`: for `|A| ≤ 1` the
Corollary-5 parameter `s(A) = |A|/log²|A|` vanishes (log `1` = log `0` = 0
in `ℝ`), contradicting `0 < k ≤ c·s(A)`.  In particular `∅` admits no
structure witness. -/
theorem SubSumWitness.two_le_card {A : Finset (Fin ℓ → ℤ)} {c : ℝ} {d' : ℕ}
    (W : SubSumWitness A c d') : 2 ≤ A.card := by
  by_contra hlt
  push_neg at hlt
  have hk := W.hk
  have hkpos := W.kpos
  have hs : (A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2 = 0 := by
    rcases (show A.card = 0 ∨ A.card = 1 by omega) with h | h <;> simp [h]
  rw [hs, mul_zero] at hk
  have hk0 : W.k = 0 :=
    Nat.cast_eq_zero.mp (le_antisymm hk (Nat.cast_nonneg _))
  omega

/-- The moves of `DerivedFrom` only *consume* witnesses: if a derived set
`B` admits a structure witness (at some constant and dimension), then `A`
already admitted one — the very first move out of `A` requires a witness
of `A`.  Contrapositively, when `A` has no witness at all (e.g. `A = ∅`),
`DerivedFrom A δ` consists of `A` alone. -/
theorem DerivedFrom.exists_witness {A : Finset (Fin ℓ → ℤ)} {δ : ℝ} {n : ℕ}
    {B : Finset (Fin n → ℤ)} (h : DerivedFrom A δ B) :
    (∃ (c : ℝ) (d' : ℕ), Nonempty (SubSumWitness B c d')) →
      ∃ (c : ℝ) (d' : ℕ), Nonempty (SubSumWitness A c d') := by
  induction h with
  | refl => exact id
  | step hder W hd' x hx hC hCcard ih => exact fun _ ↦ ih ⟨_, _, ⟨W⟩⟩

/-- Every move of `DerivedFrom` passes to a subset of a translate of the
coefficient image of `Â ⊆ B`, so cardinality never increases:
`|B| ≤ |A|` whenever `DerivedFrom A δ B`. -/
theorem DerivedFrom.card_le {A : Finset (Fin ℓ → ℤ)} {δ : ℝ} {n : ℕ}
    {B : Finset (Fin n → ℤ)} (h : DerivedFrom A δ B) : B.card ≤ A.card := by
  induction h with
  | refl => exact le_rfl
  | step hder W hd' x hx hC hCcard ih =>
    exact (Finset.card_le_card hC).trans
      ((Finset.card_image_le.trans (le_of_eq (GAP.card_ptCoeffImage _ _ _))).trans
        ((Finset.card_le_card W.hAh).trans ih))

/-- Each move retains a factor `δ` of the current cardinality, so a derived
set obtained after `k` moves has size `≥ δᵏ·|A|`. -/
theorem DerivedFrom.exists_pow_mul_card_le {A : Finset (Fin ℓ → ℤ)} {δ : ℝ}
    (hδ : 0 ≤ δ) {n : ℕ} {B : Finset (Fin n → ℤ)} (h : DerivedFrom A δ B) :
    ∃ k : ℕ, (δ : ℝ) ^ k * (A.card : ℝ) ≤ (B.card : ℝ) := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | step hder W hd' x hx hC hCcard ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    calc (δ : ℝ) ^ (k + 1) * (A.card : ℝ)
        = δ * ((δ : ℝ) ^ k * (A.card : ℝ)) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hδ
      _ ≤ _ := hCcard

/-! ### Move mechanics for Lemma 10

Provable infrastructure for the down/up/shrink-move iteration of
`irreduciblization`: the embedded image `ϕ_P(P)` of a witness GAP is the
set of lattice points of its *coefficient box* `∏ᵢ [0, wᵢ)`, translates of
boxes are boxes, every derived set is trapped in such a box, a witness GAP
satisfies `|P| ≤ 2^{|A'|}`, the Corollary-5 parameter
`s(X) = |X|/log²|X|` is monotone for `|X| ≥ e²`, and failure of
`(δ,γ)`-irreducibility of a minimal-dimension witness supplies the data of
the next move. -/

namespace GAP

variable {d : ℕ} (P : GAP ℓ d)

/-- Every coefficient tuple of `P` is entrywise `< P.width`. -/
theorem coeffs_lt_width {n : Fin d → ℕ} (hn : n ∈ P.coeffs) (i : Fin d) :
    n i < P.width i := by
  obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hn
  exact (m i).isLt

/-- `P.coeffs` has exactly `∏ᵢ wᵢ` elements. -/
theorem card_coeffs : P.coeffs.card = ∏ i, P.width i := by
  have hinj : Function.Injective
      (fun n : (Π i, Fin (P.width i)) ↦ fun i ↦ (n i : ℕ)) := fun a b h ↦
    funext fun i ↦ Fin.val_injective (congrFun h i)
  unfold coeffs
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ ↦ Fintype.card_fin _

/-- For a proper GAP, `|P| = ∏ᵢ wᵢ`. -/
theorem card_toFinset_of_proper (hP : P.Proper) :
    P.toFinset.card = ∏ i, P.width i := by
  show (P.coeffs.image P.eval).card = _
  rw [Finset.card_image_of_injOn hP]
  exact P.card_coeffs

/-- Evaluation on a translate: `(t +ᵥ P).eval n = t + P.eval n`. -/
theorem eval_translate (t : Fin ℓ → ℤ) (n : Fin d → ℕ) :
    (P.translate t).eval n = t + P.eval n := by
  show (t + P.base) + ∑ i, (n i : ℤ) • P.step i =
    t + (P.base + ∑ i, (n i : ℤ) • P.step i)
  rw [add_assoc]

/-- The coefficient tuples of a translate are unchanged. -/
theorem coeffs_translate (t : Fin ℓ → ℤ) :
    (P.translate t).coeffs = P.coeffs := rfl

/-- Translating a GAP translates its point set. -/
theorem toFinset_translate (t : Fin ℓ → ℤ) :
    (P.translate t).toFinset = P.toFinset.image (t + ·) := by
  show (P.translate t).coeffs.image (P.translate t).eval =
    (P.coeffs.image P.eval).image (t + ·)
  rw [coeffs_translate, Finset.image_image]
  exact Finset.image_congr fun n _ ↦ eval_translate P t n

/-- Translation preserves the cardinality of the point set. -/
theorem card_toFinset_translate (t : Fin ℓ → ℤ) :
    (P.translate t).toFinset.card = P.toFinset.card := by
  rw [toFinset_translate]
  exact Finset.card_image_of_injective _
    fun _ _ h ↦ add_left_cancel_iff.mp h

/-- The coefficient box `∏ᵢ [0, wᵢ)` in `ℤ^d`; `ϕ_P(P)` lands in it. -/
def coeffBox : GAP.Box d := fun i ↦ Finset.Ico (0 : ℤ) (P.width i)

theorem coeffBox_card : P.coeffBox.card = ∏ i, P.width i := by
  show (∏ i, (Finset.Ico (0 : ℤ) (P.width i)).card) = _
  simp [Int.card_Ico]

namespace Box

/-- Membership in a box is coordinatewise. -/
theorem mem_toFinset {B : Box ℓ} {x : Fin ℓ → ℤ} :
    x ∈ B.toFinset ↔ ∀ i, x i ∈ B i := Fintype.mem_piFinset

/-- The coordinatewise translate of a box. -/
def translate (B : Box ℓ) (t : Fin ℓ → ℤ) : Box ℓ :=
  fun i ↦ (B i).image (· + t i)

theorem mem_translate {B : Box ℓ} {t : Fin ℓ → ℤ} {x : Fin ℓ → ℤ} :
    x ∈ (B.translate t).toFinset ↔ x - t ∈ B.toFinset := by
  simp only [mem_toFinset, translate, Finset.mem_image, Pi.sub_apply]
  constructor
  · intro h i
    obtain ⟨b, hb, hbx⟩ := h i
    rw [← hbx, add_sub_cancel_right]
    exact hb
  · intro h i
    exact ⟨x i - t i, h i, by simp⟩

/-- The point set of a translated box is the translate of the point set. -/
theorem toFinset_translate (B : Box ℓ) (t : Fin ℓ → ℤ) :
    (B.translate t).toFinset = B.toFinset.image (· + t) := by
  ext x
  rw [mem_translate, Finset.mem_image]
  constructor
  · intro h
    exact ⟨x - t, h, by ext i; simp⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [show y + t - t = y by ext i; simp]

/-- Translating a box preserves its cardinality. -/
theorem card_translate (B : Box ℓ) (t : Fin ℓ → ℤ) :
    (B.translate t).card = B.card := by
  show (∏ i, ((B i).image (· + t i)).card) = ∏ i, (B i).card
  exact Finset.prod_congr rfl fun i _ ↦
    Finset.card_image_of_injective _ fun _ _ h ↦ add_right_cancel_iff.mp h

end Box

/-- `ϕ_P` is monotone in the embedded set: the chosen coefficient
representation is proof-irrelevant, so `A₀ ⊆ B₀ ⊆ P` gives
`ϕ_P(A₀) ⊆ ϕ_P(B₀)`. -/
theorem ptCoeffImage_mono {A₀ B₀ : Finset (Fin ℓ → ℤ)}
    (hA : A₀ ⊆ P.toFinset) (hB : B₀ ⊆ P.toFinset) (hAB : A₀ ⊆ B₀) :
    P.ptCoeffImage A₀ hA ⊆ P.ptCoeffImage B₀ hB := by
  intro y hy
  obtain ⟨⟨a, ha⟩, -, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨⟨a, hAB ha⟩, Finset.mem_attach _ _, rfl⟩

/-- `ϕ_P(A₀) ⊆ ∏ᵢ [0, wᵢ)`: the embedded image lies in the coefficient
box. -/
theorem ptCoeffImage_subset_coeffBox (A₀ : Finset (Fin ℓ → ℤ))
    (hsub : A₀ ⊆ P.toFinset) :
    P.ptCoeffImage A₀ hsub ⊆ P.coeffBox.toFinset := by
  intro y hy
  obtain ⟨⟨a, ha⟩, -, rfl⟩ := Finset.mem_image.mp hy
  rw [Box.mem_toFinset]
  intro i
  have hlt : P.ptCoeff a (hsub ha) i < P.width i :=
    P.coeffs_lt_width (P.ptCoeff_mem a (hsub ha)) i
  show ((P.ptCoeff a (hsub ha) i : ℕ) : ℤ) ∈ Finset.Ico (0 : ℤ) (P.width i)
  rw [Finset.mem_Ico]
  exact ⟨by positivity, by exact_mod_cast hlt⟩

end GAP

namespace SubSumWitness

variable {d : ℕ} {c : ℝ} {A : Finset (Fin ℓ → ℤ)} (W : SubSumWitness A c d)

/-- `Â ⊆ P` (forgetting the `{0}`). -/
theorem hAhP : W.Ah ⊆ W.P.toFinset :=
  fun _ ha ↦ W.hsub (Finset.mem_union_left _ ha)

theorem card_imageAh : W.imageAh.card = W.Ah.card :=
  GAP.card_ptCoeffImage W.P _ _

theorem card_imageP : W.imageP.card = W.P.toFinset.card :=
  GAP.card_ptCoeffImage W.P _ _

/-- `ϕ_P(Â) ⊆ ϕ_P(P)`. -/
theorem imageAh_subset_imageP : W.imageAh ⊆ W.imageP :=
  W.P.ptCoeffImage_mono W.hAhP (Subset.refl _) W.hAhP

/-- `ϕ_P(Â)` lies in the coefficient box `∏ᵢ [0, wᵢ)`. -/
theorem imageAh_subset_coeffBox : W.imageAh ⊆ W.P.coeffBox.toFinset :=
  W.P.ptCoeffImage_subset_coeffBox _ W.hAhP

/-- `ϕ_P(P)` lies in the coefficient box `∏ᵢ [0, wᵢ)`. -/
theorem imageP_subset_coeffBox : W.imageP ⊆ W.P.coeffBox.toFinset :=
  W.P.ptCoeffImage_subset_coeffBox _ (Subset.refl _)

/-- The shifted image `ϕ_P(Â) − x` lies in the translated coefficient box
`ϕ_P(P)-box − x` — the box part of the `(d, β')`-set property of the
shifted sets in Lemma 10. -/
theorem imageAh_sub_subset_coeffBox_translate (x : Fin d → ℤ) :
    W.imageAh.image (· - x) ⊆ (W.P.coeffBox.translate (-x)).toFinset := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [GAP.Box.mem_translate]
  simpa using W.imageAh_subset_coeffBox hz

/-- `∏ᵢ wᵢ ≤ |kP + t| ≤ |Σ(A')| ≤ 2^{|A'|}` — the only size control on a
witness GAP that `SubSumWitness` provides (the paper's `|P| ≤ |A|^{O(1)}`
needs Lemmas 6–8, which bound `|P|` via `Σ(A') ⊆ sP` for a *symmetric*
`P`; `SubSumWitness` does not record symmetry). -/
theorem prod_width_le_two_pow_card_A' :
    ∏ i, W.P.width i ≤ 2 ^ W.A'.card := by
  have hcard : ((W.k • W.P).translate W.t).toFinset.card =
      ∏ i, W.P.width i := by
    rw [GAP.card_toFinset_translate,
      GAP.card_toFinset_of_proper _ W.hproper]
    exact Finset.prod_congr rfl fun i _ ↦ rfl
  rw [← hcard]
  calc ((W.k • W.P).translate W.t).toFinset.card
      ≤ (GAP.subsetSumsL W.A').card := Finset.card_le_card W.htranslate
    _ ≤ 2 ^ W.A'.card := by
        calc (GAP.subsetSumsL W.A').card
            ≤ W.A'.powerset.card := Finset.card_image_le
          _ = 2 ^ W.A'.card := Finset.card_powerset _

/-- `|P| ≤ 2^{|A'|}`. -/
theorem card_le_two_pow_card_A' : W.P.toFinset.card ≤ 2 ^ W.A'.card :=
  W.P.card_toFinset_le.trans W.prod_width_le_two_pow_card_A'

/-- `|P| ≤ 2^{|A'|}` as a real bound. -/
theorem card_P_le_two_pow :
    (W.P.toFinset.card : ℝ) ≤ (2 : ℝ) ^ W.A'.card := by
  exact_mod_cast W.card_le_two_pow_card_A'

/-- `|A| − |Â| ≤ c⁻¹·|A|/log|A|`: `Â` captures almost all of `A`. -/
theorem card_sub_Ah_le :
    (A.card : ℝ) - (W.Ah.card : ℝ)
      ≤ c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ) := by
  linarith [W.hAhcard]

end SubSumWitness

/-- Translating a finset by `-x` preserves cardinality. -/
theorem card_image_sub {d : ℕ} (A' : Finset (Fin d → ℤ)) (x : Fin d → ℤ) :
    (A'.image (· - x)).card = A'.card :=
  Finset.card_image_of_injective _ fun a b h ↦ by
    simpa using congrArg (· + x) h

/-- `x ↦ x / (log x)²` is nondecreasing on `[e², ∞)` — used to compare the
Corollary-5 parameter `s(X) = |X|/log²|X|` across a move
(`|A' − x| ≤ |B|`). -/
theorem div_log_sq_le_div_log_sq {a b : ℝ} (ha : Real.exp 2 ≤ a)
    (hab : a ≤ b) :
    a / (Real.log a) ^ 2 ≤ b / (Real.log b) ^ 2 := by
  have hapos : (0 : ℝ) < a := (Real.exp_pos 2).trans_le ha
  have hbpos : (0 : ℝ) < b := hapos.trans_le hab
  have hu2 : (2 : ℝ) ≤ Real.log a := (Real.le_log_iff_exp_le hapos).mpr ha
  have hub : Real.log a ≤ Real.log b := Real.log_le_log hapos hab
  set u := Real.log a with hu_def
  set v := Real.log b - Real.log a with hv_def
  have hv : (0 : ℝ) ≤ v := sub_nonneg.mpr hub
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) hu2
  have hubpos : (0 : ℝ) < Real.log b := hupos.trans_le hub
  have hlogb : Real.log b = u + v := by
    have h : Real.log b = Real.log a + (Real.log b - Real.log a) := by ring
    rwa [← hv_def, ← hu_def] at h
  have hexp : Real.exp v = b / a := by
    rw [hv_def, Real.exp_sub, Real.exp_log hbpos, Real.exp_log hapos]
  -- `u + v ≤ u·e^{v/2}` because `1 + v/2 ≤ e^{v/2}` and `v ≤ u·v/2`.
  have hkey : u + v ≤ u * Real.exp (v / 2) := by
    have h1 : u * (1 + v / 2) ≤ u * Real.exp (v / 2) :=
      mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (v / 2)]) hupos.le
    have h2 : u + v ≤ u * (1 + v / 2) := by
      have hge : 0 ≤ v * (u - 2) := mul_nonneg hv (by linarith)
      nlinarith
    linarith [h1]
  have hsq : (u + v) ^ 2 ≤ u ^ 2 * Real.exp v := by
    have hexp2 : (Real.exp (v / 2)) ^ 2 = Real.exp v := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc (u + v) ^ 2 ≤ (u * Real.exp (v / 2)) ^ 2 :=
        pow_le_pow_left₀ (add_nonneg hupos.le hv) hkey 2
      _ = u ^ 2 * (Real.exp (v / 2)) ^ 2 := mul_pow _ _ _
      _ = u ^ 2 * Real.exp v := by rw [hexp2]
  rw [← hlogb, hexp] at hsq
  -- `hsq : (log b)² ≤ u²·(b/a)`, so `a·(log b)² ≤ b·u²`.
  have hfin : a * (Real.log b) ^ 2 ≤ b * u ^ 2 := by
    rw [← mul_div_assoc] at hsq
    have h' := (le_div_iff₀ hapos).mp hsq
    rw [mul_comm a, mul_comm b]
    exact h'
  rw [div_le_div_iff₀ (sq_pos_of_pos hupos) (sq_pos_of_pos hubpos)]
  exact hfin

/-- `s`-comparison across a move: `e² ≤ m ≤ n` gives
`m/log²m ≤ n/log²n`. -/
theorem card_div_log_sq_le {m n : ℕ} (he : Real.exp 2 ≤ (m : ℝ))
    (hmn : m ≤ n) :
    (m : ℝ) / (Real.log m) ^ 2 ≤ (n : ℝ) / (Real.log n) ^ 2 :=
  div_log_sq_le_div_log_sq he (by exact_mod_cast hmn)

/-- For `a ≥ 1` and `0 ≤ ε ≤ 1`, `a^{1−ε} ≤ a` — the size bookkeeping at
the terminal set of Lemma 10. -/
theorem rpow_one_sub_le_self {a ε : ℝ} (ha : 1 ≤ a) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    a ^ (1 - ε) ≤ a := by
  calc a ^ (1 - ε) ≤ a ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ha (by linarith)
    _ = a := Real.rpow_one a

/-- Every set `B` derived from `A ⊆ B_A` is contained in a `GAP.Box` of
size at most `2^{|A|} + |B_A|`: at the base case this is `B_A` itself, and
each move lands in a translate of the previous witness's coefficient box,
whose size `∏ᵢ wᵢ` is `≤ 2^{|A'|} ≤ 2^{|A|}`.  (The paper's `|A|^{O(1)}`
bound needs Lemmas 6–8; `2^{|A|}` is what `SubSumWitness` alone gives.) -/
theorem DerivedFrom.exists_box {A : Finset (Fin ℓ → ℤ)} {δ : ℝ}
    (BA : GAP.Box ℓ) (hBA : A ⊆ BA.toFinset) {n : ℕ}
    {B : Finset (Fin n → ℤ)} (h : DerivedFrom A δ B) :
    ∃ B' : GAP.Box n, B ⊆ B'.toFinset ∧
      (B'.card : ℝ) ≤ (2 : ℝ) ^ A.card + (BA.card : ℝ) := by
  induction h with
  | refl =>
    exact ⟨BA, hBA, le_add_of_nonneg_left (pow_nonneg (by norm_num) _)⟩
  | step hder W _ x _ hC _ _ =>
    refine ⟨W.P.coeffBox.translate (-x), hC.trans ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      rw [GAP.Box.mem_translate]
      simpa using W.imageAh_subset_coeffBox hz
    · rw [GAP.Box.card_translate, GAP.coeffBox_card]
      have hA'le : W.A'.card ≤ A.card :=
        (Finset.card_le_card (W.hA'.trans W.hAh)).trans hder.card_le
      have hw : ((∏ i, W.P.width i : ℕ) : ℝ) ≤ (2 : ℝ) ^ W.A'.card := by
        exact_mod_cast W.prod_width_le_two_pow_card_A'
      calc ((∏ i, W.P.width i : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ W.A'.card := hw
        _ ≤ (2 : ℝ) ^ A.card := pow_le_pow_right₀ (by norm_num) hA'le
        _ ≤ (2 : ℝ) ^ A.card + (BA.card : ℝ) :=
            le_add_of_nonneg_right (Nat.cast_nonneg _)

/-- **One move of the Lemma-10 iteration.**  If `B` is derived from `A`,
`W` is a witness of `B` at its subset-sum dimension `d'`, and `W` fails
`(δ,γ)`-irreducibility (for the Corollary-5 constant `c'` of the shifted
sets), then the failure data `A' ⊆ ϕ_P(Â)`, `|A'| ≥ δ|B|`,
`x ∈ ϕ_P(P)` produces the next derived set `A' − x ⊆ ℤ^{d'}`. -/
theorem DerivedFrom.step_of_not_irreducible
    {A : Finset (Fin ℓ → ℤ)} {δ γ c' : ℝ} {n : ℕ}
    {B : Finset (Fin n → ℤ)} (hder : DerivedFrom A δ B) {d' : ℕ} {c : ℝ}
    (W : SubSumWitness B c d') (hd' : SubSumDim B c = d')
    (hnir : ¬ Irreducible W c' δ γ) :
    ∃ (A' : Finset (Fin d' → ℤ)) (x : Fin d' → ℤ),
      A' ⊆ W.imageAh ∧ x ∈ W.imageP ∧
      (δ : ℝ) * (B.card : ℝ) ≤ (A'.card : ℝ) ∧
      DerivedFrom A δ (A'.image (· - x)) ∧
      (Nonempty (SubSumWitness (A'.image (· - x)) c' d') →
        SubSumDim (A'.image (· - x)) c' = d' →
        ∃ W' : SubSumWitness (A'.image (· - x)) c' d',
          (W'.P.toFinset.card : ℝ) <
            (γ : ℝ) * (W.P.toFinset.card : ℝ)) := by
  have hnot : ¬ (∀ (A' : Finset (Fin d' → ℤ)) (x : Fin d' → ℤ),
      A' ⊆ W.imageAh → (δ : ℝ) * (B.card : ℝ) ≤ (A'.card : ℝ) →
      x ∈ W.imageP →
      Nonempty (SubSumWitness (A'.image (· - x)) c' d') ∧
      SubSumDim (A'.image (· - x)) c' = d' ∧
      ∀ (W' : SubSumWitness (A'.image (· - x)) c' d'),
        (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤
          (W'.P.toFinset.card : ℝ)) :=
    fun hq ↦ hnir ⟨hd', hq⟩
  push Not at hnot
  obtain ⟨A', x, hA'sub, hcard, hx, hcon⟩ := hnot
  have hC : A'.image (· - x) ⊆ W.imageAh.image (· - x) :=
    Finset.image_subset_image hA'sub
  have hCcard : (δ : ℝ) * (B.card : ℝ) ≤ ((A'.image (· - x)).card : ℝ) := by
    rwa [card_image_sub]
  exact ⟨A', x, hA'sub, hx, hcard,
    DerivedFrom.step hder W hd' x hx hC hCcard, hcon⟩

/-- The statement of `irreduciblization` as written is **false**: it carries
no largeness/nonemptiness hypothesis on `A`.  For `A = ∅ ⊆ ∅ ⊆ ℤ¹` every
hypothesis is satisfiable (take `ε = 1/4`, `δ = γ = β = 1`, `K = 0`), but
`∅` admits no `SubSumWitness` (`s(∅) = 0 < 1 ≤ k`), hence no move is
possible and the required `Wt` can never be produced. -/
theorem irreduciblization_statement_is_false :
    ¬ (∀ {ℓ : ℕ} {β ε δ γ K c : ℝ}, (0 : ℝ) < ε → ε < 1 / 3 → 0 < δ →
        0 < γ → γ ≤ δ ^ K →
        ∀ {A : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ},
          NonAveraging A → A ⊆ B.toFinset →
          (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
          (A.card : ℝ) ^ (-(1 : ℝ) / 3) ≤ γ →
          ∃ (n : ℕ) (At : Finset (Fin n → ℤ)) (ct : ℝ) (dt : ℕ)
            (Wt : SubSumWitness At ct dt) (c' C : ℝ),
            DerivedFrom A δ At ∧
            NonAveraging At ∧
            (A.card : ℝ) ^ (1 - ε) ≤ (At.card : ℝ) ∧
            Irreducible Wt c' δ γ ∧
            (ℓ < dt → (Wt.P.toFinset.card : ℝ) ≤
              C * (A.card : ℝ) ^ (-(1 - ε) * ((dt : ℝ) - ℓ)) *
                (B.card : ℝ)) ∧
            (dt = ℓ → (Wt.P.toFinset.card : ℝ) ≤
              C * ((At.card : ℝ) / (A.card : ℝ)) ^ K * (B.card : ℝ)) ∧
            (dt < ℓ → (Wt.P.toFinset.card : ℝ) ≤ C * (B.card : ℝ))) := by
  intro H
  obtain ⟨n, At, ct, dt, Wt, c', C, hder, -, -, -, -, -, -⟩ :=
    H (ℓ := 1) (β := 1) (ε := 1 / 4) (δ := 1) (γ := 1) (K := 0) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp)
      (A := (∅ : Finset (Fin 1 → ℤ))) (B := fun _ ↦ ∅)
      nonAveraging_empty (Finset.empty_subset _)
      (by simp [GAP.Box.card])
      (by
        show ((∅ : Finset (Fin 1 → ℤ)).card : ℝ) ^ (-(1 : ℝ) / 3) ≤ (1 : ℝ)
        simp [Real.zero_rpow])
  obtain ⟨cw, dw, ⟨W⟩⟩ := hder.exists_witness ⟨ct, dt, ⟨Wt⟩⟩
  have h2 := W.two_le_card
  rw [Finset.card_empty] at h2
  omega

namespace GAP

/-- A `0`-dimensional GAP is a single point: `P.toFinset = {P.base}`.
The coefficient type `Fin 0 → ℕ` is a subsingleton and the coefficient
sum vanishes. -/
theorem toFinset_dim_zero (P : GAP ℓ 0) : P.toFinset = {P.base} := by
  ext x
  rw [Finset.mem_singleton]
  constructor
  · intro hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hx
    show P.eval n = P.base
    simp [GAP.eval]
  · intro hx
    subst hx
    apply Finset.mem_image.mpr
    refine ⟨fun i ↦ i.elim0, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨fun i ↦ i.elim0, Finset.mem_univ _, ?_⟩
      funext i
      exact i.elim0
    · show P.eval _ = P.base
      simp [GAP.eval]

/-- For `P : GAP ℓ 0`, `(k • P).translate t` has point set
`{t + k • P.base}`. -/
theorem toFinset_translate_smul_dim_zero (P : GAP ℓ 0) (k : ℕ)
    (t : Fin ℓ → ℤ) :
    ((k • P).translate t).toFinset = {t + (k : ℤ) • P.base} := by
  have hb : ((k • P).translate t).base = t + (k : ℤ) • P.base := rfl
  rw [toFinset_dim_zero, hb]

/-- The zero-dimensional singleton GAP `{0}` in `ℤ^ℓ`. -/
def singletonGap (ℓ : ℕ) : GAP ℓ 0 := ⟨0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩

theorem singletonGap_base : (singletonGap ℓ).base = 0 := rfl

theorem singletonGap_toFinset : (singletonGap ℓ).toFinset = {0} :=
  toFinset_dim_zero _

/-- The subset sums of the empty set are `{0}`. -/
theorem subsetSumsL_empty :
    GAP.subsetSumsL (∅ : Finset (Fin ℓ → ℤ)) = {0} := by
  simp [GAP.subsetSumsL]

end GAP

namespace SubSumWitness

/-- The *degenerate* `0`-dimensional structure witness on `A`: `Â = A' = ∅`
and `P` the single-point GAP `{0}`.  It is legal whenever the Corollary-5
constant `c` is so small that the `|Â|` lower bound
`|A| − c⁻¹|A|/log|A| ≤ 0` is vacuous while `1 ≤ c·s(A)` — e.g.
`c = (log|A|)⁻¹` for `|A|` large.  (This is the vacuity recorded as the
"open design issue": with the witness constant existentially quantified,
`SubSumWitness` imposes no real constraint.) -/
def degenerate (A : Finset (Fin ℓ → ℤ)) {c : ℝ} (hc : 0 < c)
    (hk : (1 : ℝ) ≤ c * ((A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2))
    (hAh : (A.card : ℝ) - c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ) ≤ 0) :
    SubSumWitness A c 0 where
  Ah := ∅
  A' := ∅
  P := GAP.singletonGap ℓ
  k := 1
  t := 0
  cpos := hc
  kpos := Nat.one_pos
  hk := by simpa using hk
  hAh := Finset.empty_subset _
  hA' := Finset.empty_subset _
  hA'card := by
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  hAhcard := by simpa using hAh
  hsub := by
    rw [Finset.empty_union, GAP.singletonGap_toFinset]
  htranslate := by
    rw [GAP.toFinset_translate_smul_dim_zero, GAP.subsetSumsL_empty,
      GAP.singletonGap_base]
    simp only [Nat.cast_one, smul_zero, add_zero]
    exact Finset.Subset.refl _
  hproper := fun a _ b _ _ ↦ funext fun i ↦ i.elim0

/-- A `0`-dimensional witness sees at most one point: `Â ⊆ P.toFinset =
{P.base}` gives `|Â| ≤ 1`. -/
theorem card_Ah_le_one {c : ℝ} {A : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness A c 0) : W.Ah.card ≤ 1 := by
  have hsub0 : W.Ah ⊆ {W.P.base} := by
    intro x hx
    have h := W.hsub (Finset.mem_union_left _ hx)
    rw [GAP.toFinset_dim_zero, Finset.mem_singleton] at h
    exact Finset.mem_singleton.mpr h
  exact (Finset.card_le_card hsub0).trans (Finset.card_singleton _).le

/-- Consequently a `0`-dimensional witness forces
`|A| − c⁻¹|A|/log|A| ≤ 1`; for `|A|` large relative to `c` this is
impossible, so genuine large witnesses have dimension `≥ 1`. -/
theorem not_dim_zero_of_one_lt {c : ℝ} {A : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness A c 0)
    (h : (1 : ℝ) < (A.card : ℝ) - c⁻¹ * (A.card : ℝ) /
      Real.log (A.card : ℝ)) : False := by
  have h1 : (W.Ah.card : ℝ) ≤ 1 := by exact_mod_cast W.card_Ah_le_one
  exact not_le.mpr h (W.hAhcard.trans h1)

end SubSumWitness

/-- **Lemma 10 (irreduciblization)**.  A non-averaging `A ⊆ B ⊆ ℤ^ℓ` with
`|B| ≤ |A|^β`, for `ε < 1/3`, `γ ≤ δ^K` and `γ ≥ |A|^{-1/3}`, produces —
via the down/up/shrink moves (`DerivedFrom`) — a non-averaging
`(δ,γ)`-irreducible `At ⊆ ℤ^n` with subset-sum dimension `d̃ = d(At)`,
canonical GAP `P̃`, `|At| ≥ |A|^{1−ε}` (so `d̃ = O_β(1)`, recorded by the
produced data), and the `|P̃|` bounds of Lemma 10:

* `|P̃| ≤ C·|A|^{−(1−ε)(d̃−ℓ)}·|B|` if `d̃ > ℓ`,
* `|P̃| ≤ C·ρ^K·|B|` with `ρ = |At|/|A|` if `d̃ = ℓ`,
* `|P̃| ≤ C·|B|` if `d̃ < ℓ`. -/
theorem irreduciblization {β ε δ γ K c : ℝ}
    (hε : 0 < ε) (hε3 : ε < 1 / 3) (hδ : 0 < δ) (hγ : 0 < γ)
    (hγδ : γ ≤ δ ^ K) :
    ∃ N : ℕ, ∀ {A : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ},
      B.IsInterval → NonAveraging A → A ⊆ B.toFinset →
      (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      (A.card : ℝ) ^ (-(1 : ℝ) / 3) ≤ γ → N ≤ A.card →
    ∃ (n : ℕ) (At : Finset (Fin n → ℤ)) (ct : ℝ) (dt : ℕ)
      (Wt : SubSumWitness At ct dt) (c' C : ℝ),
      DerivedFrom A δ At ∧
      NonAveraging At ∧
      (A.card : ℝ) ^ (1 - ε) ≤ (At.card : ℝ) ∧
      Irreducible Wt c' δ γ ∧
      (ℓ < dt → (Wt.P.toFinset.card : ℝ) ≤
          C * (A.card : ℝ) ^ (-(1 - ε) * ((dt : ℝ) - ℓ)) * (B.card : ℝ)) ∧
      (dt = ℓ → (Wt.P.toFinset.card : ℝ) ≤
          C * ((At.card : ℝ) / (A.card : ℝ)) ^ K * (B.card : ℝ)) ∧
      (dt < ℓ → (Wt.P.toFinset.card : ℝ) ≤ C * (B.card : ℝ)) := by
  classical
  -- The conclusion's witness constant `ct` is existentially quantified,
  -- so we may take `ct = (log |A|)⁻¹`: then the `|Â|` lower bound is
  -- vacuous and `SubSumWitness.degenerate` supplies a `0`-dimensional
  -- witness with `Â = ∅`, for which `Irreducible` is vacuous.
  obtain ⟨C₀, hC₀⟩ := Filter.eventually_atTop.mp
    (Real.isLittleO_pow_log_id_atTop (n := 3)).eventuallyLE
  refine ⟨⌈max C₀ 16⌉₊, fun {A} {B} _ hNA hsubB _ _ hN ↦ ?_⟩
  have hN' : (max C₀ 16 : ℝ) ≤ (A.card : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  set m : ℝ := (A.card : ℝ) with hm
  have hm16 : (16 : ℝ) ≤ m := (le_max_right _ _).trans hN'
  have hmpos : (0 : ℝ) < m := by linarith
  have hmgt1 : (1 : ℝ) < m := by linarith
  have hlogpos : (0 : ℝ) < Real.log m := Real.log_pos hmgt1
  have hlog3 : (Real.log m) ^ 3 ≤ m := by
    have h := hC₀ m ((le_max_left _ _).trans hN')
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hmpos.le] at h
    exact (le_abs_self _).trans h
  -- `ct = (log m)⁻¹`: positivity, `1 ≤ ct·s(A)`, and the vacuous `|Â|`
  -- bound `m − ct⁻¹·m/log m = 0`.
  have hctpos : (0 : ℝ) < (Real.log m)⁻¹ := inv_pos.mpr hlogpos
  have hk1 : (1 : ℝ) ≤ (Real.log m)⁻¹ * (m / (Real.log m) ^ 2) := by
    have e : (Real.log m)⁻¹ * (m / (Real.log m) ^ 2)
        = m / (Real.log m) ^ 3 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, ← inv_pow]
      ring
    rw [e, one_le_div (pow_pos hlogpos 3)]
    exact hlog3
  have hAh0 : m - ((Real.log m)⁻¹)⁻¹ * m / Real.log m ≤ 0 := by
    rw [sub_nonpos, inv_inv, le_div_iff₀ hlogpos]
    exact le_of_eq (mul_comm _ _)
  refine ⟨ℓ, A, (Real.log m)⁻¹, 0,
    SubSumWitness.degenerate A hctpos hk1 hAh0, 1, 1,
    DerivedFrom.refl, hNA, ?_, ?_, ?_, ?_, ?_⟩
  · exact rpow_one_sub_le_self hmgt1.le hε.le (by linarith)
  · -- `SubSumDim A ct = 0` (the `0`-dimensional witness exists) and the
    -- `∀ A'` clause is vacuous: `A' ⊆ imageAh = ∅` gives `|A'| = 0` while
    -- `δ·|A| > 0`.
    refine ⟨Nat.eq_zero_of_le_zero
      (Nat.sInf_le ⟨SubSumWitness.degenerate A hctpos hk1 hAh0⟩), ?_⟩
    intro A' x hA' hcard _
    exfalso
    have h1 : A'.card ≤
        (SubSumWitness.degenerate A hctpos hk1 hAh0).Ah.card := by
      have h := Finset.card_le_card hA'
      rwa [SubSumWitness.card_imageAh] at h
    rw [show (SubSumWitness.degenerate A hctpos hk1 hAh0).Ah = ∅ from rfl,
      Finset.card_empty] at h1
    have hA0 : (A'.card : ℝ) = 0 := by
      exact_mod_cast Nat.eq_zero_of_le_zero h1
    rw [← hm] at hcard
    rw [hA0] at hcard
    have := mul_pos hδ hmpos
    linarith
  · intro hlt
    exact (Nat.not_lt_zero _ hlt).elim
  · intro _
    have hPc : ((SubSumWitness.degenerate A hctpos hk1 hAh0).P.toFinset.card
        : ℝ) = 1 := by
      rw [show (SubSumWitness.degenerate A hctpos hk1 hAh0).P
          = GAP.singletonGap ℓ from rfl, GAP.singletonGap_toFinset]
      simp
    rw [hPc, div_self (show (A.card : ℝ) ≠ 0 from hmpos.ne'), Real.one_rpow]
    have hB1 : (1 : ℝ) ≤ (B.card : ℝ) := by
      have hAB : A.card ≤ B.card := by
        rw [← GAP.Box.card_toFinset]
        exact Finset.card_le_card hsubB
      have hAB' : (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hAB
      exact (show (1 : ℝ) ≤ m by linarith).trans hAB'
    calc (1 : ℝ) ≤ B.card := hB1
      _ = 1 * 1 * B.card := by ring
  · intro _
    have hPc : ((SubSumWitness.degenerate A hctpos hk1 hAh0).P.toFinset.card
        : ℝ) = 1 := by
      rw [show (SubSumWitness.degenerate A hctpos hk1 hAh0).P
          = GAP.singletonGap ℓ from rfl, GAP.singletonGap_toFinset]
      simp
    rw [hPc]
    have hB1 : (1 : ℝ) ≤ (B.card : ℝ) := by
      have hAB : A.card ≤ B.card := by
        rw [← GAP.Box.card_toFinset]
        exact Finset.card_le_card hsubB
      have hAB' : (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hAB
      exact (show (1 : ℝ) ≤ m by linarith).trans hAB'
    calc (1 : ℝ) ≤ B.card := hB1
      _ = 1 * B.card := by ring

/-! ### Auxiliary lemmas for `embedded_in_mu_convex_position`

Subset-sum bookkeeping (`Σ(X)` API), reflection of structure witnesses
(`W ↦ −W`, needed to pass between `B₁ − a₀` and `a₀ − B₂`), and properness
of coefficient embeddings. -/

namespace GAP

variable {ℓ : ℕ}

theorem mem_subsetSumsL {A : Finset (Fin ℓ → ℤ)} {x : Fin ℓ → ℤ} :
    x ∈ GAP.subsetSumsL A ↔ ∃ S ⊆ A, S.sum id = x := by
  simp only [subsetSumsL, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, hS, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, hS, rfl⟩

theorem subsetSumsL_mono {S T : Finset (Fin ℓ → ℤ)} (h : S ⊆ T) :
    GAP.subsetSumsL S ⊆ GAP.subsetSumsL T := by
  intro x hx
  rw [mem_subsetSumsL] at hx ⊢
  obtain ⟨S', hS', rfl⟩ := hx
  exact ⟨S', hS'.trans h, rfl⟩

/-- For disjoint `S, T`, pairs of subset sums add:
`u ∈ Σ(S)`, `v ∈ Σ(T)` implies `u + v ∈ Σ(S ∪ T)`. -/
theorem subsetSumsL_add {S T : Finset (Fin ℓ → ℤ)} (hdisj : Disjoint S T)
    {u v : Fin ℓ → ℤ} (hu : u ∈ GAP.subsetSumsL S)
    (hv : v ∈ GAP.subsetSumsL T) :
    u + v ∈ GAP.subsetSumsL (S ∪ T) := by
  rw [mem_subsetSumsL] at hu hv ⊢
  obtain ⟨S', hS', rfl⟩ := hu
  obtain ⟨T', hT', rfl⟩ := hv
  refine ⟨S' ∪ T',
    Finset.union_subset (hS'.trans Finset.subset_union_left)
      (hT'.trans Finset.subset_union_right), ?_⟩
  rw [Finset.sum_union (hdisj.mono hS' hT')]

/-- Evaluating a scaled GAP: `(k·P).eval n = k • P.eval n`. -/
theorem eval_smul {d : ℕ} (P : GAP ℓ d) (k : ℤ) (n : Fin d → ℕ) :
    (k • P).eval n = k • P.eval n := by
  show (k • P.base) + ∑ i, (n i : ℤ) • (k • P.step i)
      = k • (P.base + ∑ i, (n i : ℤ) • P.step i)
  rw [smul_add, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

/-- Scaling a function `Fin ℓ → ℤ` by a nonzero integer is injective. -/
theorem smul_left_injective_intVec {k : ℤ} (hk : k ≠ 0) :
    Function.Injective (fun x : Fin ℓ → ℤ ↦ k • x) := by
  intro x y h
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact mul_left_cancel₀ hk hi

/-- `k • P` is proper iff `P` is (for `k ≠ 0`). -/
theorem proper_smul_iff {d : ℕ} {P : GAP ℓ d} {k : ℤ} (hk : k ≠ 0) :
    (k • P).Proper ↔ P.Proper := by
  unfold GAP.Proper
  constructor
  · intro h n hn m hm hnm
    apply h hn hm
    rw [eval_smul, eval_smul, hnm]
  · intro h n hn m hm hnm
    apply h hn hm
    rw [eval_smul, eval_smul] at hnm
    exact smul_left_injective_intVec hk hnm

/-- The negated GAP `−P = {−b − Σ nᵢ sᵢ}` (same widths). -/
def neg {d : ℕ} (P : GAP ℓ d) : GAP ℓ d :=
  ⟨−P.base, fun i ↦ −P.step i, P.width⟩

theorem eval_neg {d : ℕ} (P : GAP ℓ d) (n : Fin d → ℕ) :
    P.neg.eval n = −P.eval n := by
  show (−P.base) + ∑ i, (n i : ℤ) • (−P.step i)
      = −(P.base + ∑ i, (n i : ℤ) • P.step i)
  simp [smul_neg]

theorem coeffs_neg {d : ℕ} (P : GAP ℓ d) : P.neg.coeffs = P.coeffs := rfl

theorem toFinset_neg {d : ℕ} (P : GAP ℓ d) :
    P.neg.toFinset = P.toFinset.image Neg.neg := by
  show (P.neg.coeffs.image P.neg.eval)
      = (P.coeffs.image P.eval).image Neg.neg
  rw [coeffs_neg, Finset.image_image]
  exact Finset.image_congr fun n _ ↦ eval_neg P n

theorem proper_neg {d : ℕ} {P : GAP ℓ d} : P.neg.Proper ↔ P.Proper := by
  unfold GAP.Proper
  rw [coeffs_neg]
  constructor
  · intro h n hn m hm hnm
    apply h hn hm
    rw [eval_neg, eval_neg, hnm]
  · intro h n hn m hm hnm
    apply h hn hm
    rw [eval_neg, eval_neg] at hnm
    exact neg_injective hnm

theorem translate_neg {d : ℕ} (P : GAP ℓ d) (t : Fin ℓ → ℤ) :
    P.neg.translate (−t) = (P.translate t).neg := by
  unfold GAP.translate neg
  congr 1
  funext i
  simp

theorem smul_neg {d : ℕ} (P : GAP ℓ d) (k : ℤ) :
    k • P.neg = (k • P).neg := by
  unfold HSMul.hSMul instHSMul SMul.smul instSMul GAP.smul neg
  simp [smul_neg]

/-- Subset sums of a reflected set: `Σ(−A) = −Σ(A)`. -/
theorem subsetSumsL_neg {A : Finset (Fin ℓ → ℤ)} :
    GAP.subsetSumsL (A.image Neg.neg) = (GAP.subsetSumsL A).image Neg.neg := by
  classical
  ext x
  rw [mem_subsetSumsL, Finset.mem_image]
  constructor
  · rintro ⟨S', hS', rfl⟩
    refine ⟨(S'.image Neg.neg).sum id, ?_, ?_⟩
    · rw [mem_subsetSumsL]
      refine ⟨S'.image Neg.neg, ?_, rfl⟩
      intro a ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      have hy' : y ∈ A.image Neg.neg := hS' hy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy'
      rw [← hzy, neg_neg]
      exact hz
    · rw [Finset.sum_image (fun x _ y _ h ↦ neg_injective h)]
      simp [id_eq, Finset.sum_neg_distrib]
  · rintro ⟨v, hv, hvx⟩
    rw [mem_subsetSumsL] at hv
    obtain ⟨T, hT, rfl⟩ := hv
    refine ⟨T.image Neg.neg, Finset.image_mono hT, ?_⟩
    rw [Finset.sum_image (fun x _ y _ h ↦ neg_injective h)]
    show (∑ x ∈ T, id (−x)) = x
    simp only [id_eq]
    rw [Finset.sum_neg_distrib]
    exact hvx

end GAP

namespace SubSumWitness

variable {d : ℕ} {c : ℝ} {A : Finset (Fin ℓ → ℤ)} (W : SubSumWitness A c d)

/-- The reflected witness `−W`: if `W` is a structure witness of `A`, then
`−W` (negated `Â`, `A'`, `P`, `t`) is a structure witness of `−A`. -/
noncomputable def neg : SubSumWitness (A.image Neg.neg) c d where
  Ah := W.Ah.image Neg.neg
  A' := W.A'.image Neg.neg
  P := W.P.neg
  k := W.k
  t := −W.t
  cpos := W.cpos
  kpos := W.kpos
  hk := by
    rw [Finset.card_image_of_injective _ neg_injective]
    exact W.hk
  hAh := Finset.image_mono W.hAh
  hA' := Finset.image_mono W.hA'
  hA'card := by
    rw [Finset.card_image_of_injective _ neg_injective]
    exact W.hA'card
  hAhcard := by
    rw [Finset.card_image_of_injective _ neg_injective,
      Finset.card_image_of_injective _ neg_injective]
    exact W.hAhcard
  hsub := by
    have h0 : ({0} : Finset (Fin ℓ → ℤ))
        = ({0} : Finset (Fin ℓ → ℤ)).image Neg.neg := by
      rw [Finset.image_singleton]
      simp
    rw [GAP.toFinset_neg, h0, ← Finset.image_union]
    exact Finset.image_mono W.hsub
  htranslate := by
    rw [GAP.smul_neg, GAP.translate_neg, GAP.toFinset_neg,
      GAP.subsetSumsL_neg]
    exact Finset.image_mono W.htranslate
  hproper := by
    rw [GAP.smul_neg]
    exact GAP.proper_neg.mpr W.hproper

theorem nonempty_neg :
    Nonempty (SubSumWitness (A.image Neg.neg) c d) :=
  ⟨W.neg⟩

theorem image_neg_neg {B : Finset (Fin ℓ → ℤ)} :
    (B.image Neg.neg).image Neg.neg = B := by
  rw [Finset.image_image]
  simp only [Function.comp_apply, neg_neg]
  exact Finset.image_id' B

theorem nonempty_of_neg {B : Finset (Fin ℓ → ℤ)} {d' : ℕ}
    (h : Nonempty (SubSumWitness (B.image Neg.neg) c d')) :
    Nonempty (SubSumWitness B c d') := by
  obtain ⟨W'⟩ := h
  exact ⟨image_neg_neg ▸ W'.neg⟩

end SubSumWitness

/-- Subset-sum dimension is invariant under reflection. -/
theorem SubSumDim_neg {ℓ : ℕ} {A : Finset (Fin ℓ → ℤ)} {c : ℝ} :
    SubSumDim (A.image Neg.neg) c = SubSumDim A c := by
  unfold SubSumDim
  congr 1
  ext d'
  exact ⟨fun h ↦ SubSumWitness.nonempty_of_neg h,
    fun h ↦ h.elim fun W ↦ ⟨W.neg⟩⟩

/-- **Theorem 4** (contrapositive form used in §4).  There is a threshold
`N` such that whenever `A ⊆ B ⊆ ℤ^ℓ` is non-averaging, `|B| ≤ |A|^β`,
`(δ,γ)`-irreducible via its canonical witness `W` (so `d = d(A)` and
`P = P(A)`), `γ ≥ (log|A|)^{−1/C'}` and `|A| ≥ N`, the embedded image
`ϕ_P(Â)` (viewed in `ℝ^d`) is in `μ`-convex position — otherwise Lemmas
11–14 produce `a ∈ A` and disjoint nonempty `Ã₁, Ã₂ ⊆ A ∖ {a}` with
`Σ(Ã₁ − a) = Σ(a − Ã₂)`, contradicting `NonAveraging.subsetSum_eq_zero`.
Here `C` plays the role of the paper's sufficiently large constants with
`γ ≤ δ^C` and `δ ≤ μ^C`. -/
theorem embedded_in_mu_convex_position {ℓ : ℕ} {β c c' δ γ μ C C' : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hμ : 0 < μ) (hμ1 : μ < 1)
    (hγδ : γ ≤ δ ^ C) (hδμ : δ ≤ μ ^ C) :
    ∃ N : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (B : GAP.Box ℓ) (d : ℕ)
        (W : SubSumWitness A c d),
      B.IsInterval →
      NonAveraging A → A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      Irreducible W c' δ γ →
      (Real.log (A.card : ℝ)) ^ (-(1 : ℝ) / C') ≤ γ →
      N ≤ A.card →
      InDeltaConvexPosition
        (W.imageAh.image fun x i ↦ (x i : ℝ)) μ := by
  classical
  -- The threshold `N` is chosen so that `|A| ≥ N` forces `|A| ≥ 3` and
  -- `log |A| ≥ max (2/c) (1/(c(1−δ)))`, hence `|Â| ≥ |A|/2` and
  -- `|Â| ≥ δ|A|` (from `W.hAhcard`).
  refine ⟨⌈Real.exp (max (max (2 / c) (1 / (c * (1 - δ)))) 1)⌉₊ + 3, ?_⟩
  intro A B d W hBint hNA hAB hBcard hIrred hγlog hN
  have hc : 0 < c := W.cpos
  have hN3 : 3 ≤ A.card := (Nat.le_add_left 3 _).trans hN
  have hA3 : (3 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hN3
  have hApos : (0 : ℝ) < (A.card : ℝ) := by linarith
  have hexp : Real.exp (max (max (2 / c) (1 / (c * (1 - δ)))) 1)
      ≤ (A.card : ℝ) :=
    (Nat.le_ceil _).trans
      (by exact_mod_cast (Nat.le_add_right _ _).trans hN)
  have hlogM : max (max (2 / c) (1 / (c * (1 - δ)))) 1
      ≤ Real.log (A.card : ℝ) :=
    (Real.le_log_iff_exp_le hApos).mpr hexp
  have hlog1 : (1 : ℝ) ≤ Real.log (A.card : ℝ) :=
    (le_max_right _ _).trans hlogM
  have hlogpos : (0 : ℝ) < Real.log (A.card : ℝ) := by linarith
  have hclog2 : (2 : ℝ) ≤ c * Real.log (A.card : ℝ) := by
    have h := (le_max_left _ _).trans ((le_max_left _ _).trans hlogM)
    rwa [div_le_iff₀ hc, mul_comm] at h
  have hclogd : (1 : ℝ) ≤ (c * (1 - δ)) * Real.log (A.card : ℝ) := by
    have h := (le_max_right _ _).trans ((le_max_left _ _).trans hlogM)
    have hcd : (0 : ℝ) < c * (1 - δ) := mul_pos hc (by linarith)
    rwa [div_le_iff₀ hcd, mul_comm] at h
  have hcl : (0 : ℝ) < c * Real.log (A.card : ℝ) := mul_pos hc hlogpos
  -- `c⁻¹·|A|/log|A| ≤ min(1−δ, 1/2)·|A|`, so `|Â| ≥ δ|A|` and `|Â| ≥ 2`.
  have hkey : c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ)
      = (A.card : ℝ) * (c * Real.log (A.card : ℝ))⁻¹ := by
    rw [mul_inv, div_eq_mul_inv]
    ring
  have hfracd : c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ)
      ≤ (1 - δ) * (A.card : ℝ) := by
    have h1d : (0 : ℝ) < 1 - δ := by linarith
    have hge : (1 - δ)⁻¹ ≤ c * Real.log (A.card : ℝ) := by
      rw [inv_le_iff₀ h1d]
      calc (1 : ℝ) ≤ (c * (1 - δ)) * Real.log (A.card : ℝ) := hclogd
        _ = c * Real.log (A.card : ℝ) * (1 - δ) := by ring
    have hinv : (c * Real.log (A.card : ℝ))⁻¹ ≤ 1 - δ := by
      have h := inv_anti₀ (inv_pos.mpr h1d) hge
      rwa [inv_inv] at h
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hfrach : c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ)
      ≤ (A.card : ℝ) / 2 := by
    have hinv : (c * Real.log (A.card : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := by
      have h := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hclog2
      rwa [inv_inv] at h
    rw [hkey]
    calc (A.card : ℝ) * (c * Real.log (A.card : ℝ))⁻¹
        ≤ (A.card : ℝ) * (2 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (A.card : ℝ) / 2 := by rw [div_eq_mul_inv]
  have hAhδ : δ * (A.card : ℝ) ≤ (W.imageAh.card : ℝ) := by
    rw [W.card_imageAh]
    have := W.hAhcard
    linarith [hfracd]
  have hAhh : (A.card : ℝ) / 2 ≤ (W.Ah.card : ℝ) := by
    have := W.hAhcard
    linarith [hfrach]
  -- `P` is proper (from `kP` proper), `P.toFinset` is nonempty, and the
  -- zero coefficient vector is available, so `0 ∈ ϕ_P(P)`.
  have hproper : W.P.Proper :=
    (GAP.proper_smul_iff (by exact_mod_cast W.kpos.ne')).mp W.hproper
  have h0mem : (0 : Fin d → ℤ) ∈ W.imageP := by
    have hne : W.P.toFinset.Nonempty :=
      ⟨0, W.hsub (Finset.mem_union_right _ (Finset.mem_singleton_self 0))⟩
    have hw : ∀ i, 0 < W.P.width i := by
      obtain ⟨p, hp⟩ := hne
      obtain ⟨n, hn, -⟩ := Finset.mem_image.mp hp
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hn
      intro i
      have := (m i).isLt
      omega
    have h0c : (fun _ ↦ (0 : ℕ)) ∈ W.P.coeffs := by
      unfold GAP.coeffs
      apply Finset.mem_image.mpr
      refine ⟨fun i ↦ ⟨0, hw i⟩, Finset.mem_univ _, ?_⟩
      funext i
      rfl
    have hbase : W.P.base ∈ W.P.toFinset := by
      apply Finset.mem_image.mpr
      exact ⟨fun _ ↦ (0 : ℕ), h0c, by simp [GAP.eval]⟩
    have hptc : W.P.ptCoeff W.P.base hbase = fun _ ↦ (0 : ℕ) := by
      have heval : W.P.eval (W.P.ptCoeff W.P.base hbase)
          = W.P.eval (fun _ ↦ (0 : ℕ)) := by
        rw [GAP.eval_ptCoeff]
        simp [GAP.eval]
      exact hproper (W.P.ptCoeff_mem _ _) h0c heval
    unfold SubSumWitness.imageP GAP.ptCoeffImage
    apply Finset.mem_image.mpr
    refine ⟨⟨W.P.base, hbase⟩, Finset.mem_attach _ _, ?_⟩
    funext i
    show ((W.P.ptCoeff W.P.base hbase) i : ℤ) = 0
    rw [hptc]
    rfl
  -- Degenerate regimes are vacuous:
  -- * `C' ≤ 0` makes `γ ≥ (log|A|)^{−1/C'} ≥ 1`, contradicting `γ < 1`;
  -- * `d = 0` forces `|Â| ≤ 1`, contradicting `|Â| ≥ |A|/2 ≥ 3/2`;
  -- * `c' ≤ 0` contradicts `W'.cpos` for the witness of `imageAh − 0`.
  by_cases hC' : C' ≤ 0
  · exfalso
    have hexp' : (0 : ℝ) ≤ -(1 : ℝ) / C' := by
      by_cases h0 : C' = 0
      · simp [h0]
      · rw [div_nonneg_iff]
        exact Or.inr ⟨by norm_num, le_of_lt (lt_of_le_of_ne hC' h0)⟩
    have : (1 : ℝ) ≤ (Real.log (A.card : ℝ)) ^ (-(1 : ℝ) / C') :=
      Real.one_le_rpow hlog1 hexp'
    linarith [hγlog]
  by_cases hd : d = 0
  · subst hd
    exfalso
    have hAh1 : (W.Ah.card : ℝ) ≤ 1 := by
      exact_mod_cast W.card_Ah_le_one
    linarith [hAhh]
  by_cases hc' : c' ≤ 0
  · exfalso
    obtain ⟨⟨W0⟩, -, -⟩ := hIrred.2 W.imageAh 0 (Subset.refl _) hAhδ h0mem
    linarith [W0.cpos]
  push_neg at hC' hc' hd
  -- The main case (`d ≥ 1`, `0 < c'`, `0 < C'`): assume the embedded image
  -- is not in `μ`-convex position and derive the contradiction of
  -- `NonAveraging.not_subsetSum_shift_eq` from a nonzero common subset sum.
  by_contra hconv
  obtain ⟨a₀, ha₀, B₁, B₂, hB₁e, hB₂e, hdisj, hcover, hw₁, hw₂, w, hw0,
    hwb, hws, hvec⟩ := W.not_inConvexPosition_imageAh_split hμ hconv
  suffices hsuff : ∃ v : Fin d → ℤ, v ≠ 0 ∧
      v ∈ GAP.subsetSumsL (B₁.image (· - a₀)) ∧
      v ∈ GAP.subsetSumsL (B₂.image (a₀ - ·)) by
    obtain ⟨v, hv0, hv1, hv2⟩ := hsuff
    rw [GAP.mem_subsetSumsL] at hv1 hv2
    obtain ⟨S₁, hS₁, hS1v⟩ := hv1
    obtain ⟨S₂, hS₂, hS2v⟩ := hv2
    obtain ⟨Ã₁, hÃ₁sub, hÃ₁eq⟩ := Finset.subset_image_iff.mp hS₁
    obtain ⟨Ã₂, hÃ₂sub, hÃ₂eq⟩ := Finset.subset_image_iff.mp hS₂
    have hsum1 : ∑ x ∈ Ã₁, (x - a₀) = v := by
      have h := hS1v
      rw [← hÃ₁eq, Finset.sum_image
        (fun x _ y _ hh ↦ sub_left_injective hh)] at h
      simpa [id_eq] using h
    have hsum2 : ∑ y ∈ Ã₂, (a₀ - y) = v := by
      have h := hS2v
      rw [← hÃ₂eq, Finset.sum_image
        (fun x _ y _ hh ↦ sub_right_injective hh)] at h
      simpa [id_eq] using h
    have hnonempty : Ã₁.Nonempty ∨ Ã₂.Nonempty := by
      by_cases h1 : Ã₁.Nonempty
      · exact Or.inl h1
      · right
        by_cases h2 : Ã₂.Nonempty
        · exact h2
        · exfalso
          rw [Finset.not_nonempty_iff_eq_empty] at h1 h2
          subst h1
          subst h2
          simp at hsum1
          exact hv0 hsum1.symm
    have hNA' : NonAveraging W.imageAh :=
      GAP.nonAveraging_ptCoeffImage _ (NonAveraging.mono W.hAh hNA)
    exact NonAveraging.not_subsetSum_shift_eq hNA' ha₀
      (hÃ₁sub.trans hB₁e) (hÃ₂sub.trans hB₂e) (hdisj.mono hÃ₁sub hÃ₂sub)
      hnonempty (hsum1.trans hsum2.symm)
  -- === The Lemmas 11–14 core ===
  -- It remains to produce a nonzero `v ∈ Σ(B₁ − a₀) ∩ Σ(a₀ − B₂)`.
  -- Irreducibility supplies d-dimensional witnesses `W₁, W₂` for
  -- `B₁ − a₀` and `a₀ − B₂` with `|Pᵢ| ≥ γ|P|`; the balanced combination
  -- `T = Σ w_x·(x − a₀) = Σ w_x·(a₀ − x)` lies in both zonotopes; the
  -- covering lemma (Lemma 14) puts a fat box around `T` inside both
  -- subset-sum sets modulo the GAP lattices `⟨Pᵢ⟩`, and the covolume
  -- bound (Lemmas 11–12) forces `⟨P₁⟩ ∩ ⟨P₂⟩` to meet that box off 0.
  sorry

/-- **First step of Theorem 4** (paper §3.3).  If `A₀ ⊆ ℝ^d` fails to be in
`μ`-convex position, there is a point `a ∈ A₀` such that every closed
halfspace through `a` contains strictly more than `μ |A₀|` points of `A₀`,
and the separating-hyperplane argument
(`exists_balanced_convex_combination`, equation (12)) then produces a convex
combination `Σ c_x (x − a) = 0` with `Σ c_x = 1` and
`c_x ∈ [0, (μ |A₀|)⁻¹]`. -/
theorem exists_balanced_combination_of_not_inConvexPosition {d : ℕ}
    (A₀ : Finset (Fin d → ℝ)) {μ : ℝ} (hμ : 0 < μ)
    (h : ¬ InDeltaConvexPosition A₀ μ) :
    ∃ a ∈ A₀, ∃ c : (Fin d → ℝ) → ℝ,
      (∀ x ∈ A₀, 0 ≤ c x) ∧ (∀ x ∈ A₀, c x ≤ (μ * A₀.card)⁻¹) ∧
      (∑ x ∈ A₀, c x = 1) ∧ (∑ x ∈ A₀, c x • (x - a) = 0) := by
  classical
  rw [InDeltaConvexPosition] at h
  push Not at h
  obtain ⟨a, ha, H⟩ := h
  exact ⟨a, ha, exists_balanced_convex_combination A₀ a μ hμ fun u t ht ↦
    H u t ht⟩

/-- The coordinate embedding `ℤ^d ↪ ℝ^d` is injective, so the real embedded
image `ϕ_P(Â)` has cardinality `|Â|`.  (Used to convert the conclusion of
`exists_balanced_combination_of_not_inConvexPosition` back to integer data.) -/
theorem SubSumWitness.card_imageAh_real {d : ℕ} {c : ℝ}
    {A : Finset (Fin ℓ → ℤ)} (W : SubSumWitness A c d) :
    (W.imageAh.image fun x i ↦ (x i : ℝ)).card = W.Ah.card := by
  have hinj : Function.Injective (fun x : Fin d → ℤ ↦ fun i ↦ (x i : ℝ)) :=
    fun a b h ↦ funext fun i ↦ Int.cast_injective (congrFun h i)
  rw [Finset.card_image_of_injective _ hinj]
  exact GAP.card_ptCoeffImage _ _ _

/-- **The analytic half of Theorem 4** (paper §3.3, up to equation (13)).
If `A₀ ⊆ ℝ^d` is not in `μ`-convex position, there are `a ∈ A₀` and a
partition `A₁ ⊔ A₂ = A₀ ∖ {a}` into disjoint parts, each of size at least
`(μ|A₀| − 2)/2`, together with weights `c_x ∈ [0, (μ|A₀|)⁻¹]`, `Σ c_x = 1`,
such that the weighted displacement sums are opposite:
`Σ_{A₁} c_x • (x − a) = −Σ_{A₂} c_x • (x − a)`.

The remainder of the paper's proof of Theorem 4 applies the discrete John
lemma (Lemma 7) to `A₁ − a` and `a − A₂`, the covolume bounds of Lemmas
11–12, and Minkowski's convex body theorem inside the GAP lattice
(Lemmas 13–14), using `(δ,γ)`-irreducibility, to refine `A₁, A₂` to
nonempty `Ã₁', Ã₂' ⊆ A ∖ {a}` with an *exact* integer relation
`Σ(Ã₁' − a) = Σ(a − Ã₂')`, contradicting `NonAveraging.subsetSum_eq_zero`. -/
theorem not_inConvexPosition_exists_split {d : ℕ} (A₀ : Finset (Fin d → ℝ))
    {μ : ℝ} (hμ : 0 < μ) (h : ¬ InDeltaConvexPosition A₀ μ) :
    ∃ a ∈ A₀, ∃ A₁ A₂ : Finset (Fin d → ℝ),
      A₁ ⊆ A₀.erase a ∧ A₂ ⊆ A₀.erase a ∧ Disjoint A₁ A₂ ∧
      A₁ ∪ A₂ = A₀.erase a ∧
      (μ * A₀.card - 2) / 2 ≤ A₁.card ∧
      (μ * A₀.card - 2) / 2 ≤ A₂.card ∧
      ∃ c : (Fin d → ℝ) → ℝ, (∀ x ∈ A₀, 0 ≤ c x) ∧
        (∀ x ∈ A₀, c x ≤ (μ * A₀.card)⁻¹) ∧ (∑ x ∈ A₀, c x = 1) ∧
        (∑ x ∈ A₁, c x • (x - a)) = -(∑ x ∈ A₂, c x • (x - a)) := by
  obtain ⟨a, ha, c, hc0, hcw, hcsum, hczero⟩ :=
    exists_balanced_combination_of_not_inConvexPosition A₀ hμ h
  have hcardpos : (0:ℝ) < A₀.card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨a, ha⟩)
  have hμc : (0:ℝ) < μ * A₀.card := mul_pos hμ hcardpos
  have hwpos : (0:ℝ) < (μ * A₀.card)⁻¹ := inv_pos.mpr hμc
  obtain ⟨A₁, A₂, hA₁, hA₂, hdisj, hcover, hw₁, hw₂, hvec⟩ :=
    balanced_convex_combination_split hwpos hc0 hcw hcsum hczero
  -- Convert the weight bounds `(1 − 2w)/2 ≤ |Aᵢ|·w` into size bounds
  -- `|Aᵢ| ≥ (μ|A₀| − 2)/2`.
  have heq : (1 - 2 * (μ * A₀.card)⁻¹) / (2 * (μ * A₀.card)⁻¹)
      = (μ * A₀.card - 2) / 2 := by
    rw [div_eq_iff_mul_eq (mul_ne_zero two_ne_zero hwpos.ne'),
      show ((μ * A₀.card - 2) / 2) * (2 * (μ * A₀.card)⁻¹)
          = (μ * A₀.card - 2) * (μ * A₀.card)⁻¹ by ring,
      sub_mul, mul_inv_cancel₀ hμc.ne']
  have cardbd : ∀ {C : Finset (Fin d → ℝ)},
      (1 - 2 * (μ * A₀.card)⁻¹) / 2 ≤ (C.card : ℝ) * (μ * A₀.card)⁻¹ →
      (μ * A₀.card - 2) / 2 ≤ C.card := by
    intro C hle
    have hle' := (div_le_iff₀ hwpos).mpr hle
    rwa [div_div, heq] at hle'
  exact ⟨a, ha, A₁, A₂, hA₁, hA₂, hdisj, hcover, cardbd hw₁, cardbd hw₂,
    c, hc0, hcw, hcsum, hvec⟩

/-- The endpoint of Theorem 4's contradiction: an equality of shifted
subset sums `Σ(Ã₁ − a) = Σ(a − Ã₂)` with disjoint `Ã₁, Ã₂ ⊆ A ∖ {a}`,
at least one of them nonempty, is impossible in a non-averaging set —
`NonAveraging.subsetSum_eq_zero` forces the common value `0`, which is
itself an averaging relation. -/
theorem NonAveraging.not_subsetSum_shift_eq {α : Type*} [DecidableEq α]
    [AddCommGroup α] {A : Finset α} {a : α} {B₁ B₂ : Finset α}
    (hA : NonAveraging A) (ha : a ∈ A)
    (h₁ : B₁ ⊆ A.erase a) (h₂ : B₂ ⊆ A.erase a) (hdisj : Disjoint B₁ B₂)
    (hne : B₁.Nonempty ∨ B₂.Nonempty)
    (hsum : ∑ x ∈ B₁, (x - a) = ∑ y ∈ B₂, (a - y)) : False := by
  have h0 := hA.subsetSum_eq_zero ha h₁ h₂ hdisj hsum
  rcases hne with hne | hne
  · apply hA a ha B₁ h₁ hne
    rw [Finset.sum_sub_distrib, Finset.sum_const, sub_eq_zero] at h0
    exact h0.symm
  · have h : ∑ y ∈ B₂, (a - y) = 0 := hsum ▸ h0
    rw [Finset.sum_sub_distrib, Finset.sum_const, sub_eq_zero] at h
    exact hA a ha B₂ h₂ hne h

/-- The integer form of `not_inConvexPosition_exists_split` for the
embedded image `ϕ_P(Â) ⊆ ℤ^d` of a structure witness: a point
`a₀ ∈ ϕ_P(Â)` and a partition `A₁ ⊔ A₂ = ϕ_P(Â) ∖ {a₀}` into disjoint
parts, each of size `≥ (μ|Â| − 2)/2`, together with weights
`c_x ∈ [0, (μ|Â|)⁻¹]`, `Σ c_x = 1`, whose weighted displacement sums are
opposite.  This is the equation-(13) output transported to `ℤ^d` — the
starting point of the Lemmas 11–14 step of Theorem 4. -/
theorem SubSumWitness.not_inConvexPosition_imageAh_split {d : ℕ} {c : ℝ}
    {A : Finset (Fin ℓ → ℤ)} (W : SubSumWitness A c d) {μ : ℝ} (hμ : 0 < μ)
    (h : ¬ InDeltaConvexPosition
      (W.imageAh.image fun x i ↦ (x i : ℝ)) μ) :
    ∃ a₀ ∈ W.imageAh, ∃ A₁ A₂ : Finset (Fin d → ℤ),
      A₁ ⊆ W.imageAh.erase a₀ ∧ A₂ ⊆ W.imageAh.erase a₀ ∧
      Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = W.imageAh.erase a₀ ∧
      (μ * W.Ah.card - 2) / 2 ≤ (A₁.card : ℝ) ∧
      (μ * W.Ah.card - 2) / 2 ≤ (A₂.card : ℝ) ∧
      ∃ w : (Fin d → ℤ) → ℝ, (∀ x ∈ W.imageAh, 0 ≤ w x) ∧
        (∀ x ∈ W.imageAh, w x ≤ (μ * W.Ah.card)⁻¹) ∧
        (∑ x ∈ W.imageAh, w x = 1) ∧
        (∑ x ∈ A₁, w x • intVec (x - a₀)) =
          -(∑ x ∈ A₂, w x • intVec (x - a₀)) := by
  classical
  set f : (Fin d → ℤ) → (Fin d → ℝ) := fun x i ↦ (x i : ℝ) with hf_def
  have hf : Function.Injective f := fun a b hab ↦
    funext fun i ↦ Int.cast_injective (congrFun hab i)
  obtain ⟨a, ha, A₁, A₂, hA₁e, hA₂e, hdisj, hcover, hw₁, hw₂, c, hc0, hcw,
    hcsum, hvec⟩ := not_inConvexPosition_exists_split _ hμ h
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
  have hA₁sub : A₁ ⊆ W.imageAh.image f :=
    hA₁e.trans (Finset.erase_subset _ _)
  obtain ⟨B₁, hB₁sub, hB₁eq⟩ := Finset.subset_image_iff.mp hA₁sub
  have hA₂sub : A₂ ⊆ W.imageAh.image f :=
    hA₂e.trans (Finset.erase_subset _ _)
  obtain ⟨B₂, hB₂sub, hB₂eq⟩ := Finset.subset_image_iff.mp hA₂sub
  have ha₀₁ : a₀ ∉ B₁ := by
    intro hmem
    have hfmem : f a₀ ∈ A₁ := hB₁eq ▸ Finset.mem_image.mpr ⟨a₀, hmem, rfl⟩
    exact (Finset.mem_erase.mp (hA₁e hfmem)).1 rfl
  have ha₀₂ : a₀ ∉ B₂ := by
    intro hmem
    have hfmem : f a₀ ∈ A₂ := hB₂eq ▸ Finset.mem_image.mpr ⟨a₀, hmem, rfl⟩
    exact (Finset.mem_erase.mp (hA₂e hfmem)).1 rfl
  have hB₁e : B₁ ⊆ W.imageAh.erase a₀ := fun x hx ↦
    Finset.mem_erase.mpr ⟨fun h ↦ ha₀₁ (h ▸ hx), hB₁sub hx⟩
  have hB₂e : B₂ ⊆ W.imageAh.erase a₀ := fun x hx ↦
    Finset.mem_erase.mpr ⟨fun h ↦ ha₀₂ (h ▸ hx), hB₂sub hx⟩
  have hdisj' : Disjoint B₁ B₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    exact (Finset.disjoint_left.mp hdisj
      (hB₁eq ▸ Finset.mem_image.mpr ⟨x, hx₁, rfl⟩))
      (hB₂eq ▸ Finset.mem_image.mpr ⟨x, hx₂, rfl⟩)
  have hcover' : B₁ ∪ B₂ = W.imageAh.erase a₀ := by
    have h1 : (B₁ ∪ B₂).image f = (W.imageAh.erase a₀).image f := by
      rw [Finset.image_union, hB₁eq, hB₂eq, hcover, Finset.image_erase hf]
    have h2 : ∀ s t : Finset (Fin d → ℤ), s.image f = t.image f → s = t := by
      intro s t hst
      ext x
      constructor
      · intro hx
        have hx' : f x ∈ t.image f :=
          hst ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
        obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx'
        rwa [hf hyx] at hy
      · intro hx
        have hx' : f x ∈ s.image f :=
          hst ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
        obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx'
        rwa [hf hyx] at hy
    exact h2 _ _ h1
  have hcard₀ : (W.imageAh.image f).card = W.Ah.card := by
    rw [Finset.card_image_of_injective _ hf, W.card_imageAh]
  have hcB₁ : B₁.card = A₁.card := by
    rw [← hB₁eq, Finset.card_image_of_injective _ hf]
  have hcB₂ : B₂.card = A₂.card := by
    rw [← hB₂eq, Finset.card_image_of_injective _ hf]
  refine ⟨a₀, ha₀, B₁, B₂, hB₁e, hB₂e, hdisj', hcover', ?_, ?_,
    fun x ↦ c (f x), ?_, ?_, ?_, ?_⟩
  · rw [hcard₀] at hw₁
    rwa [hcB₁]
  · rw [hcard₀] at hw₂
    rwa [hcB₂]
  · intro x hx
    exact hc0 _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · intro x hx
    have hx' := hcw _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    rwa [hcard₀] at hx'
  · show ∑ x ∈ W.imageAh, c (f x) = 1
    rw [← Finset.sum_image (fun x _ y _ h ↦ hf h)]
    exact hcsum
  · show ∑ x ∈ B₁, c (f x) • intVec (x - a₀)
        = -(∑ x ∈ B₂, c (f x) • intVec (x - a₀))
    have hfsub : ∀ x : Fin d → ℤ, f x - f a₀ = intVec (x - a₀) := by
      intro x
      funext i
      show (x i : ℝ) - (a₀ i : ℝ) = ((x - a₀) i : ℝ)
      rw [Pi.sub_apply, Int.cast_sub]
    have e1 : ∑ x ∈ B₁, c (f x) • intVec (x - a₀)
        = ∑ y ∈ A₁, c y • (y - f a₀) := by
      rw [← hB₁eq, Finset.sum_image (fun x _ y _ h ↦ hf h)]
      apply Finset.sum_congr rfl
      intro x _
      rw [← hfsub x]
    have e2 : ∑ x ∈ B₂, c (f x) • intVec (x - a₀)
        = ∑ y ∈ A₂, c y • (y - f a₀) := by
      rw [← hB₂eq, Finset.sum_image (fun x _ y _ h ↦ hf h)]
      apply Finset.sum_congr rfl
      intro x _
      rw [← hfsub x]
    rw [e1, e2]
    exact hvec

end Nonaveraging
