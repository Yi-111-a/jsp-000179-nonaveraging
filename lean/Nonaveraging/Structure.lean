import Nonaveraging.ConvexPosition

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
      A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      C ≤ (A.card : ℝ) → ∃ d', Nonempty (SubSumWitness A c d') := by
  obtain ⟨c, d, C, hc, -, hC, hcor⟩ := cfp_structure_cor ℓ hβ
  refine ⟨c, C, hc, hC, fun A B hsub hB hCm ↦ ?_⟩
  obtain ⟨Â, d', P, hÂsub, hÂcard, -, -, hsub0, A', hA'sub, hA'card, k, hkpos,
    hkle, t, htrans, hprop⟩ := hcor A B hsub hB hCm
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
    (hγδ : γ ≤ δ ^ K)
    {A : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ}
    (hA : NonAveraging A) (hsub : A ⊆ B.toFinset)
    (hB : (B.card : ℝ) ≤ (A.card : ℝ) ^ β)
    (hγA : (A.card : ℝ) ^ (-(1 : ℝ) / 3) ≤ γ) :
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
  sorry

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
      NonAveraging A → A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      Irreducible W c' δ γ →
      (Real.log (A.card : ℝ)) ^ (-(1 : ℝ) / C') ≤ γ →
      N ≤ A.card →
      InDeltaConvexPosition
        (W.imageAh.image fun x i ↦ (x i : ℝ)) μ := by
  sorry

end Nonaveraging
