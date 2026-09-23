import Nonaveraging.ConvexPosition
import Nonaveraging.GeoNumbers
import Nonaveraging.DiscreteJohn

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

/-- Dilation by `1` is the identity on GAPs.  Used to bridge the
`SubSumWitness` pointwise-dilation convention `k • P` with the
coefficient-width scaling `P.widthScale k` returned by
`cfp_structure_cor` (take `k = 1` on the widened progression). -/
theorem one_smul' : (1 : ℤ) • P = P := by
  show GAP.mk ((1 : ℤ) • P.base) (fun i ↦ (1 : ℤ) • P.step i) P.width =
    GAP.mk P.base P.step P.width
  rw [GAP.mk.injEq]
  exact ⟨_root_.one_smul _ _, funext fun i ↦ _root_.one_smul _ _, rfl⟩

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
  -- `SubSumWitness` stores the pointwise dilation `k • P`, while
  -- `cfp_structure_cor` supplies the coefficient-width scaling
  -- `P.widthScale k`.  Take the widened progression itself as the witness
  -- GAP with multiplicity `1`: `(1 : ℕ) • (P.widthScale k) = P.widthScale k`
  -- (`GAP.one_smul'`), `P ⊆ P.widthScale k` coefficientwise since `1 ≤ k`
  -- (`GAP.toFinset_subset_widthScale`), and `1 ≤ k ≤ c·s(A)`.
  have hQ : (1 : ℕ) • (P.widthScale k) = P.widthScale k := by
    rw [GAP.nsmul_eq_zsmul, Nat.cast_one]
    exact GAP.one_smul' _
  refine ⟨d', ⟨Â, A', P.widthScale k, 1, t, hc, zero_lt_one, ?_,
    hÂsub, hA'sub, hA'card, hÂcard, ?_, ?_, ?_⟩⟩
  · rw [Nat.cast_one]
    exact (by exact_mod_cast hkpos : (1 : ℝ) ≤ (k : ℝ)).trans hkle
  · exact hsub0.trans (P.toFinset_subset_widthScale hkpos)
  · rw [hQ]; exact htrans
  · rw [hQ]; exact hprop

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

/-- The negated GAP `-P = {-b - Σ nᵢ sᵢ}` (same widths). -/
def neg {d : ℕ} (P : GAP ℓ d) : GAP ℓ d :=
  ⟨-P.base, fun i ↦ -P.step i, P.width⟩

theorem eval_neg {d : ℕ} (P : GAP ℓ d) (n : Fin d → ℕ) :
    P.neg.eval n = -P.eval n := by
  show (-P.base) + ∑ i, (n i : ℤ) • (-P.step i)
      = -(P.base + ∑ i, (n i : ℤ) • P.step i)
  have hsum : (∑ i, (n i : ℤ) • (-P.step i))
      = -(∑ i, (n i : ℤ) • P.step i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ smul_neg _ _
  rw [hsum, neg_add]

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
    P.neg.translate (-t) = (P.translate t).neg := by
  show (⟨-t + -P.base, fun i ↦ -P.step i, P.width⟩ : GAP ℓ d)
      = ⟨-(t + P.base), fun i ↦ -P.step i, P.width⟩
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.neg_apply, neg_add]

theorem smul_neg {d : ℕ} (P : GAP ℓ d) (k : ℤ) :
    k • P.neg = (k • P).neg := by
  show (⟨k • (-P.base), fun i ↦ k • (-P.step i), P.width⟩ : GAP ℓ d)
      = ⟨-(k • P.base), fun i ↦ -(k • P.step i), P.width⟩
  congr 1
  · exact _root_.smul_neg k P.base
  · funext i
    exact _root_.smul_neg k (P.step i)

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
      have key : (∑ a ∈ S', id (Neg.neg a)) = -(S'.sum id) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun a _ ↦ rfl
      rw [key, neg_neg]
  · rintro ⟨v, hv, hvx⟩
    rw [mem_subsetSumsL] at hv
    obtain ⟨T, hT, rfl⟩ := hv
    refine ⟨T.image Neg.neg, Finset.image_mono Neg.neg hT, ?_⟩
    rw [Finset.sum_image (fun x _ y _ h ↦ neg_injective h)]
    show (∑ x ∈ T, id (-x)) = x
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
  t := -W.t
  cpos := W.cpos
  kpos := W.kpos
  hk := by
    rw [Finset.card_image_of_injective _ neg_injective]
    exact W.hk
  hAh := Finset.image_mono Neg.neg W.hAh
  hA' := Finset.image_mono Neg.neg W.hA'
  hA'card := by
    rw [Finset.card_image_of_injective _ neg_injective,
      Finset.card_image_of_injective _ neg_injective]
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
    exact Finset.image_mono Neg.neg W.hsub
  htranslate := by
    show (((W.k : ℤ) • W.P.neg).translate (-W.t)).toFinset
        ⊆ GAP.subsetSumsL (W.A'.image Neg.neg)
    rw [GAP.smul_neg, GAP.translate_neg, GAP.toFinset_neg,
      GAP.subsetSumsL_neg]
    exact Finset.image_mono Neg.neg W.htranslate
  hproper := by
    show ((W.k : ℤ) • W.P.neg).Proper
    rw [GAP.smul_neg]
    exact GAP.proper_neg.mpr W.hproper

theorem nonempty_neg (W : SubSumWitness A c d) :
    Nonempty (SubSumWitness (A.image Neg.neg) c d) :=
  ⟨W.neg⟩

theorem image_neg_neg {B : Finset (Fin ℓ → ℤ)} :
    (B.image Neg.neg).image Neg.neg = B := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ⟨z, hz, rfl⟩, hax⟩
    rw [← hax, neg_neg]
    exact hz
  · intro hx
    exact ⟨-x, ⟨x, hx, rfl⟩, neg_neg x⟩

theorem nonempty_of_neg {B : Finset (Fin ℓ → ℤ)} {d' : ℕ}
    (h : Nonempty (SubSumWitness (B.image Neg.neg) c d')) :
    Nonempty (SubSumWitness B c d') := by
  obtain ⟨W'⟩ := h
  have W'' := W'.neg
  rw [image_neg_neg] at W''
  exact ⟨W''⟩

end SubSumWitness

/-- Subset-sum dimension is invariant under reflection. -/
theorem SubSumDim_neg {ℓ : ℕ} {A : Finset (Fin ℓ → ℤ)} {c : ℝ} :
    SubSumDim (A.image Neg.neg) c = SubSumDim A c := by
  unfold SubSumDim
  congr 1
  ext d'
  exact ⟨fun h ↦ SubSumWitness.nonempty_of_neg h,
    fun h ↦ h.elim fun W ↦ ⟨W.neg⟩⟩

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

/-! ### Machinery for the Lemmas 11–14 step of Theorem 4

The helpers below supply the first moves of the paper's proof of
Theorem 4 (arXiv:2410.14624v2, §3.2) once the split
`ϕ_P(Â) ∖ {a₀} = B₁ ⊔ B₂` of equation (13) has been produced:

* `GAP.lattice` — the lattice `⟨P⟩` generated by the steps of a GAP;
* `smul_sum_mem_zonotope_image_sub` / `_const_sub` — the rescaled balanced
  displacement `r • Σ_x w_x • (x ∓ a₀)` lies in the zonotope of `B₁ − a₀`,
  resp. `a₀ − B₂` (paper: `z₁ = z₂ ∈ 𝒵_{A₁−a} ∩ 𝒵_{a−A₂}`);
* `exists_subset_sum_int_close` — the Lemma-13 rounding
  (`exists_subset_sum_sub_le_int`) transported back across the images;
* `Irreducible.exists_witness_image_sub` / `_const_sub` — the first half
  of Lemma 11 packaged: a large `A' ⊆ ϕ_P(Â)` shifted by `x ∈ ϕ_P(P)` has
  subset-sum dimension `d` and a `d`-dimensional witness `W'` with
  `|P'| ≥ γ |P|`;
* `SubSumWitness.subsetSumsL_superset` / `card_subsetSumsL_ge` — the
  `Σ(X) ⊇ kP + t` inclusion and its cardinality consequence;
* `GAP.subsetSumsL_sdiff_add_subset` — the
  `Σ(X ∖ Y) + Σ(Y) ⊆ Σ(X)` decomposition used to place
  `Σ(Ā₁ ∖ A₁') + (k₁P₁ + q₁)` inside `Σ(B₁ − a₀)` in the paper. -/

namespace GAP

variable {d : ℕ} (P : GAP ℓ d)

/-- The lattice `⟨P⟩` generated by the step vectors of `P`, as a
`ℤ`-submodule of `ℤ^ℓ`. -/
def lattice : Submodule ℤ (Fin ℓ → ℤ) := Submodule.span ℤ (Set.range P.step)

theorem step_mem_lattice (i : Fin d) : P.step i ∈ P.lattice :=
  Submodule.subset_span ⟨i, rfl⟩

theorem eval_sub_base_mem_lattice (n : Fin d → ℕ) :
    P.eval n - P.base ∈ P.lattice := by
  have e : P.eval n - P.base = ∑ i, (n i : ℤ) • P.step i := by
    show P.base + ∑ i, (n i : ℤ) • P.step i - P.base = _
    rw [add_sub_cancel_left]
  rw [e]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (P.step_mem_lattice i)

/-- The difference of two points of a GAP lies in its lattice. -/
theorem sub_mem_lattice {x y : Fin ℓ → ℤ}
    (hx : x ∈ P.toFinset) (hy : y ∈ P.toFinset) : x - y ∈ P.lattice := by
  obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hy
  have e : P.eval n - P.eval m = ∑ i, ((n i : ℤ) - (m i : ℤ)) • P.step i := by
    show P.base + ∑ i, (n i : ℤ) • P.step i
        - (P.base + ∑ i, (m i : ℤ) • P.step i) = _
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ (sub_smul _ _ _).symm
  rw [e]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (P.step_mem_lattice i)

/-- The lattice of a scaled GAP sits inside the original lattice:
`⟨kP⟩ ⊆ ⟨P⟩`. -/
theorem lattice_smul_le (k : ℤ) : (k • P).lattice ≤ P.lattice := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  show (k : ℤ) • P.step i ∈ P.lattice
  exact Submodule.smul_mem _ _ (P.step_mem_lattice i)

/-- Translating a GAP leaves its lattice unchanged: `⟨P + t⟩ = ⟨P⟩`. -/
theorem lattice_translate (t : Fin ℓ → ℤ) :
    (P.translate t).lattice = P.lattice := rfl

/-- Negating a GAP leaves its lattice unchanged: `⟨−P⟩ = ⟨P⟩`. -/
theorem lattice_neg : P.neg.lattice = P.lattice := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    show -P.step i ∈ P.lattice
    exact Submodule.neg_mem _ (P.step_mem_lattice i)
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    have e : P.step i = -(-P.step i) := (neg_neg _).symm
    rw [e]
    exact Submodule.neg_mem _ (P.neg.step_mem_lattice i)

/-- The point set of a scaled GAP is the image under `k • ·`. -/
theorem toFinset_smul (k : ℤ) : (k • P).toFinset = P.toFinset.image (k • ·) := by
  have hc : (k • P).coeffs = P.coeffs := rfl
  show (k • P).coeffs.image (k • P).eval
      = (P.coeffs.image P.eval).image (fun x ↦ k • x)
  rw [hc, Finset.image_image]
  exact Finset.image_congr fun n _ ↦ eval_smul P k n

/-- Negating a GAP preserves the cardinality of its point set. -/
theorem card_toFinset_neg {d : ℕ} (P : GAP ℓ d) :
    P.neg.toFinset.card = P.toFinset.card := by
  rw [toFinset_neg]
  exact Finset.card_image_of_injective _ neg_injective

/-- Coordinatewise bound on differences of points of the coefficient box:
`|(x − y)ᵢ| ≤ wᵢ` for `x, y ∈ ∏[0, wᵢ)`. -/
theorem abs_sub_apply_le_width {x y : Fin d → ℤ}
    (hx : x ∈ P.coeffBox.toFinset) (hy : y ∈ P.coeffBox.toFinset)
    (i : Fin d) : |(((x - y) i : ℤ) : ℝ)| ≤ (P.width i : ℝ) := by
  have hx' := Finset.mem_Ico.mp
    (show x i ∈ Finset.Ico (0 : ℤ) (P.width i) from
      GAP.Box.mem_toFinset.mp hx i)
  have hy' := Finset.mem_Ico.mp
    (show y i ∈ Finset.Ico (0 : ℤ) (P.width i) from
      GAP.Box.mem_toFinset.mp hy i)
  have e : (((x - y) i : ℤ) : ℝ) = (x i : ℝ) - (y i : ℝ) := by
    rw [Pi.sub_apply, Int.cast_sub]
  have hx0' : (0 : ℝ) ≤ (x i : ℝ) := by exact_mod_cast hx'.1
  have hxw' : (x i : ℝ) < (P.width i : ℝ) := by exact_mod_cast hx'.2
  have hy0' : (0 : ℝ) ≤ (y i : ℝ) := by exact_mod_cast hy'.1
  have hyw' : (y i : ℝ) < (P.width i : ℝ) := by exact_mod_cast hy'.2
  rw [e, abs_le]
  constructor <;> linarith

/-- If `Y ⊆ X`, a sum of a subset sum of `X ∖ Y` and a subset sum of `Y`
is a subset sum of `X`: `Σ(X ∖ Y) + Σ(Y) ⊆ Σ(X)`. -/
theorem subsetSumsL_sdiff_add_subset {X Y : Finset (Fin ℓ → ℤ)} (hY : Y ⊆ X)
    {u v : Fin ℓ → ℤ} (hu : u ∈ GAP.subsetSumsL (X \ Y))
    (hv : v ∈ GAP.subsetSumsL Y) : u + v ∈ GAP.subsetSumsL X := by
  have h := GAP.subsetSumsL_add Finset.sdiff_disjoint hu hv
  rwa [Finset.sdiff_union_of_subset hY] at h

end GAP

/-- The rescaled weighted displacement `r • Σ_{x ∈ S} w_x • (x − a₀)`
lies in the zonotope of the real image of `S − a₀`: the rescaled weights
`r·w_x ∈ [0,1]` serve as the zonotope coefficients after `Finset.image`
reindexing.  (Paper: `z₁ ∈ 𝒵_{A₁ − a}`.) -/
theorem smul_sum_mem_zonotope_image_sub {d : ℕ} (S : Finset (Fin d → ℤ))
    (a₀ : Fin d → ℤ) {w : (Fin d → ℤ) → ℝ} {r : ℝ} (hr : 0 < r)
    (hw0 : ∀ x ∈ S, 0 ≤ w x) (hwb : ∀ x ∈ S, w x ≤ r⁻¹) :
    r • (∑ x ∈ S, w x • intVec (x - a₀)) ∈
      zonotope ((S.image (· - a₀)).image intVec) := by
  classical
  rw [mem_zonotope]
  have hfl : ∀ x : Fin d → ℤ,
      (fun i ↦ a₀ i + ⌊intVec (x - a₀) i⌋) = x := by
    intro x
    funext i
    have h1 : ⌊intVec (x - a₀) i⌋ = (x - a₀) i := by
      show ⌊(((x - a₀) i : ℤ) : ℝ)⌋ = _
      exact Int.floor_intCast _
    rw [h1, Pi.sub_apply]
    ring
  refine ⟨fun y ↦ r * w (fun i ↦ a₀ i + ⌊y i⌋), fun y hy ↦ ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    show r * w (fun i ↦ a₀ i + ⌊intVec (x - a₀) i⌋) ∈ Set.Icc 0 1
    rw [hfl x]
    exact ⟨mul_nonneg hr.le (hw0 x hx),
      (mul_le_mul_of_nonneg_left (hwb x hx) hr.le).trans
        (le_of_eq (mul_inv_cancel₀ hr.ne'))⟩
  · rw [Finset.sum_image (fun x _ y _ h ↦ intVec_injective h),
      Finset.sum_image (fun x _ y _ h ↦ sub_left_injective h),
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    show r • (w x • intVec (x - a₀))
        = (r * w (fun i ↦ a₀ i + ⌊intVec (x - a₀) i⌋)) • intVec (x - a₀)
    rw [hfl x]
    exact (mul_smul r (w x) _).symm

/-- The reflected version for `a₀ − S`: `r • Σ_{x ∈ S} w_x • (a₀ − x)` lies
in the zonotope of the real image of `a₀ − S`.  (Paper: `z₂ ∈ 𝒵_{a−A₂}`.) -/
theorem smul_sum_mem_zonotope_image_const_sub {d : ℕ} (S : Finset (Fin d → ℤ))
    (a₀ : Fin d → ℤ) {w : (Fin d → ℤ) → ℝ} {r : ℝ} (hr : 0 < r)
    (hw0 : ∀ x ∈ S, 0 ≤ w x) (hwb : ∀ x ∈ S, w x ≤ r⁻¹) :
    r • (∑ x ∈ S, w x • intVec (a₀ - x)) ∈
      zonotope ((S.image (a₀ - ·)).image intVec) := by
  classical
  rw [mem_zonotope]
  have hfl : ∀ x : Fin d → ℤ,
      (fun i ↦ a₀ i - ⌊intVec (a₀ - x) i⌋) = x := by
    intro x
    funext i
    have h1 : ⌊intVec (a₀ - x) i⌋ = (a₀ - x) i := by
      show ⌊(((a₀ - x) i : ℤ) : ℝ)⌋ = _
      exact Int.floor_intCast _
    rw [h1, Pi.sub_apply]
    ring
  refine ⟨fun y ↦ r * w (fun i ↦ a₀ i - ⌊y i⌋), fun y hy ↦ ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    show r * w (fun i ↦ a₀ i - ⌊intVec (a₀ - x) i⌋) ∈ Set.Icc 0 1
    rw [hfl x]
    exact ⟨mul_nonneg hr.le (hw0 x hx),
      (mul_le_mul_of_nonneg_left (hwb x hx) hr.le).trans
        (le_of_eq (mul_inv_cancel₀ hr.ne'))⟩
  · rw [Finset.sum_image (fun x _ y _ h ↦ intVec_injective h),
      Finset.sum_image (fun x _ y _ h ↦ sub_right_injective h),
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    show r • (w x • intVec (a₀ - x))
        = (r * w (fun i ↦ a₀ i - ⌊intVec (a₀ - x) i⌋)) • intVec (a₀ - x)
    rw [hfl x]
    exact (mul_smul r (w x) _).symm

/-- Lemma-13 rounding pulled back across an injective image: if
`z ∈ 𝒵_{intVec(f(S))}` with `|(f x)ᵢ| ≤ wdᵢ` for `x ∈ S`, then some
`S' ⊆ f(S)` has `|(Σ S')ᵢ − zᵢ| ≤ d·wdᵢ` coordinatewise. -/
theorem exists_subset_sum_int_close {d : ℕ} {S : Finset (Fin d → ℤ)}
    {f : (Fin d → ℤ) → Fin d → ℤ} (hf : Function.Injective f)
    {z : Fin d → ℝ} {wd : Fin d → ℝ}
    (hz : z ∈ zonotope ((S.image f).image intVec))
    (hwd : ∀ i, 0 ≤ wd i)
    (hb : ∀ x ∈ S, ∀ i, |((f x) i : ℝ)| ≤ wd i) :
    ∃ S' ⊆ S.image f, ∀ i,
      |(((S'.sum id) i : ℤ) : ℝ) - z i| ≤ (d : ℝ) * wd i := by
  classical
  obtain ⟨S'', hS'', hclose⟩ := exists_subset_sum_sub_le hz hwd (fun a ha ↦ by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hb x hx)
  obtain ⟨S', hS'sub, hS'eq⟩ := Finset.subset_image_iff.mp hS''
  refine ⟨S', hS'sub, fun i ↦ ?_⟩
  have hsum : ((S'.sum id) i : ℝ) = (∑ b ∈ S'', b) i := by
    have e1 : (S'.sum id) i = ∑ v ∈ S', (v i : ℤ) := by
      simp only [Finset.sum_apply, id_eq]
    rw [e1, Int.cast_sum, ← hS'eq, Finset.sum_apply,
      Finset.sum_image (fun x _ y _ h ↦ intVec_injective h)]
    exact Finset.sum_congr rfl fun v _ ↦ rfl
  rw [hsum]
  exact hclose i

namespace SubSumWitness

variable {d : ℕ} {c : ℝ} {X : Finset (Fin ℓ → ℤ)} (W : SubSumWitness X c d)

/-- `P` is proper: `kP` is proper and scaling by `k ≠ 0` preserves
properness. -/
theorem proper : W.P.Proper :=
  (GAP.proper_smul_iff (by exact_mod_cast W.kpos.ne')).mp W.hproper

/-- `Σ(X)` contains the translate `kP + t` of the scaled witness GAP
(via `A' ⊆ Â ⊆ X`). -/
theorem subsetSumsL_superset :
    ((W.k • W.P).translate W.t).toFinset ⊆ GAP.subsetSumsL X :=
  W.htranslate.trans (GAP.subsetSumsL_mono (W.hA'.trans W.hAh))

/-- `|Σ(X)| ≥ |P|`: subset sums are at least as numerous as the proper
GAP's points. -/
theorem card_subsetSumsL_ge : W.P.toFinset.card ≤ (GAP.subsetSumsL X).card := by
  have hcard : ((W.k • W.P).translate W.t).toFinset.card =
      ∏ i, W.P.width i := by
    rw [GAP.card_toFinset_translate,
      GAP.card_toFinset_of_proper _ W.hproper]
    exact Finset.prod_congr rfl fun i _ ↦ rfl
  rw [← GAP.card_toFinset_of_proper _ W.proper] at hcard
  rw [← hcard]
  exact Finset.card_le_card W.subsetSumsL_superset

end SubSumWitness

/-- **Lemma 11, first half**: irreducibility applied to a large subset
`A' ⊆ ϕ_P(Â)` shifted by `x ∈ ϕ_P(P)` produces a `d`-dimensional witness
`W₁` for `A' − x` with `|P₁| ≥ γ |P|`. -/
theorem Irreducible.exists_witness_image_sub {d : ℕ} {c c' δ γ : ℝ}
    {A : Finset (Fin ℓ → ℤ)} {W : SubSumWitness A c d}
    (h : Irreducible W c' δ γ) {A' : Finset (Fin d → ℤ)}
    (hA' : A' ⊆ W.imageAh) (hcard : δ * (A.card : ℝ) ≤ (A'.card : ℝ))
    {x : Fin d → ℤ} (hx : x ∈ W.imageP) :
    ∃ W₁ : SubSumWitness (A'.image (· - x)) c' d,
      SubSumDim (A'.image (· - x)) c' = d ∧
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₁.P.toFinset.card : ℝ) := by
  obtain ⟨hne, hdim, hbound⟩ := h.2 A' x hA' hcard hx
  obtain ⟨W₁⟩ := hne
  exact ⟨W₁, hdim, hbound W₁⟩

/-- The reflected version for `x − A'`: since `x − A' = −(A' − x)`, both
the subset-sum dimension and the witness-cardinality bound transport
across negation (`SubSumDim_neg`, `SubSumWitness.neg`,
`GAP.card_toFinset_neg`). -/
theorem Irreducible.exists_witness_image_const_sub {d : ℕ} {c c' δ γ : ℝ}
    {A : Finset (Fin ℓ → ℤ)} {W : SubSumWitness A c d}
    (h : Irreducible W c' δ γ) {A' : Finset (Fin d → ℤ)}
    (hA' : A' ⊆ W.imageAh) (hcard : δ * (A.card : ℝ) ≤ (A'.card : ℝ))
    {x : Fin d → ℤ} (hx : x ∈ W.imageP) :
    ∃ W₂ : SubSumWitness (A'.image (x - ·)) c' d,
      SubSumDim (A'.image (x - ·)) c' = d ∧
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₂.P.toFinset.card : ℝ) := by
  obtain ⟨W₁, hdim, hbound⟩ := h.exists_witness_image_sub hA' hcard hx
  have hcong : (A'.image (· - x)).image Neg.neg = A'.image (x - ·) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro a _
    show -(a - x) = x - a
    exact neg_sub a x
  rw [← hcong]
  refine ⟨W₁.neg, SubSumDim_neg.trans hdim, ?_⟩
  show (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₁.P.neg.toFinset.card : ℝ)
  rw [GAP.card_toFinset_neg]
  exact hbound

/-! ### Nondegeneracy of minimal-dimension witnesses

A `width 1` step never contributes to a GAP's point set (its coefficient
is forced to `0`), so a structure witness whose GAP has such a step drops
to a genuinely lower-dimensional witness (`GAP.dropStep`,
`SubSumWitness.dropTrivialStep`).  At the minimal subset-sum dimension
this yields `2 ≤ P.width i` at every coordinate; combined with `P.Proper`
(available from `kP` proper) it also gives `P.step i ≠ 0`
(`SubSumWitness.step_ne_zero`).  We also record the `⟨P⟩`-membership
bookkeeping used by the paper's eq. (15): `0 ∈ P` puts `P.toFinset`,
`Â`, `A'`, `Σ(A')` and the translate `t` all inside `⟨P⟩`
(`SubSumWitness.t_mem_gapLattice`).

*Caveat.*  Full `ℤ`-linear independence of `P.step` — equivalently
`(gapLattice P).index ≠ 0` — does **not** follow from minimality in this
formalization: a dependent-step GAP can be proper and yet possess no
lower-dimensional structure witness, because the two conditions on a
witness pull in opposite directions (`Â ⊆ P.toFinset` needs large
widths, while `kP + t ⊆ Σ(A')` needs a small point set).  See the
residual comment at `embedded_in_mu_convex_position`. -/

namespace GAP

/-- Delete the `i₀`-th step of a `GAP ℓ (d+1)`.  When `P.width i₀ = 1`
the point set is unchanged (`GAP.toFinset_dropStep`). -/
private def dropStep {d : ℕ} (P : GAP ℓ (d + 1)) (i₀ : Fin (d + 1)) :
    GAP ℓ d where
  base := P.base
  step := fun j ↦ P.step (i₀.succAbove j)
  width := fun j ↦ P.width (i₀.succAbove j)

/-- Evaluating the dropped GAP is evaluating `P` with coefficient `0`
inserted at `i₀`. -/
private theorem eval_dropStep {d : ℕ} (P : GAP ℓ (d + 1))
    (i₀ : Fin (d + 1)) (m : Fin d → ℕ) :
    (P.dropStep i₀).eval m = P.eval (Fin.insertNth i₀ 0 m) := by
  generalize hn : (Fin.insertNth i₀ 0 m : Fin (d + 1) → ℕ) = n
  show P.base + ∑ j, (m j : ℤ) • P.step (i₀.succAbove j)
      = P.base + ∑ j, (n j : ℤ) • P.step j
  congr 1
  rw [Fin.sum_univ_succAbove
    (fun j : Fin (d + 1) ↦ (n j : ℤ) • P.step j) i₀]
  have hi₀ : n i₀ = 0 := by rw [← hn, Fin.insertNth_apply_same]
  rw [hi₀, Nat.cast_zero, zero_smul, zero_add]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [← hn, Fin.insertNth_apply_succAbove]

/-- Coefficient tuples of `P` that vanish at `i₀` are exactly the
coefficient tuples of the dropped GAP. -/
private theorem insertNth_mem_coeffs {d : ℕ} {P : GAP ℓ (d + 1)}
    {i₀ : Fin (d + 1)} (hw : 0 < P.width i₀) {m : Fin d → ℕ} :
    Fin.insertNth i₀ 0 m ∈ P.coeffs ↔ m ∈ (P.dropStep i₀).coeffs := by
  rw [mem_coeffs, mem_coeffs]
  constructor
  · intro h j
    have h' := h (i₀.succAbove j)
    rwa [Fin.insertNth_apply_succAbove] at h'
  · intro h j
    rcases eq_or_ne j i₀ with rfl | hj
    · rw [Fin.insertNth_apply_same]
      exact hw
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq_iff.mpr hj
      rw [Fin.insertNth_apply_succAbove]
      exact h k

/-- When `width i₀ = 1` every coefficient tuple vanishes at `i₀`, so
evaluation factors through the dropped GAP. -/
private theorem eval_eq_eval_dropStep {d : ℕ} {P : GAP ℓ (d + 1)}
    {i₀ : Fin (d + 1)} (hw : P.width i₀ = 1) {n : Fin (d + 1) → ℕ}
    (hn : n ∈ P.coeffs) :
    P.eval n = (P.dropStep i₀).eval (fun j ↦ n (i₀.succAbove j)) := by
  have h0 : n i₀ = 0 := by
    have h := coeff_mem_width hn i₀
    omega
  show P.base + ∑ j, (n j : ℤ) • P.step j
      = P.base + ∑ j, (n (i₀.succAbove j) : ℤ) • P.step (i₀.succAbove j)
  congr 1
  rw [Fin.sum_univ_succAbove (fun j : Fin (d + 1) ↦ (n j : ℤ) • P.step j)
    i₀, h0, Nat.cast_zero, zero_smul, zero_add]

/-- Dropping a `width 1` step leaves the point set unchanged. -/
private theorem toFinset_dropStep {d : ℕ} (P : GAP ℓ (d + 1))
    {i₀ : Fin (d + 1)} (hw : P.width i₀ = 1) :
    (P.dropStep i₀).toFinset = P.toFinset := by
  ext x
  simp only [toFinset, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨Fin.insertNth i₀ 0 m,
      (insertNth_mem_coeffs (P := P) (by omega)).mpr hm,
      (eval_dropStep P i₀ m).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨fun j ↦ n (i₀.succAbove j),
      mem_coeffs.mpr fun j ↦ coeff_mem_width hn (i₀.succAbove j),
      (eval_eq_eval_dropStep hw hn).symm⟩

/-- Dropping a step commutes with dilation (definitionally). -/
private theorem dropStep_smul {d : ℕ} (P : GAP ℓ (d + 1))
    (i₀ : Fin (d + 1)) (k : ℤ) :
    (k • P).dropStep i₀ = k • (P.dropStep i₀) := rfl

/-- Dropping a step commutes with translation (definitionally). -/
private theorem dropStep_translate {d : ℕ} (P : GAP ℓ (d + 1))
    (i₀ : Fin (d + 1)) (t : Fin ℓ → ℤ) :
    (P.translate t).dropStep i₀ = (P.dropStep i₀).translate t := rfl

/-- Properness is preserved by dropping a trivial step. -/
private theorem proper_dropStep {d : ℕ} {P : GAP ℓ (d + 1)}
    {i₀ : Fin (d + 1)} (hw : P.width i₀ = 1) (hP : P.Proper) :
    (P.dropStep i₀).Proper := by
  intro m₁ hm₁ m₂ hm₂ h
  rw [eval_dropStep, eval_dropStep] at h
  have h1 := hP ((insertNth_mem_coeffs (by omega)).mpr hm₁)
    ((insertNth_mem_coeffs (by omega)).mpr hm₂) h
  funext j
  have h2 := congrFun h1 (i₀.succAbove j)
  rwa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at h2

end GAP

namespace SubSumWitness

/-- A structure witness whose GAP has a `width 1` step drops to a
lower-dimensional witness: the trivial step contributes nothing to
`P.toFinset`, to `kP`, or to properness. -/
private theorem dropTrivialStep {d : ℕ} {c : ℝ} {X : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness X c (d + 1)) {i₀ : Fin (d + 1)}
    (hw : W.P.width i₀ = 1) : Nonempty (SubSumWitness X c d) := by
  refine ⟨{ Ah := W.Ah, A' := W.A', P := W.P.dropStep i₀, k := W.k,
            t := W.t, cpos := W.cpos, kpos := W.kpos, hk := W.hk,
            hAh := W.hAh, hA' := W.hA', hA'card := W.hA'card,
            hAhcard := W.hAhcard, hsub := ?_, htranslate := ?_,
            hproper := ?_ }⟩
  · rw [GAP.toFinset_dropStep W.P hw]
    exact W.hsub
  · have hdef : (W.k • W.P.dropStep i₀).translate W.t
        = ((W.k • W.P).translate W.t).dropStep i₀ := rfl
    have hw' : ((W.k • W.P).translate W.t).width i₀ = 1 := hw
    rw [hdef, GAP.toFinset_dropStep _ hw']
    exact W.htranslate
  · have hdef : W.k • W.P.dropStep i₀ = (W.k • W.P).dropStep i₀ := rfl
    rw [hdef]
    exact GAP.proper_dropStep (show (W.k • W.P).width i₀ = 1 from hw)
      W.hproper

/-- `0 ∈ P.toFinset`, from `Ah ∪ {0} ⊆ P`. -/
private theorem zero_mem_toFinset {d : ℕ} {c : ℝ} {X : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness X c d) : (0 : Fin ℓ → ℤ) ∈ W.P.toFinset :=
  W.hsub (Finset.mem_union_right _ (Finset.mem_singleton_self 0))

/-- A minimal-dimension witness has `2 ≤ width` at every coordinate: a
`width 0` step would make `P` empty (contradicting `0 ∈ P`) and a
`width 1` step could be deleted, contradicting `SubSumDim = d`. -/
private theorem two_le_width {d : ℕ} {c : ℝ} {X : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness X c d) (hdim : SubSumDim X c = d) (i : Fin d) :
    2 ≤ W.P.width i := by
  have hpos : 0 < W.P.width i := by
    obtain ⟨n, hn, -⟩ := Finset.mem_image.mp W.zero_mem_toFinset
    have h := GAP.mem_coeffs.mp hn i
    omega
  rcases d with _ | d'
  · exact i.elim0
  · have hne : W.P.width i ≠ 1 := by
      intro hw
      have hle := subSumDim_le (W.dropTrivialStep hw)
      omega
    omega

/-- Steps of a minimal-dimension witness are nonzero: otherwise the
coefficient tuples `0` and `eⱼ` would collide, contradicting
`P.Proper`. -/
private theorem step_ne_zero {d : ℕ} {c : ℝ} {X : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness X c d) (hdim : SubSumDim X c = d) (j : Fin d) :
    W.P.step j ≠ 0 := by
  intro hs
  have hw : ∀ i, 2 ≤ W.P.width i := fun i ↦ W.two_le_width hdim i
  have h0 : (0 : Fin d → ℕ) ∈ W.P.coeffs :=
    GAP.mem_coeffs.mpr fun i ↦ by
      have := hw i
      simp only [Pi.zero_apply]
      omega
  have he : Function.update (0 : Fin d → ℕ) j 1 ∈ W.P.coeffs :=
    GAP.mem_coeffs.mpr fun i ↦ by
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self]
        have := hw i; omega
      · rw [Function.update_of_ne hij, Pi.zero_apply]
        have := hw i; omega
  have heval : W.P.eval (0 : Fin d → ℕ) =
      W.P.eval (Function.update (0 : Fin d → ℕ) j 1) := by
    show W.P.base + ∑ i, ((0 : Fin d → ℕ) i : ℤ) • W.P.step i =
        W.P.base + ∑ i, ((Function.update (0 : Fin d → ℕ) j 1 i : ℤ) •
          W.P.step i)
    have hsum0 : (∑ i, ((0 : Fin d → ℕ) i : ℤ) • W.P.step i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp
    rw [hsum0, Finset.sum_eq_single j]
    · rw [Function.update_self]
      simp [hs]
    · intro i _ hij
      rw [Function.update_of_ne hij]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hc := W.proper h0 he heval
  have h1 := congrFun hc j
  simp [Function.update_self] at h1

/-- `0 ∈ P` puts every point of the GAP inside the step lattice:
`x = x - 0 ∈ ⟨P⟩`. -/
private theorem mem_gapLattice_of_mem_toFinset {d : ℕ} {c : ℝ}
    {X : Finset (Fin ℓ → ℤ)} (W : SubSumWitness X c d) {x : Fin ℓ → ℤ}
    (hx : x ∈ W.P.toFinset) : x ∈ gapLattice W.P := by
  have h := W.P.sub_mem_lattice hx W.zero_mem_toFinset
  rwa [sub_zero] at h

private theorem Ah_mem_gapLattice {d : ℕ} {c : ℝ}
    {X : Finset (Fin ℓ → ℤ)} (W : SubSumWitness X c d) {a : Fin ℓ → ℤ}
    (ha : a ∈ W.Ah) : a ∈ gapLattice W.P :=
  W.mem_gapLattice_of_mem_toFinset (W.hsub (Finset.mem_union_left _ ha))

private theorem A'_mem_gapLattice {d : ℕ} {c : ℝ}
    {X : Finset (Fin ℓ → ℤ)} (W : SubSumWitness X c d) {a : Fin ℓ → ℤ}
    (ha : a ∈ W.A') : a ∈ gapLattice W.P :=
  W.Ah_mem_gapLattice (W.hA' ha)

private theorem mem_gapLattice_of_mem_subsetSumsL_A' {d : ℕ} {c : ℝ}
    {X : Finset (Fin ℓ → ℤ)} (W : SubSumWitness X c d) {x : Fin ℓ → ℤ}
    (hx : x ∈ GAP.subsetSumsL W.A') : x ∈ gapLattice W.P := by
  obtain ⟨S, hS, rfl⟩ := GAP.mem_subsetSumsL.mp hx
  exact Submodule.sum_mem _ fun a ha ↦
    W.A'_mem_gapLattice (hS ha)

/-- The translate `t` lies in `⟨P⟩`: pick `p ∈ kP ⊆ ⟨P⟩`, then
`t = (t + p) - p` with `t + p ∈ kP + t ⊆ Σ(A') ⊆ ⟨P⟩`. -/
private theorem t_mem_gapLattice {d : ℕ} {c : ℝ}
    {X : Finset (Fin ℓ → ℤ)} (W : SubSumWitness X c d) :
    W.t ∈ gapLattice W.P := by
  obtain ⟨n₀, hn₀, hn₀e⟩ := Finset.mem_image.mp W.zero_mem_toFinset
  have hbase : W.P.base ∈ gapLattice W.P := by
    have hev : W.P.base + ∑ i, (n₀ i : ℤ) • W.P.step i = 0 := hn₀e
    have hbe : W.P.base = -∑ i, (n₀ i : ℤ) • W.P.step i :=
      eq_neg_of_add_eq_zero_left hev
    rw [hbe]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i)))
  have hevalL : W.P.eval n₀ ∈ gapLattice W.P := by
    have h1 : W.P.eval n₀ - W.P.base ∈ gapLattice W.P :=
      W.P.eval_sub_base_mem_lattice n₀
    have h2 := Submodule.add_mem _ h1 hbase
    rwa [sub_add_cancel] at h2
  have hp : (W.k • W.P).eval n₀ ∈ gapLattice W.P := by
    have hev : (W.k • W.P).eval n₀ = ((W.k : ℤ) • W.P).eval n₀ := rfl
    rw [hev, GAP.smul_eval]
    exact Submodule.smul_mem _ _ hevalL
  have htp : W.t + (W.k • W.P).eval n₀ ∈ gapLattice W.P := by
    have hmem : W.t + (W.k • W.P).eval n₀ ∈
        ((W.k • W.P).translate W.t).toFinset :=
      Finset.mem_image.mpr ⟨n₀, hn₀, GAP.translate_eval _ _ _⟩
    exact W.mem_gapLattice_of_mem_subsetSumsL_A' (W.htranslate hmem)
  have h := Submodule.sub_mem _ htp hp
  rwa [add_sub_cancel_right] at h

end SubSumWitness

/-! ### The Lemmas 11–14 covering package

The input that the Minkowski assembly `exists_ne_zero_subsetSum_inter`
(`Nonaveraging/DiscreteJohn.lean`) consumes to produce the nonzero common
subset sum `v ∈ Σ(X₁) ∩ Σ(X₂)` needed at the end of Theorem 4.  A
`SubSumCoveringPackage` bundles:

* `T` — a common basepoint in `⟨W₁.P⟩ ∩ ⟨W₂.P⟩` (in the paper, a lattice
  point of the intersection lattice near the shared zonotope point
  `z₁ = z₂` of eq. (13));
* `r` — the radii of a coordinate box large enough for the covolume
  bound `2^d·index⟨P₁⟩·index⟨P₂⟩ ≤ ∏ rᵢ` (Lemma 11's `Pᵢ ⊆ C·B` step
  bounds feed `index_gapLattice_le`; the nonzero indices are the
  `⟨Pᵢ⟩`-rank input coming from the same containment);
* `T_big` — `T` exceeds the box in some coordinate, forcing the output
  `y = T + z` nonzero (the paper's alternative phrasing: the fat box
  `z₁ + ξ'|A|B` captures `≥ 2` common lattice points, one of which is
  nonzero);
* `cov₁`, `cov₂` — the eq.-(15) covering: every `⟨Pᵢ⟩`-point within
  `r` of `T` is a subset sum of `Xᵢ` (via
  `mem_subsetSumsL_of_zonotope_translate`, using the Lemma-14 fat box
  `z̄ᵢ + ξ|A|B ⊆ 𝒵` and the `discrete_john_strong` absorption of the
  Lemma-13 rounding error into `(kᵢ/2)Pᵢ`). -/
structure SubSumCoveringPackage {d : ℕ} [NeZero d] {c₁ c₂ : ℝ}
    {X₁ X₂ : Finset (Fin d → ℤ)}
    (W₁ : SubSumWitness X₁ c₁ d) (W₂ : SubSumWitness X₂ c₂ d) where
  /-- The common basepoint. -/
  T : Fin d → ℤ
  /-- The box radii. -/
  r : Fin d → ℝ
  /-- `⟨P₁⟩` has finite index in `ℤ^d` (the `P₁`-rank input). -/
  idx₁ : (gapLattice W₁.P).toAddSubgroup.index ≠ 0
  /-- `⟨P₂⟩` has finite index in `ℤ^d` (the `P₂`-rank input). -/
  idx₂ : (gapLattice W₂.P).toAddSubgroup.index ≠ 0
  /-- `T ∈ ⟨P₁⟩`. -/
  T_mem₁ : T ∈ gapLattice W₁.P
  /-- `T ∈ ⟨P₂⟩`. -/
  T_mem₂ : T ∈ gapLattice W₂.P
  /-- Nonnegativity of the radii. -/
  r_nonneg : ∀ i, 0 ≤ r i
  /-- `T` exceeds the box in some coordinate (nondegeneracy). -/
  T_big : ∃ i₀, r i₀ < |(T i₀ : ℝ)|
  /-- The `⟨P₁⟩ ∩ ⟨P₂⟩` covolume bound. -/
  covol_le : 2 ^ d *
      (((gapLattice W₁.P).toAddSubgroup.index *
        (gapLattice W₂.P).toAddSubgroup.index : ℕ) : ℝ) ≤ ∏ i, r i
  /-- The eq.-(15) covering for `X₁`: `⟨P₁⟩`-points of `T + box(r)` are
  subset sums. -/
  cov₁ : ∀ y : Fin d → ℤ, y ∈ gapLattice W₁.P →
      (∀ i, |((y - T) i : ℝ)| ≤ r i) → y ∈ GAP.subsetSumsL X₁
  /-- The eq.-(15) covering for `X₂`. -/
  cov₂ : ∀ y : Fin d → ℤ, y ∈ gapLattice W₂.P →
      (∀ i, |((y - T) i : ℝ)| ≤ r i) → y ∈ GAP.subsetSumsL X₂

/-- Given the covering package, the Minkowski assembly
(`exists_ne_zero_mem_inf_mem_box` inside
`exists_ne_zero_subsetSum_inter`, both proved) produces the nonzero
common subset sum. -/
theorem SubSumCoveringPackage.exists_common_subsetSum {d : ℕ} [NeZero d]
    {c₁ c₂ : ℝ} {X₁ X₂ : Finset (Fin d → ℤ)}
    {W₁ : SubSumWitness X₁ c₁ d} {W₂ : SubSumWitness X₂ c₂ d}
    (cov : SubSumCoveringPackage W₁ W₂) :
    ∃ v : Fin d → ℤ, v ≠ 0 ∧ v ∈ GAP.subsetSumsL X₁ ∧
      v ∈ GAP.subsetSumsL X₂ :=
  exists_ne_zero_subsetSum_inter cov.idx₁ cov.idx₂ cov.T_mem₁ cov.T_mem₂
    cov.r_nonneg cov.T_big cov.covol_le cov.cov₁ cov.cov₂

/-- A `GAP d d` with `ℤ`-linearly independent steps generates a
finite-index sublattice of `ℤ^d` (the `⟨P⟩`-rank input of the Lemma-12
covolume bound): `⟨P⟩` is then a free `ℤ`-module of rank `d`, so
`Int.submodule_toAddSubgroup_index_ne_zero_iff` applies. -/
theorem gapLattice_index_ne_zero {d : ℕ} {P : GAP d d}
    (hv : LinearIndependent ℤ P.step) :
    (gapLattice P).toAddSubgroup.index ≠ 0 :=
  Int.submodule_toAddSubgroup_index_ne_zero_iff.mpr
    ⟨(Module.Basis.span hv).equivFun⟩

/-- **The missing geometric input** for `SubSumCoveringPackage`, stated
so that the derivable part of the package is separated from the
genuinely unformalized mathematics of §3.3.  Its fields are exactly the
paper's missing ingredients:

* `li₁`, `li₂`, `C`, `step₁`, `step₂` — **Lemma 11, second half**
  (`Pᵢ ⊆` a translate of `C·B`): each `Pᵢ` has `ℤ`-linearly independent
  step vectors, bounded columnwise by `C` (in the paper
  `|stepⱼᵢ| ≤ C·wᵢ` via `step_abs_le_of_subset`; the rank conclusion
  uses the minimal-dimension argument against a rank-deficient `⟨Pᵢ⟩`.
  Per the caveat above `SubSumWitness.two_le_width`, `liᵢ` is genuinely
  an input: `SubSumDim = d` minimality alone does not imply step
  independence in this formalization);
* `T`, `T_mem₁`, `T_mem₂` — **Lemma 13 rounding into the intersection
  lattice**: a common basepoint `T ∈ ⟨P₁⟩ ∩ ⟨P₂⟩` near the shared
  zonotope point `Tz`.  (The integer roundings of `Tz` are sums of
  `Bᵢ ∓ a₀`, and `Bᵢ ∓ a₀ ⊄ ⟨Pᵢ⟩`; in the paper the membership is
  supplied by the `Āᵢ ⊆ Pᵢ` refinement, which is not among the
  hypotheses here.);
* `r`, `r_nonneg`, `T_big`, `r_covol` — the Lemma-14 fat box of radii
  `r` about `T`: large enough to dominate the covolume bound
  `2^d·(d!·∏Cⱼ)² ≤ ∏ rᵢ` (the paper's `ξ|A|·B` scale), yet strictly
  exceeded by `T` in some coordinate;
* `cov₁`, `cov₂` — **Lemma 14 / eq. (15)**: every `⟨Pᵢ⟩`-point within
  `r` of `T` is a subset sum of `Xᵢ` (via
  `mem_subsetSumsL_of_zonotope_translate`; its absorption hypothesis is
  the `discrete_john_strong` sandwich on `⟨Pᵢ⟩`).

Given a seed, `SubSumCoveringSeed.toPackage` discharges the remaining
package fields: `idxᵢ` is `gapLattice_index_ne_zero` and `covol_le` is
`index_gapLattice_le` applied to the step bounds, chained with
`r_covol`. -/
structure SubSumCoveringSeed {d : ℕ} [NeZero d] {c₁ c₂ : ℝ}
    {X₁ X₂ : Finset (Fin d → ℤ)}
    (W₁ : SubSumWitness X₁ c₁ d) (W₂ : SubSumWitness X₂ c₂ d) where
  /-- `P₁` has `ℤ`-linearly independent steps (full rank of `⟨P₁⟩`). -/
  li₁ : LinearIndependent ℤ W₁.P.step
  /-- `P₂` has `ℤ`-linearly independent steps. -/
  li₂ : LinearIndependent ℤ W₂.P.step
  /-- Uniform columnwise bound on the steps of both `Pᵢ` (the Lemma-11
  `Pᵢ ⊆ C·B` output). -/
  C : Fin d → ℤ
  step₁ : ∀ j i, |W₁.P.step j i| ≤ C j
  step₂ : ∀ j i, |W₂.P.step j i| ≤ C j
  /-- The common basepoint. -/
  T : Fin d → ℤ
  T_mem₁ : T ∈ gapLattice W₁.P
  T_mem₂ : T ∈ gapLattice W₂.P
  /-- The box radii (the Lemma-14 `ξ|A|·B` scale). -/
  r : Fin d → ℝ
  r_nonneg : ∀ i, 0 ≤ r i
  /-- `T` exceeds the box in some coordinate (nondegeneracy). -/
  T_big : ∃ i₀, r i₀ < |(T i₀ : ℝ)|
  /-- The radii dominate the covolume bound supplied by `C`. -/
  r_covol : (2 : ℝ) ^ d *
      (((d.factorial * ∏ j, (C j).natAbs) *
        (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) ≤ ∏ i, r i
  /-- The eq.-(15) covering for `X₁`. -/
  cov₁ : ∀ y : Fin d → ℤ, y ∈ gapLattice W₁.P →
      (∀ i, |((y - T) i : ℝ)| ≤ r i) → y ∈ GAP.subsetSumsL X₁
  /-- The eq.-(15) covering for `X₂`. -/
  cov₂ : ∀ y : Fin d → ℤ, y ∈ gapLattice W₂.P →
      (∀ i, |((y - T) i : ℝ)| ≤ r i) → y ∈ GAP.subsetSumsL X₂

/-- A `SubSumCoveringSeed` yields a `SubSumCoveringPackage`: the lattice
indices are nonzero by `gapLattice_index_ne_zero` and the covolume bound
follows from `index_gapLattice_le` applied to the step bounds. -/
def SubSumCoveringSeed.toPackage {d : ℕ} [NeZero d] {c₁ c₂ : ℝ}
    {X₁ X₂ : Finset (Fin d → ℤ)}
    {W₁ : SubSumWitness X₁ c₁ d} {W₂ : SubSumWitness X₂ c₂ d}
    (s : SubSumCoveringSeed W₁ W₂) :
    SubSumCoveringPackage W₁ W₂ := by
  refine ⟨s.T, s.r, gapLattice_index_ne_zero s.li₁,
    gapLattice_index_ne_zero s.li₂, s.T_mem₁, s.T_mem₂, s.r_nonneg,
    s.T_big, ?_, s.cov₁, s.cov₂⟩
  have h₁ := index_gapLattice_le s.li₁ s.step₁
  have h₂ := index_gapLattice_le s.li₂ s.step₂
  have hmul : (gapLattice W₁.P).toAddSubgroup.index *
      (gapLattice W₂.P).toAddSubgroup.index ≤
      (d.factorial * ∏ j, (s.C j).natAbs) *
        (d.factorial * ∏ j, (s.C j).natAbs) :=
    Nat.mul_le_mul h₁ h₂
  calc (2 : ℝ) ^ d *
          (((gapLattice W₁.P).toAddSubgroup.index *
            (gapLattice W₂.P).toAddSubgroup.index : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ d *
          (((d.factorial * ∏ j, (s.C j).natAbs) *
            (d.factorial * ∏ j, (s.C j).natAbs) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmul) (by positivity)
    _ ≤ ∏ i, s.r i := s.r_covol

/-! ### §3.3 decomposition of the covering-seed construction

`exists_subSumCoveringSeed` is reduced to the residual inputs of
`exists_lemma11_rank` and `exists_lemma14_covering` below, whose
conclusions are exactly the unformalized mathematics of the paper's
§3.3.  They are assembled from the four atomic residuals
`exists_lemma11_rank` (minimal-dimension rank),
`exists_lemma13_14_data` (the Lemma-11 column bound `C` with its
coordinate boxes, the largeness of the common zonotope point `Tz` at
the covolume scale `bound(C)`, and the Lemma-14 fat-box covering at
that same scale — the three must share one `C`, see its docstring),
`exists_lemma14_lattice_core` (the `Āᵢ ⊆ Pᵢ` refinement for elements
outside `Wᵢ.Ah`), and `exists_lemma14_absorption` (the
`discrete_john_strong` sandwich), all sharing the hypothesis bundle
`lemma33Hypotheses`.  Everything else is proved: the step bound
(`lemma11_step_bound`, via `step_abs_le_of_subset`), the `Wᵢ.Ah`-part
of the lattice refinement (`SubSumWitness.Ah_mem_gapLattice`), the
Lemma-13 rounding of `Tz` into `⟨P₁⟩ ∩ ⟨P₂⟩`
(`exists_lattice_intersection_rounding`), the choice of covering radii
(`seed_radii`), and the eq.-(15) covering assembly
(`fat_box_covering`, via `mem_subsetSumsL_of_zonotope_translate`). -/

namespace SubSumWitness

/-- A structure-witness GAP is homogeneous: `0 ∈ P.toFinset` expresses
`P.base` as a (negated) integer combination of the steps. -/
theorem homogeneous {d : ℕ} {c : ℝ} {X : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness X c d) : W.P.Homogeneous := by
  obtain ⟨n₀, -, hn₀e⟩ := Finset.mem_image.mp W.zero_mem_toFinset
  have hev : W.P.base + ∑ i, (n₀ i : ℤ) • W.P.step i = 0 := hn₀e
  have hbe : W.P.base = -∑ i, (n₀ i : ℤ) • W.P.step i :=
    eq_neg_of_add_eq_zero_left hev
  refine ⟨fun i ↦ -(n₀ i : ℤ), ?_⟩
  rw [hbe, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul]

/-- **Compression lemma** — the algebraic half of Lemma 11's rank
argument.  If a `d`-dimensional witness `W` admits a *sandwich* — a
proper lower-dimensional GAP `Q` with `W.Ah ∪ {0} ⊆ Q ⊆ W.P` (pointwise)
— then the same data `(Ah, A', k, t)` form a witness at the lower
dimension: `Q ⊇ Ah ∪ {0}` by assumption, `kQ + t ⊆ kP + t ⊆ Σ(A')` since
`Q ⊆ P`, and `kQ` is proper since `Q` is and `k ≠ 0`.

In the paper this is the mechanism by which a rank-deficient `⟨P⟩`
(which confines `P` to a coset of a lower-dimensional lattice) would
contradict `SubSumDim = d`; the remaining geometric input is the
*existence* of the sandwich, which the paper obtains from the
`P ⊆` translate-of-`C·B` containment of Lemma 11. -/
theorem compress_of_subgap {d r : ℕ} {c : ℝ} {X : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness X c d) (Q : GAP ℓ r) (hQ : Q.Proper)
    (hAh : (W.Ah ∪ {0}) ⊆ Q.toFinset)
    (hfit : Q.toFinset ⊆ W.P.toFinset) :
    Nonempty (SubSumWitness X c r) := by
  refine ⟨{ Ah := W.Ah, A' := W.A', P := Q, k := W.k, t := W.t,
            cpos := W.cpos, kpos := W.kpos, hk := W.hk, hAh := W.hAh,
            hA' := W.hA', hA'card := W.hA'card, hAhcard := W.hAhcard,
            hsub := hAh, htranslate := ?_, hproper := ?_ }⟩
  · intro x hx
    apply W.htranslate
    rw [GAP.mem_translate_iff] at hx ⊢
    have himg : (W.k • Q).toFinset ⊆ (W.k • W.P).toFinset := by
      rw [GAP.nsmul_eq_zsmul W.k Q, GAP.nsmul_eq_zsmul W.k W.P,
        GAP.toFinset_smul, GAP.toFinset_smul]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨z, hfit hz, rfl⟩
    exact himg hx
  · rw [GAP.nsmul_eq_zsmul]
    exact (GAP.proper_smul_iff
      (show (W.k : ℤ) ≠ 0 by exact_mod_cast W.kpos.ne')).mpr hQ

/-- A minimal-dimension witness admits no proper lower-dimensional
sandwich: `compress_of_subgap` would give `SubSumDim X c ≤ r < d`,
contradicting `SubSumDim X c = d`.  This is the precise point at which
`exists_lemma11_rank` consumes its geometric input. -/
theorem no_sandwich_of_minimal {d : ℕ} {c : ℝ} {X : Finset (Fin ℓ → ℤ)}
    (W : SubSumWitness X c d) (hdim : SubSumDim X c = d) :
    ¬ ∃ (r : ℕ) (Q : GAP ℓ r), r < d ∧ Q.Proper ∧
        (W.Ah ∪ {0}) ⊆ Q.toFinset ∧ Q.toFinset ⊆ W.P.toFinset := by
  rintro ⟨r, Q, hr, hQ, hAh, hfit⟩
  have hle := subSumDim_le (W.compress_of_subgap Q hQ hAh hfit)
  omega

end SubSumWitness

/-- **Lemma 11, second half** (the step bound): a nonempty `d`-dimensional
GAP contained in the integer coordinate box `∏ [loᵢ, hiᵢ]` has its `j`-th
step bounded columnwise by the box widths, hence by `C j` whenever
`hiᵢ − loᵢ ≤ C j`.  This is `step_abs_le_of_subset` repackaged; it
discharges the `step₁`/`step₂` fields of `SubSumCoveringSeed` from the
paper's `Pᵢ ⊆` translate-of-`C·B` containment. -/
theorem lemma11_step_bound {d : ℕ} {P : GAP d d}
    {lo hi C : Fin d → ℤ}
    (hsub : P.toFinset ⊆
      Fintype.piFinset fun i ↦ Finset.Icc (lo i) (hi i))
    (hne : P.toFinset.Nonempty) (hw : ∀ j, 2 ≤ P.width j)
    (hC : ∀ j i, hi i - lo i ≤ C j) :
    ∀ j i, |P.step j i| ≤ C j :=
  fun j i ↦ (step_abs_le_of_subset hsub hne j (hw j) i).trans (hC j i)

/-- **Lemma 13** (rounding into the intersection lattice): if `⟨P₁⟩` and
`⟨P₂⟩` have full rank, there is a uniform coordinatewise slack `ρ` such
that every real point `Tz` admits a common lattice point
`T ∈ ⟨P₁⟩ ∩ ⟨P₂⟩` with `|Tᵢ − Tzᵢ| ≤ ρᵢ`.  Take a `ℤ`-basis `w` of the
finite-index intersection `L = ⟨P₁⟩ ∩ ⟨P₂⟩`, view it as an `ℝ`-basis
(`index L = |det w| ≠ 0`), write `Tz = ∑ αⱼ·wⱼ` and round each
coefficient down; the error is bounded by `ρᵢ = ∑ⱼ |wⱼᵢ|`. -/
theorem exists_lattice_intersection_rounding {d : ℕ} [NeZero d]
    {P₁ P₂ : GAP d d}
    (hli₁ : LinearIndependent ℤ P₁.step)
    (hli₂ : LinearIndependent ℤ P₂.step) :
    ∃ ρ : Fin d → ℝ, ∀ Tz : Fin d → ℝ, ∃ T : Fin d → ℤ,
      T ∈ gapLattice P₁ ∧ T ∈ gapLattice P₂ ∧
      ∀ i, |(T i : ℝ) - Tz i| ≤ ρ i := by
  classical
  set L₁ := (gapLattice P₁).toAddSubgroup
  set L₂ := (gapLattice P₂).toAddSubgroup
  have hL₁ : L₁.index ≠ 0 := gapLattice_index_ne_zero hli₁
  have hL₂ : L₂.index ≠ 0 := gapLattice_index_ne_zero hli₂
  set L := L₁ ⊓ L₂
  have hLi : L.index ≠ 0 := AddSubgroup.index_inf_ne_zero hL₁ hL₂
  obtain ⟨e⟩ : Nonempty (↥(L.toIntSubmodule) ≃ₗ[ℤ] (Fin d → ℤ)) :=
    (Int.submodule_toAddSubgroup_index_ne_zero_iff).mp (by
      rw [AddSubgroup.toIntSubmodule_toAddSubgroup]; exact hLi)
  set bL : Module.Basis (Fin d) ℤ ↥(L.toIntSubmodule) :=
    (Pi.basisFun ℤ (Fin d)).map e.symm
  set w : Fin d → Fin d → ℤ := fun i ↦ (bL i : Fin d → ℤ)
  have hwmem : ∀ i, w i ∈ L.toIntSubmodule := fun i ↦ (bL i).2
  -- `index L = |det w| ≠ 0`, so `w` remains a basis over `ℝ`.
  have hdet : L.index = (((Pi.basisFun ℤ (Fin d)).det w).natAbs) :=
    AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin d)) L bL
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
  refine ⟨fun i ↦ ∑ j, |(vR j) i|, fun Tz ↦ ?_⟩
  set T : Fin d → ℤ := ∑ j, ⌊bR.repr Tz j⌋ • w j with hTdef
  have hTL : T ∈ L.toIntSubmodule :=
    Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hwmem j)
  have hTinf : T ∈ L₁ ⊓ L₂ := hTL
  have hT1 : T ∈ gapLattice P₁ := (AddSubgroup.mem_inf.mp hTinf).1
  have hT2 : T ∈ gapLattice P₂ := (AddSubgroup.mem_inf.mp hTinf).2
  refine ⟨T, hT1, hT2, fun i ↦ ?_⟩
  have hTz : Tz = ∑ j, bR.repr Tz j • vR j := by
    have h := bR.sum_repr Tz
    rw [hbR_eq] at h
    exact h.symm
  have hTint : intVec T = ∑ j, (⌊bR.repr Tz j⌋ : ℝ) • vR j := by
    rw [hTdef, intVec_sum]
    exact Finset.sum_congr rfl fun j _ ↦ intVec_smul _ _
  have hcoord : (T i : ℝ) - Tz i =
      ∑ j, ((⌊bR.repr Tz j⌋ : ℝ) - bR.repr Tz j) * (vR j) i := by
    have e1 : (intVec T) i =
        ∑ j, (⌊bR.repr Tz j⌋ : ℝ) * (vR j) i := by
      rw [hTint]
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have e2 : Tz i = ∑ j, bR.repr Tz j * (vR j) i := by
      conv_lhs => rw [hTz]
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have e3 : (T i : ℝ) = (intVec T) i := (intVec_apply T i).symm
    rw [e3, e1, e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  calc |(T i : ℝ) - Tz i|
      = |∑ j, ((⌊bR.repr Tz j⌋ : ℝ) - bR.repr Tz j) * (vR j) i| := by
        rw [hcoord]
    _ ≤ ∑ j, |((⌊bR.repr Tz j⌋ : ℝ) - bR.repr Tz j) * (vR j) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |(vR j) i| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have hj : |(⌊bR.repr Tz j⌋ : ℝ) - bR.repr Tz j| ≤ 1 := by
          have h1 : |(⌊bR.repr Tz j⌋ : ℝ) - bR.repr Tz j| =
              Int.fract (bR.repr Tz j) := by
            have e : (⌊bR.repr Tz j⌋ : ℝ) - bR.repr Tz j =
                -(bR.repr Tz j - (⌊bR.repr Tz j⌋ : ℝ)) := by ring
            rw [e, abs_neg, Int.self_sub_floor]
            exact abs_of_nonneg (Int.fract_nonneg _)
          rw [h1]
          exact (Int.fract_lt_one _).le
        calc |(⌊bR.repr Tz j⌋ : ℝ) - bR.repr Tz j| * |(vR j) i|
            ≤ 1 * |(vR j) i| :=
              mul_le_mul_of_nonneg_right hj (abs_nonneg _)
          _ = |(vR j) i| := one_mul _

/-- The coordinatewise rounding slack produced by
`exists_lattice_intersection_rounding`. -/
noncomputable def intersectionRoundingSlack {d : ℕ} [NeZero d]
    {P₁ P₂ : GAP d d}
    (hli₁ : LinearIndependent ℤ P₁.step)
    (hli₂ : LinearIndependent ℤ P₂.step) : Fin d → ℝ :=
  Classical.choose (exists_lattice_intersection_rounding hli₁ hli₂)

/-- The rounding of `Tz` into `⟨P₁⟩ ∩ ⟨P₂⟩` at slack
`intersectionRoundingSlack`. -/
theorem intersectionRoundingSlack_spec {d : ℕ} [NeZero d]
    {P₁ P₂ : GAP d d}
    (hli₁ : LinearIndependent ℤ P₁.step)
    (hli₂ : LinearIndependent ℤ P₂.step) (Tz : Fin d → ℝ) :
    ∃ T : Fin d → ℤ, T ∈ gapLattice P₁ ∧ T ∈ gapLattice P₂ ∧
      ∀ i, |(T i : ℝ) - Tz i| ≤ intersectionRoundingSlack hli₁ hli₂ i :=
  Classical.choose_spec
    (exists_lattice_intersection_rounding hli₁ hli₂) Tz

/-- The rounding slack is nonnegative: the spec at `Tz = 0` yields
`0 ≤ |(T i : ℝ)| ≤ ρ i`.  This records that the largeness part of
`exists_lemma13_14_data` can never hold at `Tz = 0` (both the covolume
term and the slack are nonnegative), so the largeness of `Tz` is a
genuine input about the eq.-(13) point — not a consequence of the
zonotope memberships (which hold at `Tz = 0` by `zero_mem_zonotope`). -/
theorem intersectionRoundingSlack_nonneg {d : ℕ} [NeZero d]
    {P₁ P₂ : GAP d d}
    (hli₁ : LinearIndependent ℤ P₁.step)
    (hli₂ : LinearIndependent ℤ P₂.step) (i : Fin d) :
    0 ≤ intersectionRoundingSlack hli₁ hli₂ i := by
  obtain ⟨T, -, -, hT⟩ :=
    intersectionRoundingSlack_spec hli₁ hli₂ (0 : Fin d → ℝ)
  have h : |(T i : ℝ)| ≤ intersectionRoundingSlack hli₁ hli₂ i := by
    have hTi := hT i
    simp only [Pi.zero_apply, sub_zero] at hTi
    exact hTi
  exact (abs_nonneg _).trans h

/-- The covering radii: given the Lemma-11 column bound `C` and a common
lattice point `T` exceeding the covolume bound `2^d·(d!·∏ Cⱼ)²` in
coordinate `i₀`, the radii `r_{i₀} = 2^d·(d!·∏ Cⱼ)²`, `rᵢ = 1` (else)
satisfy `r_nonneg`, `T_big`, `r_covol`, and stay at the covolume scale
(`rᵢ ≤ bound + 1`). -/
theorem seed_radii {d : ℕ} {C : Fin d → ℤ} {T : Fin d → ℤ} {i₀ : Fin d}
    (hT : (2 : ℝ) ^ d *
        (((d.factorial * ∏ j, (C j).natAbs) *
          (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) < |(T i₀ : ℝ)|) :
    ∃ r : Fin d → ℝ, (∀ i, 0 ≤ r i) ∧
      (∀ i, r i ≤ (2 : ℝ) ^ d *
          (((d.factorial * ∏ j, (C j).natAbs) *
            (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) + 1) ∧
      (∃ i₀, r i₀ < |(T i₀ : ℝ)|) ∧
      (2 : ℝ) ^ d *
          (((d.factorial * ∏ j, (C j).natAbs) *
            (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) ≤ ∏ i, r i := by
  classical
  set B : ℝ := (2 : ℝ) ^ d *
    (((d.factorial * ∏ j, (C j).natAbs) *
      (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) with hBdef
  have hB : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (pow_nonneg zero_le_two _) (Nat.cast_nonneg _)
  refine ⟨fun i ↦ if i = i₀ then B else 1, fun i ↦ ?_, fun i ↦ ?_, ?_, ?_⟩
  · by_cases hi : i = i₀
    · show (0 : ℝ) ≤ if i = i₀ then B else 1
      rw [ite_eq_left hi]; exact hB
    · show (0 : ℝ) ≤ if i = i₀ then B else 1
      rw [ite_eq_right hi]; exact zero_le_one
  · by_cases hi : i = i₀
    · show (if i = i₀ then B else 1 : ℝ) ≤ B + 1
      rw [ite_eq_left hi]; linarith
    · show (if i = i₀ then B else 1 : ℝ) ≤ B + 1
      rw [ite_eq_right hi]; linarith
  · exact ⟨i₀, by
      show (if i₀ = i₀ then B else 1 : ℝ) < |(T i₀ : ℝ)|
      rw [ite_eq_left rfl]; exact hT⟩
  · have hprod : ∏ i, (if i = i₀ then B else (1 : ℝ)) = B := by
      rw [Finset.prod_eq_single i₀ (fun b _ hb ↦ if_neg hb)
        (fun h ↦ absurd (Finset.mem_univ i₀) h), if_pos rfl]
    rw [hprod]

/-- **Lemma 14** (eq. (15) covering assembly): every `⟨P⟩`-point of the
box `T + ∏ [−rᵢ, rᵢ]` is a subset sum of `X`.  This is
`mem_subsetSumsL_of_zonotope_translate` instantiated at the structure
witness `W` (`X' = W.A'`, `K = W.k`, `q = W.t`, `P = W.P`): the translate
containment is `W.htranslate`, `q ∈ ⟨P⟩` is `W.t_mem_gapLattice`, and
`P` is homogeneous (`SubSumWitness.homogeneous`).  The three hypotheses
`hXspan` (`X ⊆ ⟨P⟩`, the `Ā ⊆ P` refinement), `habs` (the
`discrete_john_strong` absorption of a small `⟨P⟩`-point into `kP` over
`(k/2)P`) and `hfat` (the fat box `z̄ + ξ|A|B ⊆ 𝒵_{X∖A'}` covering the
region `T + box(r) − q − (k/2)P`) are the genuine Lemma-14 inputs. -/
theorem fat_box_covering {d : ℕ} {c : ℝ} {X : Finset (Fin d → ℤ)}
    (W : SubSumWitness X c d) {wX : Fin d → ℝ}
    (hwX0 : ∀ i, 0 ≤ wX i)
    (hwX : ∀ a ∈ X \ W.A', ∀ i, |(a i : ℝ)| ≤ wX i)
    (hXspan : ∀ a ∈ X, a ∈ gapLattice W.P)
    (habs : ∀ s : Fin d → ℤ, s ∈ gapLattice W.P →
        (∀ i, |(s i : ℝ)| ≤ (d : ℝ) * wX i) →
        ∀ t ∈ (((W.k : ℤ) / 2) • W.P).toFinset,
          s + t ∈ ((W.k : ℤ) • W.P).toFinset)
    {T : Fin d → ℤ} {r : Fin d → ℝ}
    (hfat : ∀ y : Fin d → ℤ, (∀ i, |((y - T) i : ℝ)| ≤ r i) →
        ∃ t ∈ (((W.k : ℤ) / 2) • W.P).toFinset,
          (fun i ↦ (y i : ℝ) - (W.t i : ℝ) - (t i : ℝ)) ∈
            zonotope ((X \ W.A').image fun x i ↦ (x i : ℝ))) :
    ∀ y : Fin d → ℤ, y ∈ gapLattice W.P →
      (∀ i, |((y - T) i : ℝ)| ≤ r i) → y ∈ GAP.subsetSumsL X := by
  classical
  intro y hy hbd
  obtain ⟨t, ht, hzt⟩ := hfat y hbd
  apply mem_subsetSumsL_of_zonotope_translate (X' := W.A') (P := W.P)
    (K := (W.k : ℤ)) (q := W.t) (wX := wX)
  · exact W.hA'.trans W.hAh
  · exact W.homogeneous
  · exact W.t_mem_gapLattice
  · exact hXspan
  · exact W.htranslate
  · exact hwX0
  · exact hwX
  · exact habs
  · exact hy
  · exact ⟨fun i ↦ (y i : ℝ) - (W.t i : ℝ) - (t i : ℝ), hzt, t, ht,
      fun i ↦ by
        show (y i : ℝ) =
          (y i : ℝ) - (W.t i : ℝ) - (t i : ℝ) + (W.t i : ℝ) + (t i : ℝ)
        ring⟩

/-- The §3.3 hypothesis bundle shared by the residual inputs below:
`A` is non-averaging with `(δ,γ)`-irreducible structure witness `W`,
`a₀ ∈ ϕ_P(Â)`, `B₁ ⊔ B₂ = ϕ_P(Â) ∖ {a₀}` is the equitable split with
`δ|A| ≤ |Bᵢ|`, `Wᵢ` are the minimal witnesses of `Bᵢ ∓ a₀` supplied by
Lemma 11's first half (`SubSumDim = d`, `|Pᵢ| ≥ γ|P|`), the pieces lie
in the coefficient box `|x ∓ a₀| ≤ wᵢ`, and `Tz` is the common
eq.-(13) zonotope point; `N₀` is the ambient largeness threshold. -/
def lemma33Hypotheses {ℓ : ℕ} {c c' δ γ C' : ℝ} (N₀ : ℕ)
    (A : Finset (Fin ℓ → ℤ)) (d : ℕ)
    (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
    (B₁ B₂ : Finset (Fin d → ℤ))
    (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
    (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
    (Tz : Fin d → ℝ) : Prop :=
  NonAveraging A ∧ Irreducible W c' δ γ ∧
    (Real.log (A.card : ℝ)) ^ (-(1 : ℝ) / C') ≤ γ ∧
    0 < δ ∧ δ < 1 ∧ 0 < γ ∧ γ < 1 ∧ 4 * δ < 1 ∧ N₀ ≤ A.card ∧
    a₀ ∈ W.imageAh ∧
    B₁ ⊆ W.imageAh.erase a₀ ∧ B₂ ⊆ W.imageAh.erase a₀ ∧
    Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = W.imageAh.erase a₀ ∧
    δ * (A.card : ℝ) ≤ (B₁.card : ℝ) ∧
    δ * (A.card : ℝ) ≤ (B₂.card : ℝ) ∧
    (∀ x ∈ B₁, ∀ i, |((x - a₀) i : ℝ)| ≤ (W.P.width i : ℝ)) ∧
    (∀ x ∈ B₂, ∀ i, |((a₀ - x) i : ℝ)| ≤ (W.P.width i : ℝ)) ∧
    SubSumDim (B₁.image (· - a₀)) c' = d ∧
    SubSumDim (B₂.image (a₀ - ·)) c' = d ∧
    (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₁.P.toFinset.card : ℝ) ∧
    (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₂.P.toFinset.card : ℝ) ∧
    Tz ∈ zonotope ((B₁.image (· - a₀)).image intVec) ∧
    Tz ∈ zonotope ((B₂.image (a₀ - ·)).image intVec)

/-- Every finite set of integer vectors has a uniform coordinatewise
bound — the trivial interval box containing `P.toFinset` used for the
Lemma-11 `Pᵢ ⊆ C·B` bookkeeping (any bound works here; the paper's
sharp `C·wⱼ` scale is needed only downstream, inside the
`∏ (C j).natAbs` covolume bound and the Lemma-13 largeness input). -/
theorem exists_int_coord_bound {d : ℕ} (S : Finset (Fin d → ℤ)) :
    ∃ B : ℕ, ∀ x ∈ S, ∀ i, |x i| ≤ (B : ℤ) := by
  refine ⟨∑ x ∈ S, ∑ i, (x i).natAbs, fun x hx i ↦ ?_⟩
  have h1 : (x i).natAbs ≤ ∑ j, (x j).natAbs :=
    Finset.single_le_sum (f := fun j ↦ (x j).natAbs)
      (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have h2 : ∑ j, (x j).natAbs ≤ ∑ y ∈ S, ∑ j, (y j).natAbs :=
    Finset.single_le_sum (f := fun y ↦ ∑ j, (y j).natAbs)
      (fun y _ ↦ Finset.sum_nonneg (f := fun j ↦ (y j).natAbs)
        fun j _ ↦ Nat.zero_le _) hx
  have h3 := h1.trans h2
  rw [← Int.natCast_natAbs]
  exact_mod_cast h3

/-- **Residual input — Lemma 11 second half (rank).**  For `|A|` large,
the steps of the minimal-dimension witnesses `Wᵢ.P` are `ℤ`-linearly
independent.  In the paper this is the minimal-dimension argument: a
rank-deficient `⟨Pᵢ⟩` would place `Pᵢ` in a lower-dimensional
sublattice and (via the `Pᵢ ⊆ C·B` containment) compress it to a
witness of dimension `< d`, contradicting `SubSumDim (Bᵢ ∓ a₀) c' = d`.

The algebraic half of that compression is proved:
`SubSumWitness.compress_of_subgap` builds a lower-dimensional
`SubSumWitness` from a *sandwich* GAP `Q` (proper, `r < d`, with
`Wᵢ.Ah ∪ {0} ⊆ Q ⊆ Wᵢ.P` pointwise), and
`SubSumWitness.no_sandwich_of_minimal` shows such a `Q` cannot exist at
`SubSumDim = d`.  The genuine missing input is thus exactly: rank
deficiency of `⟨Pᵢ⟩` (which confines `Pᵢ` to a lower-dimensional lattice
coset) produces such a sandwich — the paper supplies it through the
`Pᵢ ⊆` translate-of-`C·B` containment, which is not among the
hypotheses here (no bound on `Pᵢ` at all is assumed).  (Per the caveat
at `SubSumWitness.two_le_width`, minimality alone does not imply step
independence in this formalization, so this remains an input.) -/
theorem exists_lemma11_rank {ℓ : ℕ} {c c' δ γ C' : ℝ} :
    ∃ N₀ : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (d : ℕ) [NeZero d]
        (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
        (B₁ B₂ : Finset (Fin d → ℤ))
        (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
        (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
        (Tz : Fin d → ℝ),
      lemma33Hypotheses (c' := c') (δ := δ) (γ := γ) (C' := C')
        N₀ A d W a₀ B₁ B₂ W₁ W₂ Tz →
      LinearIndependent ℤ W₁.P.step ∧ LinearIndependent ℤ W₂.P.step :=
  sorry

/-- **Residual input — Lemmas 13 + 14 (largeness and fat-box covering
at a shared scale).**  For `|A|` large there is a *single* column bound
`C` — the Lemma-11 `Pᵢ ⊆` translate-of-`C·B` scale, witnessed by
coordinate boxes `∏ [loᵢ, hiᵢ]` of width `≤ C` containing the
`Wᵢ.P.toFinset` — at which

* (`Tz` large) the common eq.-(13) zonotope point `Tz` exceeds, in some
  coordinate `i₀`, the covolume bound `2^d·(d!·∏ Cⱼ)²` of
  `⟨P₁⟩ ∩ ⟨P₂⟩` plus the intersection-lattice rounding slack, so that
  its `exists_lattice_intersection_rounding` image `T` still satisfies
  `T_big`; and
* (fat box) the Lemma-14 covering `y − tᵢ − t ∈ 𝒵_{Xᵢ∖A'ᵢ}` holds for
  every `⟨P₁⟩ ∩ ⟨P₂⟩`-rounding `T` of `Tz` and all radii `r` up to the
  covolume scale `bound(C) + 1` — the paper's
  `z̄ᵢ + ξ|A|·B ⊆ 𝒵_{Xᵢ∖A'ᵢ}` containment.

The two halves MUST share the same `C`: downstream (`seed_radii`) sets
the large radius to `bound(C)` itself, so the covolume bound, the
`Tz`-largeness and the covering radius live at one scale.  Quantifying
`C` universally instead would be *false*: for `C` large, `bound(C)`
exceeds the fixed `|Tz i₀|` (both summands are nonnegative,
`intersectionRoundingSlack_nonneg`) and exceeds the bounded zonotope
`𝒵_{X∖A'}`, so neither the largeness nor the covering could hold.

Both halves remain genuine inputs: `Tz = 0` satisfies the zonotope
memberships (`zero_mem_zonotope`) while `bound(C) + slack i₀ ≥ 0`, so
the largeness is irreducibly a property of the specific eq.-(13) point
(in the paper `z₁` carries `≈ μ|A|/2` of total weight; alternatively the
nondegeneracy could come from a two-points variant of
`exists_ne_zero_mem_inf_mem_box`), and the covering is the unformalized
fat-box containment of Lemma 14. -/
theorem exists_lemma13_14_data {ℓ : ℕ} {c c' δ γ C' : ℝ} :
    ∃ N₀ : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (d : ℕ) [NeZero d]
        (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
        (B₁ B₂ : Finset (Fin d → ℤ))
        (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
        (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
        (Tz : Fin d → ℝ)
        (hli₁ : LinearIndependent ℤ W₁.P.step)
        (hli₂ : LinearIndependent ℤ W₂.P.step),
      lemma33Hypotheses (c' := c') (δ := δ) (γ := γ) (C' := C')
        N₀ A d W a₀ B₁ B₂ W₁ W₂ Tz →
      ∃ (C lo₁ hi₁ lo₂ hi₂ : Fin d → ℤ),
        (W₁.P.toFinset ⊆
          Fintype.piFinset fun i ↦ Finset.Icc (lo₁ i) (hi₁ i)) ∧
        (W₂.P.toFinset ⊆
          Fintype.piFinset fun i ↦ Finset.Icc (lo₂ i) (hi₂ i)) ∧
        (∀ j i, hi₁ i - lo₁ i ≤ C j) ∧
        (∀ j i, hi₂ i - lo₂ i ≤ C j) ∧
        (∃ i₀, (2 : ℝ) ^ d *
            (((d.factorial * ∏ j, (C j).natAbs) *
              (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) +
          intersectionRoundingSlack hli₁ hli₂ i₀ < |(Tz i₀ : ℝ)|) ∧
        (∀ (T : Fin d → ℤ) (r : Fin d → ℝ),
          T ∈ gapLattice W₁.P → T ∈ gapLattice W₂.P →
          (∀ i, |(T i : ℝ) - Tz i| ≤
            intersectionRoundingSlack hli₁ hli₂ i) →
          (∀ i, 0 ≤ r i) →
          (∀ i, r i ≤ (2 : ℝ) ^ d *
              (((d.factorial * ∏ j, (C j).natAbs) *
                (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) + 1) →
          (∀ y : Fin d → ℤ, (∀ i, |((y - T) i : ℝ)| ≤ r i) →
            ∃ t ∈ (((W₁.k : ℤ) / 2) • W₁.P).toFinset,
              (fun i ↦ (y i : ℝ) - (W₁.t i : ℝ) - (t i : ℝ)) ∈
                zonotope (((B₁.image (· - a₀)) \ W₁.A').image
                  fun x i ↦ (x i : ℝ))) ∧
          (∀ y : Fin d → ℤ, (∀ i, |((y - T) i : ℝ)| ≤ r i) →
            ∃ t ∈ (((W₂.k : ℤ) / 2) • W₂.P).toFinset,
              (fun i ↦ (y i : ℝ) - (W₂.t i : ℝ) - (t i : ℝ)) ∈
                zonotope (((B₂.image (a₀ - ·)) \ W₂.A').image
                  fun x i ↦ (x i : ℝ)))) :=
  sorry

/-- **Lemma 11 second half + Lemma 13 largeness** (assembled).  For all
sufficiently large `|A|`, the minimal-dimension witnesses `W₁`, `W₂`
supplied by Lemma 11's first half satisfy:

* (`Pᵢ ⊆` translate of `C·B`, step bounds) each `Pᵢ.toFinset` is
  contained in an integer coordinate box `∏ [loᵢ, hiᵢ]` whose widths are
  bounded by the column bound `C` — feeding `lemma11_step_bound` and
  `index_gapLattice_le`.  The boxes and the bound `C` are part of the
  shared-scale residual `exists_lemma13_14_data` (a trivial bound
  `exists_int_coord_bound` always exists, but only the paper's
  `C·wⱼ`-scale bound can feed the largeness and the fat-box covering at
  the covolume scale);
* (rank) each `Pᵢ.step` is `ℤ`-linearly independent — the residual
  `exists_lemma11_rank`;
* (`Tz` dominates the covolume bound plus the intersection-lattice
  rounding slack) — part of the residual `exists_lemma13_14_data` (the
  rounding itself is proved — `exists_lattice_intersection_rounding`). -/
theorem exists_lemma11_13_data {ℓ : ℕ} {c c' δ γ C' : ℝ} :
    ∃ N₀ : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (d : ℕ) [NeZero d]
        (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
        (B₁ B₂ : Finset (Fin d → ℤ))
        (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
        (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
        (Tz : Fin d → ℝ),
      NonAveraging A → Irreducible W c' δ γ →
      (Real.log (A.card : ℝ)) ^ (-(1 : ℝ) / C') ≤ γ →
      0 < δ → δ < 1 → 0 < γ → γ < 1 → 4 * δ < 1 →
      N₀ ≤ A.card →
      a₀ ∈ W.imageAh →
      B₁ ⊆ W.imageAh.erase a₀ → B₂ ⊆ W.imageAh.erase a₀ →
      Disjoint B₁ B₂ → B₁ ∪ B₂ = W.imageAh.erase a₀ →
      δ * (A.card : ℝ) ≤ (B₁.card : ℝ) →
      δ * (A.card : ℝ) ≤ (B₂.card : ℝ) →
      (∀ x ∈ B₁, ∀ i, |((x - a₀) i : ℝ)| ≤ (W.P.width i : ℝ)) →
      (∀ x ∈ B₂, ∀ i, |((a₀ - x) i : ℝ)| ≤ (W.P.width i : ℝ)) →
      SubSumDim (B₁.image (· - a₀)) c' = d →
      SubSumDim (B₂.image (a₀ - ·)) c' = d →
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₁.P.toFinset.card : ℝ) →
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₂.P.toFinset.card : ℝ) →
      Tz ∈ zonotope ((B₁.image (· - a₀)).image intVec) →
      Tz ∈ zonotope ((B₂.image (a₀ - ·)).image intVec) →
      ∃ (C lo₁ hi₁ lo₂ hi₂ : Fin d → ℤ)
        (hli₁ : LinearIndependent ℤ W₁.P.step)
        (hli₂ : LinearIndependent ℤ W₂.P.step),
        (W₁.P.toFinset ⊆
          Fintype.piFinset fun i ↦ Finset.Icc (lo₁ i) (hi₁ i)) ∧
        (W₂.P.toFinset ⊆
          Fintype.piFinset fun i ↦ Finset.Icc (lo₂ i) (hi₂ i)) ∧
        (∀ j i, hi₁ i - lo₁ i ≤ C j) ∧
        (∀ j i, hi₂ i - lo₂ i ≤ C j) ∧
        ∃ i₀, (2 : ℝ) ^ d *
            (((d.factorial * ∏ j, (C j).natAbs) *
              (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) +
          intersectionRoundingSlack hli₁ hli₂ i₀ < |(Tz i₀ : ℝ)| := by
  classical
  obtain ⟨N₁, hN₁⟩ := exists_lemma11_rank (ℓ := ℓ) (c := c) (c' := c')
    (δ := δ) (γ := γ) (C' := C')
  obtain ⟨N₂, hN₂⟩ := exists_lemma13_14_data (ℓ := ℓ) (c := c)
    (c' := c') (δ := δ) (γ := γ) (C' := C')
  refine ⟨max N₁ N₂, ?_⟩
  intro A d _ W a₀ B₁ B₂ W₁ W₂ Tz hNA hIrred hγlog hδ hδ1 hγ hγ1 hδ4
    hN ha₀ hB₁e hB₂e hdisj hcover hδB₁ hδB₂ hb₁ hb₂ hdim₁ hdim₂ hP₁ hP₂
    hTz₁ hTz₂
  obtain ⟨hli₁, hli₂⟩ := hN₁ A d W a₀ B₁ B₂ W₁ W₂ Tz
    ⟨hNA, hIrred, hγlog, hδ, hδ1, hγ, hγ1, hδ4,
      (le_max_left N₁ N₂).trans hN, ha₀, hB₁e, hB₂e, hdisj, hcover,
      hδB₁, hδB₂, hb₁, hb₂, hdim₁, hdim₂, hP₁, hP₂, hTz₁, hTz₂⟩
  obtain ⟨C, lo₁, hi₁, lo₂, hi₂, hbox₁, hbox₂, hC₁, hC₂, hlarge, -⟩ :=
    hN₂ A d W a₀ B₁ B₂ W₁ W₂ Tz hli₁ hli₂
      ⟨hNA, hIrred, hγlog, hδ, hδ1, hγ, hγ1, hδ4,
        (le_max_right N₁ N₂).trans hN, ha₀, hB₁e, hB₂e, hdisj, hcover,
        hδB₁, hδB₂, hb₁, hb₂, hdim₁, hdim₂, hP₁, hP₂, hTz₁, hTz₂⟩
  exact ⟨C, lo₁, hi₁, lo₂, hi₂, hli₁, hli₂, hbox₁, hbox₂, hC₁, hC₂,
    hlarge⟩

/-- **Residual input — Lemma 14, the `Āᵢ ⊆ Pᵢ` refinement (lattice
membership, core).**  For `|A|` large, the shifted-piece elements that
are *not already* witness points — `a ∈ (Bᵢ ∓ a₀) ∖ Wᵢ.Ah` — lie in the
lattices `⟨Pᵢ⟩`.  In the paper this is the refinement step of
Lemma 11/14: the minimal witness `Pᵢ` is chosen so that `Āᵢ ⊆ Pᵢ`, and
`x ∓ a₀ ∈ ⟨Pᵢ⟩` follows for the coefficient image of every point of
`Bᵢ`.

Only the `∖ Wᵢ.Ah` part is a genuine input: elements of `Wᵢ.Ah` lie in
`Wᵢ.P.toFinset` (`SubSumWitness.hsub`) and hence in `⟨Wᵢ.P⟩`
(`SubSumWitness.Ah_mem_gapLattice`), so `exists_lemma14_lattice` below
extends this to all of `Bᵢ ∓ a₀`. -/
theorem exists_lemma14_lattice_core {ℓ : ℕ} {c c' δ γ C' : ℝ} :
    ∃ N₀ : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (d : ℕ) [NeZero d]
        (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
        (B₁ B₂ : Finset (Fin d → ℤ))
        (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
        (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
        (Tz : Fin d → ℝ),
      lemma33Hypotheses (c' := c') (δ := δ) (γ := γ) (C' := C')
        N₀ A d W a₀ B₁ B₂ W₁ W₂ Tz →
      (∀ a ∈ B₁.image (· - a₀) \ W₁.Ah, a ∈ gapLattice W₁.P) ∧
      (∀ a ∈ B₂.image (a₀ - ·) \ W₂.Ah, a ∈ gapLattice W₂.P) :=
  sorry

/-- **Lemma 14, the `Āᵢ ⊆ Pᵢ` refinement (lattice membership).**  For
`|A|` large, the whole shifted pieces `Bᵢ ∓ a₀` (not merely
`Wᵢ.Ah ⊆ Bᵢ ∓ a₀`) lie in the lattices `⟨Pᵢ⟩`: `Wᵢ.Ah`-elements are in
`⟨Pᵢ⟩` by `SubSumWitness.Ah_mem_gapLattice`, the rest is the residual
`exists_lemma14_lattice_core`. -/
theorem exists_lemma14_lattice {ℓ : ℕ} {c c' δ γ C' : ℝ} :
    ∃ N₀ : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (d : ℕ) [NeZero d]
        (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
        (B₁ B₂ : Finset (Fin d → ℤ))
        (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
        (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
        (Tz : Fin d → ℝ),
      lemma33Hypotheses (c' := c') (δ := δ) (γ := γ) (C' := C')
        N₀ A d W a₀ B₁ B₂ W₁ W₂ Tz →
      (∀ a ∈ B₁.image (· - a₀), a ∈ gapLattice W₁.P) ∧
      (∀ a ∈ B₂.image (a₀ - ·), a ∈ gapLattice W₂.P) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_lemma14_lattice_core (ℓ := ℓ) (c := c)
    (c' := c') (δ := δ) (γ := γ) (C' := C')
  refine ⟨N₀, ?_⟩
  intro A d _ W a₀ B₁ B₂ W₁ W₂ Tz h
  obtain ⟨h₁, h₂⟩ := hN₀ A d W a₀ B₁ B₂ W₁ W₂ Tz h
  refine ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · by_cases ha' : a ∈ W₁.Ah
    · exact W₁.Ah_mem_gapLattice ha'
    · exact h₁ a (Finset.mem_sdiff.mpr ⟨ha, ha'⟩)
  · by_cases ha' : a ∈ W₂.Ah
    · exact W₂.Ah_mem_gapLattice ha'
    · exact h₂ a (Finset.mem_sdiff.mpr ⟨ha, ha'⟩)

/-- **Residual input — Lemma 14, absorption.**  For `|A|` large, a
lattice point `s ∈ ⟨Pᵢ⟩` coordinatewise bounded by `d·w` is absorbed:
`s + t ∈ kᵢ·Pᵢ` for every `t ∈ (kᵢ/2)·Pᵢ`.  In the paper this is the
`discrete_john_strong` sandwich on `⟨Pᵢ⟩` combined with
`kᵢ ≈ s(A)` being large (the rounding error `r` of Lemma 13 satisfies
`r + (kᵢ/2)Pᵢ ⊆ kᵢPᵢ` coefficientwise). -/
theorem exists_lemma14_absorption {ℓ : ℕ} {c c' δ γ C' : ℝ} :
    ∃ N₀ : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (d : ℕ) [NeZero d]
        (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
        (B₁ B₂ : Finset (Fin d → ℤ))
        (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
        (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
        (Tz : Fin d → ℝ),
      lemma33Hypotheses (c' := c') (δ := δ) (γ := γ) (C' := C')
        N₀ A d W a₀ B₁ B₂ W₁ W₂ Tz →
      (∀ s : Fin d → ℤ, s ∈ gapLattice W₁.P →
        (∀ i, |(s i : ℝ)| ≤ (d : ℝ) * (W.P.width i : ℝ)) →
        ∀ t ∈ (((W₁.k : ℤ) / 2) • W₁.P).toFinset,
          s + t ∈ ((W₁.k : ℤ) • W₁.P).toFinset) ∧
      (∀ s : Fin d → ℤ, s ∈ gapLattice W₂.P →
        (∀ i, |(s i : ℝ)| ≤ (d : ℝ) * (W.P.width i : ℝ)) →
        ∀ t ∈ (((W₂.k : ℤ) / 2) • W₂.P).toFinset,
          s + t ∈ ((W₂.k : ℤ) • W₂.P).toFinset) :=
  sorry

/-- **Lemma 14 (eq. (15) covering)** — assembled from the residual
inputs above:

* (`Āᵢ ⊆ Pᵢ` refinement) `exists_lemma14_lattice`: the shifted pieces
  `Bᵢ ∓ a₀` lie in the lattices `⟨Pᵢ⟩`;
* (absorption) `exists_lemma14_absorption`: a lattice point
  `s ∈ ⟨Pᵢ⟩` coordinatewise bounded by `d·w` is absorbed:
  `s + t ∈ kᵢ·Pᵢ` for every `t ∈ (kᵢ/2)·Pᵢ`;
* (shared-scale data) `exists_lemma13_14_data`: the Lemma-11 column
  bound `C` with its coordinate boxes, the `Tz`-largeness at
  `bound(C)`, and the fat-box covering of `T + ∏[−rᵢ, rᵢ]` for
  `r ≤ bound(C) + 1` — `y − tᵢ − t ∈ 𝒵_{Xᵢ∖A'ᵢ}`.

The column bound `C` is returned existentially (with its boxes,
largeness and covering) so that it can be shared with the covolume
argument downstream — see the caveat at `exists_lemma13_14_data`.
Together with `fat_box_covering` these give the `cov₁`/`cov₂` fields of
`SubSumCoveringSeed`. -/
theorem exists_lemma14_covering {ℓ : ℕ} {c c' δ γ C' : ℝ} :
    ∃ N₀ : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (d : ℕ) [NeZero d]
        (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
        (B₁ B₂ : Finset (Fin d → ℤ))
        (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
        (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
        (Tz : Fin d → ℝ)
        (hli₁ : LinearIndependent ℤ W₁.P.step)
        (hli₂ : LinearIndependent ℤ W₂.P.step),
      NonAveraging A → Irreducible W c' δ γ →
      (Real.log (A.card : ℝ)) ^ (-(1 : ℝ) / C') ≤ γ →
      0 < δ → δ < 1 → 0 < γ → γ < 1 → 4 * δ < 1 →
      N₀ ≤ A.card →
      a₀ ∈ W.imageAh →
      B₁ ⊆ W.imageAh.erase a₀ → B₂ ⊆ W.imageAh.erase a₀ →
      Disjoint B₁ B₂ → B₁ ∪ B₂ = W.imageAh.erase a₀ →
      δ * (A.card : ℝ) ≤ (B₁.card : ℝ) →
      δ * (A.card : ℝ) ≤ (B₂.card : ℝ) →
      (∀ x ∈ B₁, ∀ i, |((x - a₀) i : ℝ)| ≤ (W.P.width i : ℝ)) →
      (∀ x ∈ B₂, ∀ i, |((a₀ - x) i : ℝ)| ≤ (W.P.width i : ℝ)) →
      SubSumDim (B₁.image (· - a₀)) c' = d →
      SubSumDim (B₂.image (a₀ - ·)) c' = d →
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₁.P.toFinset.card : ℝ) →
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₂.P.toFinset.card : ℝ) →
      Tz ∈ zonotope ((B₁.image (· - a₀)).image intVec) →
      Tz ∈ zonotope ((B₂.image (a₀ - ·)).image intVec) →
      (∀ a ∈ B₁.image (· - a₀), a ∈ gapLattice W₁.P) ∧
      (∀ a ∈ B₂.image (a₀ - ·), a ∈ gapLattice W₂.P) ∧
      (∀ s : Fin d → ℤ, s ∈ gapLattice W₁.P →
        (∀ i, |(s i : ℝ)| ≤ (d : ℝ) * (W.P.width i : ℝ)) →
        ∀ t ∈ (((W₁.k : ℤ) / 2) • W₁.P).toFinset,
          s + t ∈ ((W₁.k : ℤ) • W₁.P).toFinset) ∧
      (∀ s : Fin d → ℤ, s ∈ gapLattice W₂.P →
        (∀ i, |(s i : ℝ)| ≤ (d : ℝ) * (W.P.width i : ℝ)) →
        ∀ t ∈ (((W₂.k : ℤ) / 2) • W₂.P).toFinset,
          s + t ∈ ((W₂.k : ℤ) • W₂.P).toFinset) ∧
      ∃ (C lo₁ hi₁ lo₂ hi₂ : Fin d → ℤ),
        (W₁.P.toFinset ⊆
          Fintype.piFinset fun i ↦ Finset.Icc (lo₁ i) (hi₁ i)) ∧
        (W₂.P.toFinset ⊆
          Fintype.piFinset fun i ↦ Finset.Icc (lo₂ i) (hi₂ i)) ∧
        (∀ j i, hi₁ i - lo₁ i ≤ C j) ∧
        (∀ j i, hi₂ i - lo₂ i ≤ C j) ∧
        (∃ i₀, (2 : ℝ) ^ d *
            (((d.factorial * ∏ j, (C j).natAbs) *
              (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) +
          intersectionRoundingSlack hli₁ hli₂ i₀ < |(Tz i₀ : ℝ)|) ∧
        (∀ (T : Fin d → ℤ) (r : Fin d → ℝ),
          T ∈ gapLattice W₁.P → T ∈ gapLattice W₂.P →
          (∀ i, |(T i : ℝ) - Tz i| ≤
            intersectionRoundingSlack hli₁ hli₂ i) →
          (∀ i, 0 ≤ r i) →
          (∀ i, r i ≤ (2 : ℝ) ^ d *
              (((d.factorial * ∏ j, (C j).natAbs) *
                (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) + 1) →
          (∀ y : Fin d → ℤ, (∀ i, |((y - T) i : ℝ)| ≤ r i) →
            ∃ t ∈ (((W₁.k : ℤ) / 2) • W₁.P).toFinset,
              (fun i ↦ (y i : ℝ) - (W₁.t i : ℝ) - (t i : ℝ)) ∈
                zonotope (((B₁.image (· - a₀)) \ W₁.A').image
                  fun x i ↦ (x i : ℝ))) ∧
          (∀ y : Fin d → ℤ, (∀ i, |((y - T) i : ℝ)| ≤ r i) →
            ∃ t ∈ (((W₂.k : ℤ) / 2) • W₂.P).toFinset,
              (fun i ↦ (y i : ℝ) - (W₂.t i : ℝ) - (t i : ℝ)) ∈
                zonotope (((B₂.image (a₀ - ·)) \ W₂.A').image
                  fun x i ↦ (x i : ℝ)))) := by
  classical
  obtain ⟨N₁, hN₁⟩ := exists_lemma14_lattice (ℓ := ℓ) (c := c)
    (c' := c') (δ := δ) (γ := γ) (C' := C')
  obtain ⟨N₂, hN₂⟩ := exists_lemma14_absorption (ℓ := ℓ) (c := c)
    (c' := c') (δ := δ) (γ := γ) (C' := C')
  obtain ⟨N₃, hN₃⟩ := exists_lemma13_14_data (ℓ := ℓ) (c := c)
    (c' := c') (δ := δ) (γ := γ) (C' := C')
  refine ⟨max (max N₁ N₂) N₃, ?_⟩
  intro A d _ W a₀ B₁ B₂ W₁ W₂ Tz hli₁ hli₂ hNA hIrred hγlog hδ hδ1 hγ
    hγ1 hδ4 hN ha₀ hB₁e hB₂e hdisj hcover hδB₁ hδB₂ hb₁ hb₂ hdim₁ hdim₂
    hP₁ hP₂ hTz₁ hTz₂
  have hle₁ : N₁ ≤ A.card :=
    ((le_max_left N₁ N₂).trans (le_max_left _ N₃)).trans hN
  have hle₂ : N₂ ≤ A.card :=
    ((le_max_right N₁ N₂).trans (le_max_left _ N₃)).trans hN
  have hle₃ : N₃ ≤ A.card := (le_max_right _ N₃).trans hN
  obtain ⟨hlat₁, hlat₂⟩ := hN₁ A d W a₀ B₁ B₂ W₁ W₂ Tz
    ⟨hNA, hIrred, hγlog, hδ, hδ1, hγ, hγ1, hδ4, hle₁, ha₀,
      hB₁e, hB₂e, hdisj, hcover, hδB₁, hδB₂, hb₁, hb₂, hdim₁, hdim₂,
      hP₁, hP₂, hTz₁, hTz₂⟩
  obtain ⟨habs₁, habs₂⟩ := hN₂ A d W a₀ B₁ B₂ W₁ W₂ Tz
    ⟨hNA, hIrred, hγlog, hδ, hδ1, hγ, hγ1, hδ4, hle₂, ha₀,
      hB₁e, hB₂e, hdisj, hcover, hδB₁, hδB₂, hb₁, hb₂, hdim₁, hdim₂,
      hP₁, hP₂, hTz₁, hTz₂⟩
  obtain ⟨C, lo₁, hi₁, lo₂, hi₂, hbox₁, hbox₂, hC₁, hC₂, hlarge, hfat⟩ :=
    hN₃ A d W a₀ B₁ B₂ W₁ W₂ Tz hli₁ hli₂
      ⟨hNA, hIrred, hγlog, hδ, hδ1, hγ, hγ1, hδ4, hle₃, ha₀,
        hB₁e, hB₂e, hdisj, hcover, hδB₁, hδB₂, hb₁, hb₂, hdim₁, hdim₂,
        hP₁, hP₂, hTz₁, hTz₂⟩
  exact ⟨hlat₁, hlat₂, habs₁, habs₂,
    C, lo₁, hi₁, lo₂, hi₂, hbox₁, hbox₂, hC₁, hC₂, hlarge, hfat⟩

/-- **The Lemmas 11 (second half)–14 core** — the single remaining
faithful input for Theorem 4.  For all sufficiently large `|A|`, the data
produced by the paper's §3.3 argument — an irreducible `(δ,γ)`-witness
`W` of the non-averaging set `A`, the non-`μ`-convex-position basepoint
`a₀`, the equitable pieces `B₁ ⊔ B₂ = ϕ_P(Â) ∖ {a₀}` with `|Bᵢ| ≥ δ|A|`,
the piecewise minimal witnesses `W₁`, `W₂` for `B₁ ∓ a₀` supplied by
Lemma 11's first half (`SubSumDim = d`, `|Pᵢ| ≥ γ|P|`), the coefficient
box bound `Bᵢ ∓ a₀ ⊆ ∏ [−wⱼ, wⱼ]`, and the common zonotope point
`Tz ∈ 𝒵_{B₁−a₀} ∩ 𝒵_{a₀−B₂}` of eq. (13) — yield a
`SubSumCoveringPackage`.

This bundles exactly the three unformalized ingredients of §3.3:

* **Lemma 11, second half** (`Pᵢ ⊆` translate of `C·B`): gives the step
  bounds `|step_j| ≪ wⱼ`, hence `LinearIndependent ℤ Wᵢ.P.step` and
  `index ⟨Pᵢ⟩ ≤ d!·∏ (C·wⱼ)` via `step_abs_le_of_subset` and
  `index_gapLattice_le` — the `idxᵢ` and `covol_le` inputs.  (In this
  formalization `index ≠ 0` is *not* a consequence of the minimality
  `hdimᵢ`: dependent-step GAPs can be proper minimal-dimension
  witnesses.)
* **Lemma 13 rounding into the intersection lattice**: the real common
  point `Tz` is rounded to `T ∈ ⟨P₁⟩ ∩ ⟨P₂⟩` (another application of
  `exists_ne_zero_mem_inf_mem_box` at scale `≈ |Tz|`; note that the
  Lemma-13 roundings of `Tz` are sums of `Bᵢ ∓ a₀`, and
  `Bᵢ ∓ a₀ ⊄ ⟨Pᵢ⟩`, so lattice membership is part of the input —
  in the paper it is supplied by the `Āᵢ ⊆ Pᵢ` refinement).
  `T_big` is the largeness of `Tz`.
* **Lemma 14 fat-box covering**: `covᵢ` is
  `mem_subsetSumsL_of_zonotope_translate` applied with `X' = Wᵢ.A'`,
  `K = Wᵢ.k`, `q = Wᵢ.t`; its absorption hypothesis `habs` uses the
  `discrete_john_strong` sandwich on `⟨Pᵢ⟩`, and the zonotope
  containment uses the fat box `z̄ᵢ + ξ|A|B ⊆ 𝒵_{Xᵢ ∖ A'ᵢ}`.

The statement is deliberately conditional on the full §3.3 hypothesis
list, with its own threshold `N₀`, so that it is *strictly* the missing
geometric input — every other step of Theorem 4 is formalized.

The conclusion is stated through `SubSumCoveringSeed` (the structure
whose fields are exactly the unformalized ingredients, see its
docstring); `SubSumCoveringSeed.toPackage` then supplies the derived
fields (`idxᵢ`, `covol_le`) of the package. -/
theorem exists_subSumCoveringSeed {ℓ : ℕ} {c c' δ γ C' : ℝ} :
    ∃ N₀ : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (d : ℕ) [NeZero d]
        (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
        (B₁ B₂ : Finset (Fin d → ℤ))
        (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
        (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
        (Tz : Fin d → ℝ),
      NonAveraging A → Irreducible W c' δ γ →
      (Real.log (A.card : ℝ)) ^ (-(1 : ℝ) / C') ≤ γ →
      0 < δ → δ < 1 → 0 < γ → γ < 1 → 4 * δ < 1 →
      N₀ ≤ A.card →
      a₀ ∈ W.imageAh →
      B₁ ⊆ W.imageAh.erase a₀ → B₂ ⊆ W.imageAh.erase a₀ →
      Disjoint B₁ B₂ → B₁ ∪ B₂ = W.imageAh.erase a₀ →
      δ * (A.card : ℝ) ≤ (B₁.card : ℝ) →
      δ * (A.card : ℝ) ≤ (B₂.card : ℝ) →
      (∀ x ∈ B₁, ∀ i, |((x - a₀) i : ℝ)| ≤ (W.P.width i : ℝ)) →
      (∀ x ∈ B₂, ∀ i, |((a₀ - x) i : ℝ)| ≤ (W.P.width i : ℝ)) →
      SubSumDim (B₁.image (· - a₀)) c' = d →
      SubSumDim (B₂.image (a₀ - ·)) c' = d →
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₁.P.toFinset.card : ℝ) →
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₂.P.toFinset.card : ℝ) →
      Tz ∈ zonotope ((B₁.image (· - a₀)).image intVec) →
      Tz ∈ zonotope ((B₂.image (a₀ - ·)).image intVec) →
      Nonempty (SubSumCoveringSeed W₁ W₂) := by
  classical
  obtain ⟨N₁, hN₁⟩ := exists_lemma11_rank (ℓ := ℓ) (c := c) (c' := c')
    (δ := δ) (γ := γ) (C' := C')
  obtain ⟨N₂, hN₂⟩ := exists_lemma14_covering (ℓ := ℓ) (c := c)
    (c' := c') (δ := δ) (γ := γ) (C' := C')
  refine ⟨max N₁ N₂, ?_⟩
  intro A d _ W a₀ B₁ B₂ W₁ W₂ Tz hNA hIrred hγlog hδ hδ1 hγ hγ1 hδ4
    hN ha₀ hB₁e hB₂e hdisj hcover hδB₁ hδB₂ hb₁ hb₂ hdim₁ hdim₂ hP₁ hP₂
    hTz₁ hTz₂
  obtain ⟨hli₁, hli₂⟩ := hN₁ A d W a₀ B₁ B₂ W₁ W₂ Tz
    ⟨hNA, hIrred, hγlog, hδ, hδ1, hγ, hγ1, hδ4,
      (le_max_left N₁ N₂).trans hN, ha₀, hB₁e, hB₂e, hdisj, hcover,
      hδB₁, hδB₂, hb₁, hb₂, hdim₁, hdim₂, hP₁, hP₂, hTz₁, hTz₂⟩
  obtain ⟨hX₁, hX₂, habs₁, habs₂, C, _lo₁, _hi₁, _lo₂, _hi₂,
    hbox₁, hbox₂, hC₁, hC₂, hlarge, hfat⟩ :=
    hN₂ A d W a₀ B₁ B₂ W₁ W₂ Tz hli₁ hli₂ hNA hIrred hγlog hδ hδ1 hγ
      hγ1 hδ4 ((le_max_right N₁ N₂).trans hN) ha₀ hB₁e hB₂e hdisj hcover
      hδB₁ hδB₂ hb₁ hb₂ hdim₁ hdim₂ hP₁ hP₂ hTz₁ hTz₂
  obtain ⟨i₀, hi₀⟩ := hlarge
  obtain ⟨T, hT₁, hT₂, hTclose⟩ :=
    intersectionRoundingSlack_spec hli₁ hli₂ Tz
  -- `T` still exceeds the covolume bound in coordinate `i₀`.
  have hTlt : (2 : ℝ) ^ d *
      (((d.factorial * ∏ j, (C j).natAbs) *
        (d.factorial * ∏ j, (C j).natAbs) : ℕ) : ℝ) < |(T i₀ : ℝ)| := by
    have hclose := hTclose i₀
    have hsub : |(Tz i₀)| - |(T i₀ : ℝ)| ≤ |(T i₀ : ℝ) - Tz i₀| := by
      have h := abs_sub_abs_le_abs_sub (Tz i₀) ((T i₀ : ℤ) : ℝ)
      rwa [abs_sub_comm] at h
    linarith
  obtain ⟨r, hrnn, hrb, hrbig, hrcovol⟩ := seed_radii hTlt
  obtain ⟨hfat₁, hfat₂⟩ :=
    hfat T r hT₁ hT₂ hTclose hrnn hrb
  have hwX0 : ∀ i, 0 ≤ (W.P.width i : ℝ) := fun i ↦ Nat.cast_nonneg _
  have hwX₁ : ∀ a ∈ (B₁.image (· - a₀)) \ W₁.A', ∀ i,
      |(a i : ℝ)| ≤ (W.P.width i : ℝ) := by
    intro a ha i
    obtain ⟨x, hx, rfl⟩ :=
      Finset.mem_image.mp (Finset.mem_sdiff.mp ha).1
    exact hb₁ x hx i
  have hwX₂ : ∀ a ∈ (B₂.image (a₀ - ·)) \ W₂.A', ∀ i,
      |(a i : ℝ)| ≤ (W.P.width i : ℝ) := by
    intro a ha i
    obtain ⟨x, hx, rfl⟩ :=
      Finset.mem_image.mp (Finset.mem_sdiff.mp ha).1
    exact hb₂ x hx i
  exact ⟨{ li₁ := hli₁, li₂ := hli₂, C := C,
           step₁ := lemma11_step_bound hbox₁ ⟨0, W₁.zero_mem_toFinset⟩
             (fun j ↦ W₁.two_le_width hdim₁ j) hC₁,
           step₂ := lemma11_step_bound hbox₂ ⟨0, W₂.zero_mem_toFinset⟩
             (fun j ↦ W₂.two_le_width hdim₂ j) hC₂,
           T := T, T_mem₁ := hT₁, T_mem₂ := hT₂, r := r,
           r_nonneg := hrnn, T_big := hrbig, r_covol := hrcovol,
           cov₁ := fat_box_covering W₁ hwX0 hwX₁ hX₁ habs₁ hfat₁,
           cov₂ := fat_box_covering W₂ hwX0 hwX₂ hX₂ habs₂ hfat₂ }⟩

/-- The covering package of Lemmas 11–14, obtained from the seed input
`exists_subSumCoveringSeed` via `SubSumCoveringSeed.toPackage`. -/
theorem exists_subSumCoveringPackage {ℓ : ℕ} {c c' δ γ C' : ℝ} :
    ∃ N₀ : ℕ, ∀ (A : Finset (Fin ℓ → ℤ)) (d : ℕ) [NeZero d]
        (W : SubSumWitness A c d) (a₀ : Fin d → ℤ)
        (B₁ B₂ : Finset (Fin d → ℤ))
        (W₁ : SubSumWitness (B₁.image (· - a₀)) c' d)
        (W₂ : SubSumWitness (B₂.image (a₀ - ·)) c' d)
        (Tz : Fin d → ℝ),
      NonAveraging A → Irreducible W c' δ γ →
      (Real.log (A.card : ℝ)) ^ (-(1 : ℝ) / C') ≤ γ →
      0 < δ → δ < 1 → 0 < γ → γ < 1 → 4 * δ < 1 →
      N₀ ≤ A.card →
      a₀ ∈ W.imageAh →
      B₁ ⊆ W.imageAh.erase a₀ → B₂ ⊆ W.imageAh.erase a₀ →
      Disjoint B₁ B₂ → B₁ ∪ B₂ = W.imageAh.erase a₀ →
      δ * (A.card : ℝ) ≤ (B₁.card : ℝ) →
      δ * (A.card : ℝ) ≤ (B₂.card : ℝ) →
      (∀ x ∈ B₁, ∀ i, |((x - a₀) i : ℝ)| ≤ (W.P.width i : ℝ)) →
      (∀ x ∈ B₂, ∀ i, |((a₀ - x) i : ℝ)| ≤ (W.P.width i : ℝ)) →
      SubSumDim (B₁.image (· - a₀)) c' = d →
      SubSumDim (B₂.image (a₀ - ·)) c' = d →
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₁.P.toFinset.card : ℝ) →
      (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W₂.P.toFinset.card : ℝ) →
      Tz ∈ zonotope ((B₁.image (· - a₀)).image intVec) →
      Tz ∈ zonotope ((B₂.image (a₀ - ·)).image intVec) →
      Nonempty (SubSumCoveringPackage W₁ W₂) := by
  obtain ⟨N₀, hN₀⟩ := exists_subSumCoveringSeed (ℓ := ℓ) (c := c)
    (c' := c') (δ := δ) (γ := γ) (C' := C')
  refine ⟨N₀, ?_⟩
  intro A d _ W a₀ B₁ B₂ W₁ W₂ Tz hNA hIrred hγlog hδ hδ1 hγ hγ1 hδ4
    hN ha₀ hB₁e hB₂e hdisj hcover hδB₁ hδB₂ hb₁ hb₂ hdim₁ hdim₂ hP₁ hP₂
    hTz₁ hTz₂
  obtain ⟨s⟩ := hN₀ A d W a₀ B₁ B₂ W₁ W₂ Tz hNA hIrred hγlog hδ hδ1 hγ
    hγ1 hδ4 hN ha₀ hB₁e hB₂e hdisj hcover hδB₁ hδB₂ hb₁ hb₂ hdim₁ hdim₂
    hP₁ hP₂ hTz₁ hTz₂
  exact ⟨s.toPackage⟩

/-- **Theorem 4** (contrapositive form used in §4).  There is a threshold
`N` such that whenever `A ⊆ B ⊆ ℤ^ℓ` is non-averaging, `|B| ≤ |A|^β`,
`(δ,γ)`-irreducible via its canonical witness `W` (so `d = d(A)` and
`P = P(A)`), `γ ≥ (log|A|)^{−1/C'}` and `|A| ≥ N`, the embedded image
`ϕ_P(Â)` (viewed in `ℝ^d`) is in `μ`-convex position — otherwise Lemmas
11–14 produce `a ∈ A` and disjoint nonempty `Ã₁, Ã₂ ⊆ A ∖ {a}` with
`Σ(Ã₁ − a) = Σ(a − Ã₂)`, contradicting `NonAveraging.subsetSum_eq_zero`.
Here `C` plays the role of the paper's sufficiently large constants with
`γ ≤ δ^C` and `δ ≤ μ^C`.  The additional hypothesis `hδ4 : 4δ < 1` is the
paper's standing assumption `δ < 1/4` (in the intended parameter regime
`δ = (log log)^{-κ} → 0`, so `δ < 1/4` for all large `|A|`); it is what
lets irreducibility be applied to the two halves `B₁, B₂` of the
equitable split (`δ·|A| ≤ |Bᵢ|`). -/
theorem embedded_in_mu_convex_position {ℓ : ℕ} {β c c' δ γ μ C C' : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hμ : 0 < μ) (hμ1 : μ < 1)
    (hγδ : γ ≤ δ ^ C) (hδμ : δ ≤ μ ^ C) (hδ4 : 4 * δ < 1) :
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
  -- The threshold `N` also enforces `|A| ≥ 6/(1−4δ)` so that the
  -- equitable halves satisfy `|Bᵢ| ≥ δ·|A|` (via `δ < 1/4`).
  -- The Lemmas 11–14 covering package (the single remaining input, see
  -- `exists_subSumCoveringPackage`) is quantified by its own threshold
  -- `N₀`; take `N` to dominate both thresholds.
  obtain ⟨N₀, hN₀⟩ := exists_subSumCoveringPackage (ℓ := ℓ) (c := c)
    (c' := c') (δ := δ) (γ := γ) (C' := C')
  refine ⟨max (⌈Real.exp (max (max (2 / c) (1 / (c * (1 - δ)))) 1)⌉₊ + 3 +
      ⌈6 / (1 - 4 * δ)⌉₊) N₀, ?_⟩
  intro A B d W hBint hNA hAB hBcard hIrred hγlog hN
  have hN' : ⌈Real.exp (max (max (2 / c) (1 / (c * (1 - δ)))) 1)⌉₊ + 3 +
      ⌈6 / (1 - 4 * δ)⌉₊ ≤ A.card := (le_max_left _ _).trans hN
  have hNN₀ : N₀ ≤ A.card := (le_max_right _ _).trans hN
  have hc : 0 < c := W.cpos
  have hN3 : 3 ≤ A.card := by
    have : 3 ≤ ⌈Real.exp (max (max (2 / c) (1 / (c * (1 - δ)))) 1)⌉₊ +
        3 + ⌈6 / (1 - 4 * δ)⌉₊ := by omega
    exact this.trans hN'
  have hA3 : (3 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hN3
  have hApos : (0 : ℝ) < (A.card : ℝ) := by linarith
  have hexp : Real.exp (max (max (2 / c) (1 / (c * (1 - δ)))) 1)
      ≤ (A.card : ℝ) :=
    (Nat.le_ceil _).trans
      (by exact_mod_cast ((Nat.le_add_right _ _).trans
        (Nat.le_add_right _ _)).trans hN')
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
    have hinv : (c * Real.log (A.card : ℝ))⁻¹ ≤ 1 - δ := by
      rw [inv_le_iff_one_le_mul₀ hcl]
      calc (1 : ℝ) ≤ (c * (1 - δ)) * Real.log (A.card : ℝ) := hclogd
        _ = (1 - δ) * (c * Real.log (A.card : ℝ)) := by ring
    rw [hkey]
    calc (A.card : ℝ) * (c * Real.log (A.card : ℝ))⁻¹
        ≤ (A.card : ℝ) * (1 - δ) :=
          mul_le_mul_of_nonneg_left hinv hApos.le
      _ = (1 - δ) * (A.card : ℝ) := by ring
  have hfrach : c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ)
      ≤ (A.card : ℝ) / 2 := by
    have hinv : (c * Real.log (A.card : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num : (0 : ℝ) < 2) hclog2
    rw [hkey]
    calc (A.card : ℝ) * (c * Real.log (A.card : ℝ))⁻¹
        ≤ (A.card : ℝ) * (2 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv hApos.le
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
  obtain ⟨a₀, ha₀, D₁, D₂, hD₁e, hD₂e, hdisjD, hcoverD, hw₁, hw₂, w, hw0,
    hwb, hws, hvec⟩ := W.not_inConvexPosition_imageAh_split hμ hconv
  -- The weighted displacements over `S₀ := imageAh ∖ {a₀}` cancel: the
  -- two halves of the split of equation (13) sum to opposite vectors.
  set S₀ := W.imageAh.erase a₀ with hS₀def
  have hS₀zero : ∑ x ∈ S₀, w x • intVec (x - a₀) = 0 := by
    rw [← hcoverD, Finset.sum_union hdisjD, hvec]
    exact neg_add_cancel _
  -- Re-split `S₀ = B₁ ⊔ B₂` equitably.  (The paper takes the split given
  -- by convex position, which additionally balances the total weight;
  -- for `z₁ = z₂` only the vanishing total matters, while the
  -- irreducibility step needs `|Bᵢ| ≥ δ|A|` — guaranteed by an equitable
  -- split once `δ < 1/4` asymptotically, cf. `hB₁sz`/`hB₂sz` below.)
  obtain ⟨B₁, hB₁sub₀, hB₁card⟩ := Finset.exists_subset_card_eq
    (show S₀.card / 2 ≤ S₀.card from Nat.div_le_self _ _)
  set B₂ := S₀ \ B₁ with hB₂def
  have hB₂sub₀ : B₂ ⊆ S₀ := Finset.sdiff_subset
  have hcover : B₁ ∪ B₂ = S₀ := Finset.union_sdiff_of_subset hB₁sub₀
  have hdisj : Disjoint B₁ B₂ := Finset.disjoint_sdiff
  have hB₁e : B₁ ⊆ W.imageAh.erase a₀ := hB₁sub₀
  have hB₂e : B₂ ⊆ W.imageAh.erase a₀ := hB₂sub₀
  -- The displacements over the new halves still cancel.
  have hvecB : ∑ x ∈ B₁, w x • intVec (x - a₀)
      = -(∑ x ∈ B₂, w x • intVec (x - a₀)) := by
    have hBsum : ∑ x ∈ S₀, w x • intVec (x - a₀)
        = ∑ x ∈ B₁, w x • intVec (x - a₀)
          + ∑ x ∈ B₂, w x • intVec (x - a₀) := by
      rw [← hcover, Finset.sum_union hdisj]
    rw [hBsum] at hS₀zero
    exact eq_neg_of_add_eq_zero_left hS₀zero
  -- Size bookkeeping: `|S₀| = |Â| − 1` and both parts have
  -- `|Bᵢ| ≥ (|Â| − 3)/2 ≥ |A|/4 − 3/2`.
  have hAh2 : 2 ≤ W.Ah.card := by
    have h15 : (3 / 2 : ℝ) ≤ (W.Ah.card : ℝ) := by
      have hA3' : (3 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA3
      linarith [hAhh]
    have h1 : (1 : ℝ) < (W.Ah.card : ℝ) := by linarith
    exact Nat.succ_le_of_lt (Nat.one_lt_cast.mp h1)
  have hS₀card : S₀.card = W.Ah.card - 1 := by
    rw [hS₀def, Finset.card_erase_of_mem ha₀, W.card_imageAh]
  have hS₀cardR : (S₀.card : ℝ) = (W.Ah.card : ℝ) - 1 := by
    rw [hS₀card, Nat.cast_sub (by omega : 1 ≤ W.Ah.card), Nat.cast_one]
  have hdiv2 : (S₀.card : ℝ) ≤ 2 * ((S₀.card / 2 : ℕ) : ℝ) + 1 := by
    have e : S₀.card ≤ 2 * (S₀.card / 2) + 1 := by omega
    exact_mod_cast e
  have hB₁sz : ((W.Ah.card : ℝ) - 3) / 2 ≤ (B₁.card : ℝ) := by
    rw [hB₁card]
    linarith [hS₀cardR, hdiv2]
  have hB₂sz : ((W.Ah.card : ℝ) - 3) / 2 ≤ (B₂.card : ℝ) := by
    have hle : S₀.card / 2 ≤ B₂.card := by
      rw [hB₂def, Finset.card_sdiff_of_subset hB₁sub₀, hB₁card]
      omega
    have hle' : ((S₀.card / 2 : ℕ) : ℝ) ≤ (B₂.card : ℝ) := by
      exact_mod_cast hle
    linarith [hS₀cardR, hdiv2]
  -- === Step 1 (paper eq. (13)): the balanced displacement
  -- `T := Σ_{B₁} w_x • (x − a₀) = Σ_{B₂} w_x • (a₀ − x)` lies in both
  -- zonotopes after rescaling by `r := μ·|Â|` (which is `≥ 1` since
  -- `¬InDeltaConvexPosition` already forced `μ|Â| ≥ 1`).
  have hr : 0 < μ * (W.Ah.card : ℝ) :=
    mul_pos hμ (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hAh2))
  have hT₁ : (μ * (W.Ah.card : ℝ)) • (∑ x ∈ B₁, w x • intVec (x - a₀)) ∈
      zonotope ((B₁.image (· - a₀)).image intVec) :=
    smul_sum_mem_zonotope_image_sub B₁ a₀ hr
      (fun x hx ↦ hw0 x ((Finset.mem_erase.mp (hB₁e hx)).2))
      (fun x hx ↦ hwb x ((Finset.mem_erase.mp (hB₁e hx)).2))
  have hT₂ : (μ * (W.Ah.card : ℝ)) • (∑ x ∈ B₂, w x • intVec (a₀ - x)) ∈
      zonotope ((B₂.image (a₀ - ·)).image intVec) :=
    smul_sum_mem_zonotope_image_const_sub B₂ a₀ hr
      (fun x hx ↦ hw0 x ((Finset.mem_erase.mp (hB₂e hx)).2))
      (fun x hx ↦ hwb x ((Finset.mem_erase.mp (hB₂e hx)).2))
  -- The two rescaled sums coincide: `intVec (a₀ − x) = − intVec (x − a₀)`
  -- pointwise and `hvecB` supplies the cancellation.
  have hTeq : (μ * (W.Ah.card : ℝ)) • (∑ x ∈ B₁, w x • intVec (x - a₀))
      = (μ * (W.Ah.card : ℝ)) • (∑ x ∈ B₂, w x • intVec (a₀ - x)) := by
    have e : ∀ x : Fin d → ℤ, intVec (a₀ - x) = -intVec (x - a₀) := by
      intro x
      funext i
      show ((a₀ - x) i : ℝ) = -(((x - a₀) i : ℤ) : ℝ)
      rw [Pi.sub_apply, Pi.sub_apply, Int.cast_sub, Int.cast_sub]
      ring
    have hneg : ∑ x ∈ B₂, w x • intVec (a₀ - x)
        = -(∑ x ∈ B₂, w x • intVec (x - a₀)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [e, smul_neg]
    rw [hneg, ← hvecB]
  -- === Step 2 (Lemma 13): `T` is within `d·wᵢ` of an honest integer
  -- subset sum in each of `Σ(B₁ − a₀)`, `Σ(a₀ − B₂)`.  The width bound
  -- uses `x, a₀ ∈ ϕ_P(P) ⊆ ∏[0,wᵢ)` (`GAP.abs_sub_apply_le_width`).
  have hPa₀ : a₀ ∈ W.P.coeffBox.toFinset :=
    W.imageP_subset_coeffBox (W.imageAh_subset_imageP ha₀)
  have hb₁ : ∀ x ∈ B₁, ∀ i,
      |(((x - a₀) i : ℤ) : ℝ)| ≤ (W.P.width i : ℝ) := fun x hx i ↦
    W.P.abs_sub_apply_le_width
      (W.imageP_subset_coeffBox
        (W.imageAh_subset_imageP (Finset.mem_erase.mp (hB₁e hx)).2))
      hPa₀ i
  have hb₂ : ∀ x ∈ B₂, ∀ i,
      |(((a₀ - x) i : ℤ) : ℝ)| ≤ (W.P.width i : ℝ) := fun x hx i ↦
    W.P.abs_sub_apply_le_width hPa₀
      (W.imageP_subset_coeffBox
        (W.imageAh_subset_imageP (Finset.mem_erase.mp (hB₂e hx)).2))
      i
  obtain ⟨S₁', hS₁', hclose₁⟩ := exists_subset_sum_int_close
    sub_left_injective hT₁ (fun i ↦ Nat.cast_nonneg _) hb₁
  obtain ⟨S₂', hS₂', hclose₂⟩ := exists_subset_sum_int_close
    sub_right_injective hT₂ (fun i ↦ Nat.cast_nonneg _) hb₂
  -- === Step 3 (Lemma 11): `δ < 1/4` (hypothesis `hδ4`) together with
  -- `|A| ≥ 6/(1−4δ)` (built into `N`) gives
  -- `δ·|A| ≤ |A|/4 − 3/2 ≤ (|Â|−3)/2 ≤ |Bᵢ|`, so irreducibility applies
  -- to the two halves of the equitable split themselves, producing
  -- `d`-dimensional witnesses `W₁`, `W₂` for `B₁ − a₀` and `a₀ − B₂`
  -- with `|Pᵢ| ≥ γ|P|` — exactly the paper's `P₁ = P(A₁ − a)`,
  -- `P₂ = P(a − A₂)`.
  have hden : (0 : ℝ) < 1 - 4 * δ := by linarith [hδ4]
  have hAceil : (6 : ℝ) / (1 - 4 * δ) ≤ (A.card : ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (Nat.le_add_left _ _).trans hN'
  have hAmain : δ * (A.card : ℝ) ≤ (A.card : ℝ) / 4 - 3 / 2 := by
    have h6 : (6 : ℝ) ≤ (A.card : ℝ) * (1 - 4 * δ) := by
      rwa [div_le_iff₀ hden] at hAceil
    nlinarith [h6, hApos]
  have hδB₁ : δ * (A.card : ℝ) ≤ (B₁.card : ℝ) := by
    linarith [hAmain, hAhh, hB₁sz]
  have hδB₂ : δ * (A.card : ℝ) ≤ (B₂.card : ℝ) := by
    linarith [hAmain, hAhh, hB₂sz]
  obtain ⟨W₁, hdim₁, hP₁⟩ := hIrred.exists_witness_image_sub
    (hB₁e.trans (Finset.erase_subset _ _)) hδB₁
    (W.imageAh_subset_imageP ha₀)
  obtain ⟨W₂, hdim₂, hP₂⟩ := hIrred.exists_witness_image_const_sub
    (hB₂e.trans (Finset.erase_subset _ _)) hδB₂
    (W.imageAh_subset_imageP ha₀)
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
      GAP.nonAveraging_ptCoeffImage W.P W.hAhP (NonAveraging.mono W.hAh hNA)
    exact NonAveraging.not_subsetSum_shift_eq hNA' ha₀
      (hÃ₁sub.trans hB₁e) (hÃ₂sub.trans hB₂e) (hdisj.mono hÃ₁sub hÃ₂sub)
      hnonempty (hsum1.trans hsum2.symm)
  -- === The Lemmas 12–14 core ===
  -- It remains to produce a nonzero `v ∈ Σ(B₁ − a₀) ∩ Σ(a₀ − B₂)`.
  -- What is in place (this proof + the helpers above and
  -- `Nonaveraging.DiscreteJohn`):
  --   * the equitable split `S₀ = B₁ ⊔ B₂` with `|Bᵢ| ≥ (|Â|−3)/2`
  --     (`hB₁sz`, `hB₂sz`) and balanced displacement `hvecB`;
  --   * `r·T ∈ 𝒵` for both translated images (`hT₁`, `hT₂`, `hTeq`);
  --   * the Lemma-13 roundings `S₁' ⊆ B₁−a₀`, `S₂' ⊆ a₀−B₂` at distance
  --     `≤ d·wᵢ` of `r·T` (`hclose₁`, `hclose₂`);
  --   * `δ·|A| ≤ |Bᵢ|` (`hδB₁`, `hδB₂`, from `hδ4 : δ < 1/4` and
  --     `|A| ≥ 6/(1−4δ)`), so irreducibility yields `d`-dimensional
  --     witnesses `W₁`, `W₂` for `B₁ ∓ a₀` with `|Pᵢ| ≥ γ|P|`
  --     (`hdim₁`, `hP₁`, `hdim₂`, `hP₂`);
  --   * `exists_ne_zero_subsetSum_inter` (DiscreteJohn): given a common
  --     lattice point `T ∈ ⟨W₁.P⟩ ∩ ⟨W₂.P⟩`, a coordinate box of radii
  --     `rᵢ` with `2^d·index(⟨P₁⟩)·index(⟨P₂⟩) ≤ ∏ rᵢ`, and the covering
  --     property that every `⟨Pᵢ⟩`-point within `r` of `T` is a subset
  --     sum of `Bᵢ ∓ a₀`, produces exactly the required `v`.
  -- === Nondegeneracy data available from minimality ===
  -- `SubSumDim (Bᵢ ∓ a₀) = d` is the minimum, so `Wᵢ.P` has no `width 1`
  -- step (else `SubSumWitness.dropTrivialStep` gives a `(d−1)`-witness).
  -- Hence `2 ≤ Wᵢ.P.width j` — discharging the `hj` hypothesis of
  -- `step_abs_le_of_subset` for the eventual covolume bound — and
  -- `Wᵢ.P.step j ≠ 0` (properness would otherwise collide `0` and `eⱼ`).
  -- We also record the eq. (15) lattice memberships: `tᵢ ∈ ⟨Pᵢ⟩`,
  -- `Âᵢ ⊆ ⟨Pᵢ⟩`, `Σ(A'ᵢ) ⊆ ⟨Pᵢ⟩`, and `kᵢPᵢ + tᵢ ⊆ Σ(Bᵢ ∓ a₀)`.
  have hw₁ : ∀ j, 2 ≤ W₁.P.width j := fun j ↦ W₁.two_le_width hdim₁ j
  have hw₂ : ∀ j, 2 ≤ W₂.P.width j := fun j ↦ W₂.two_le_width hdim₂ j
  have hstep₁ : ∀ j, W₁.P.step j ≠ 0 := fun j ↦ W₁.step_ne_zero hdim₁ j
  have hstep₂ : ∀ j, W₂.P.step j ≠ 0 := fun j ↦ W₂.step_ne_zero hdim₂ j
  have htL₁ : W₁.t ∈ gapLattice W₁.P := W₁.t_mem_gapLattice
  have htL₂ : W₂.t ∈ gapLattice W₂.P := W₂.t_mem_gapLattice
  have hAhL₁ : ∀ a ∈ W₁.Ah, a ∈ gapLattice W₁.P := fun a ha ↦
    W₁.Ah_mem_gapLattice ha
  have hAhL₂ : ∀ a ∈ W₂.Ah, a ∈ gapLattice W₂.P := fun a ha ↦
    W₂.Ah_mem_gapLattice ha
  have hSigL₁ : ∀ x ∈ GAP.subsetSumsL W₁.A', x ∈ gapLattice W₁.P :=
    fun x hx ↦ W₁.mem_gapLattice_of_mem_subsetSumsL_A' hx
  have hSigL₂ : ∀ x ∈ GAP.subsetSumsL W₂.A', x ∈ gapLattice W₂.P :=
    fun x hx ↦ W₂.mem_gapLattice_of_mem_subsetSumsL_A' hx
  have htr₁ : ((W₁.k • W₁.P).translate W₁.t).toFinset ⊆
      GAP.subsetSumsL (B₁.image (· - a₀)) := W₁.subsetSumsL_superset
  have htr₂ : ((W₂.k • W₂.P).translate W₂.t).toFinset ⊆
      GAP.subsetSumsL (B₂.image (a₀ - ·)) := W₂.subsetSumsL_superset
  -- === The residual: the Lemmas 11–14 covering package ===
  -- The single remaining faithful input is
  -- `exists_subSumCoveringPackage` (defined and documented just above
  -- Theorem 4): it packages Lemma 11's second half (`Pᵢ ⊆ C·B`, which
  -- supplies both the `⟨Pᵢ⟩`-rank `index ≠ 0` and the covolume bound via
  -- `step_abs_le_of_subset` + `index_gapLattice_le`), the Lemma-13
  -- rounding of the common zonotope point into `⟨P₁⟩ ∩ ⟨P₂⟩`, and the
  -- Lemma-14 fat-box covering (eq. (15)).  Everything else — the
  -- Minkowski assembly `exists_ne_zero_subsetSum_inter` and the
  -- contradiction with `NonAveraging.not_subsetSum_shift_eq` — is
  -- proved.
  haveI : NeZero d := ⟨hd⟩
  have hTz₂ : (μ * (W.Ah.card : ℝ)) • (∑ x ∈ B₁, w x • intVec (x - a₀)) ∈
      zonotope ((B₂.image (a₀ - ·)).image intVec) := by
    rw [hTeq]
    exact hT₂
  obtain ⟨cov⟩ := hN₀ A d W a₀ B₁ B₂ W₁ W₂
    ((μ * (W.Ah.card : ℝ)) • ∑ x ∈ B₁, w x • intVec (x - a₀))
    hNA hIrred hγlog hδ hδ1 hγ hγ1 hδ4 hNN₀ ha₀
    hB₁e hB₂e hdisj (hcover.trans hS₀def) hδB₁ hδB₂ hb₁ hb₂
    hdim₁ hdim₂ hP₁ hP₂ hT₁ hTz₂
  exact cov.exists_common_subsetSum

end Nonaveraging
