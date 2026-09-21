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

open Finset Asymptotics Filter

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

/-- The *centered* GAP `{∑ rᵢ • qᵢ : rᵢ ∈ [−Nᵢ, Nᵢ]}`, expressed in `GAP`
form as `base = −∑ Nᵢ • qᵢ`, `widthᵢ = 2Nᵢ + 1`.  Centered GAPs are
homogeneous and symmetric about `0`; they are the normal form used for the
GAP `P` in the CFP structure theorem (cf. CFP23 §5, where it is noted that
`P` may be taken symmetric at the cost of at most doubling the widths). -/
def centered (q : Fin d → (Fin ℓ → ℤ)) (N : Fin d → ℕ) : GAP ℓ d where
  base := -(∑ i, (N i : ℤ) • q i)
  step := q
  width := fun i ↦ 2 * N i + 1

theorem centered_eval (q : Fin d → (Fin ℓ → ℤ)) (N : Fin d → ℕ)
    (n : Fin d → ℕ) :
    (centered q N).eval n = ∑ i, ((n i : ℤ) - N i) • q i := by
  simp only [centered, eval, sub_smul, Finset.sum_sub_distrib]
  rw [sub_eq_add_neg, add_comm]

/-- Membership in a centered GAP: sums `∑ rᵢ • qᵢ` with `|rᵢ| ≤ Nᵢ`. -/
theorem mem_centered {q : Fin d → (Fin ℓ → ℤ)} {N : Fin d → ℕ}
    {x : Fin ℓ → ℤ} :
    x ∈ (centered q N).toFinset ↔
      ∃ r : Fin d → ℤ, (∀ i, |r i| ≤ (N i : ℤ)) ∧ x = ∑ i, r i • q i := by
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hn
    refine ⟨fun i ↦ ((m i : ℕ) : ℤ) - (N i : ℤ), fun i ↦ ?_,
      centered_eval q N (fun i ↦ (m i : ℕ))⟩
    have hlt : (m i : ℕ) ≤ 2 * N i := by
      have h : (m i : ℕ) < 2 * N i + 1 := (m i).isLt
      omega
    have hle : ((m i : ℕ) : ℤ) ≤ 2 * (N i : ℤ) := by exact_mod_cast hlt
    have hnn : (0 : ℤ) ≤ ((m i : ℕ) : ℤ) := by positivity
    show |(m i : ℤ) - (N i : ℤ)| ≤ (N i : ℤ)
    rw [abs_le]; constructor <;> omega
  · rintro ⟨r, hr, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨fun i ↦ (r i + N i).toNat, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨fun i ↦ ⟨(r i + N i).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
      · have hri := abs_le.mp (hr i)
        show (r i + N i).toNat < 2 * N i + 1
        omega
      · ext i; simp
    · rw [centered_eval]
      apply Finset.sum_congr rfl; intro i _
      have hri := abs_le.mp (hr i)
      have hnonneg : (0 : ℤ) ≤ r i + N i := by omega
      congr 1
      rw [Int.toNat_of_nonneg hnonneg]
      omega

/-- A centered GAP is symmetric about `0`. -/
theorem centered_symmetric (q : Fin d → (Fin ℓ → ℤ)) (N : Fin d → ℕ) :
    (centered q N).Symmetric := by
  refine ⟨0, fun x hx ↦ ?_⟩
  obtain ⟨r, hr, rfl⟩ := mem_centered.mp hx
  apply mem_centered.mpr
  refine ⟨fun i ↦ -r i, fun i ↦ by simpa using hr i, ?_⟩
  simp [neg_smul, Finset.sum_neg_distrib]

/-- A centered GAP is homogeneous (its base is `∑ (−Nᵢ) • qᵢ`). -/
theorem centered_homogeneous (q : Fin d → (Fin ℓ → ℤ)) (N : Fin d → ℕ) :
    (centered q N).Homogeneous :=
  ⟨fun i ↦ -(N i : ℤ), by simp [centered, neg_smul, Finset.sum_neg_distrib]⟩

/-- `0` belongs to every centered GAP. -/
theorem zero_mem_centered (q : Fin d → (Fin ℓ → ℤ)) (N : Fin d → ℕ) :
    (0 : Fin ℓ → ℤ) ∈ (centered q N).toFinset :=
  mem_centered.mpr ⟨0, fun i ↦ by simp, by simp⟩

/-- The base-`H` packing `a ↦ ∑ⱼ aⱼ Hʲ` used in the Appendix-A encoding
`φ : (−H/2, H/2]^ℓ → ℤ` of Pham–Zakharov (arXiv:2410.14624v2, Appendix A).
It is additive and injective on the balanced box `|aⱼ| < H/2`. -/
def packVec (H : ℤ) {ℓ : ℕ} (a : Fin ℓ → ℤ) : ℤ :=
  ∑ j, a j * H ^ j.val

theorem packVec_zero (H : ℤ) {ℓ : ℕ} : packVec H (0 : Fin ℓ → ℤ) = 0 := by
  simp [packVec]

theorem packVec_add (H : ℤ) {ℓ : ℕ} (a b : Fin ℓ → ℤ) :
    packVec H (a + b) = packVec H a + packVec H b := by
  simp [packVec, add_mul, Finset.sum_add_distrib]

theorem packVec_neg (H : ℤ) {ℓ : ℕ} (a : Fin ℓ → ℤ) :
    packVec H (-a) = -packVec H a := by
  simp [packVec, neg_mul, Finset.sum_neg_distrib]

theorem packVec_sub (H : ℤ) {ℓ : ℕ} (a b : Fin ℓ → ℤ) :
    packVec H (a - b) = packVec H a - packVec H b := by
  rw [sub_eq_add_neg, packVec_add, packVec_neg, sub_eq_add_neg]

theorem packVec_smul (H : ℤ) {ℓ : ℕ} (t : ℤ) (a : Fin ℓ → ℤ) :
    packVec H (t • a) = t * packVec H a := by
  simp [packVec, mul_assoc, Finset.mul_sum]

/-- `packVec` as an additive group homomorphism `(Fin ℓ → ℤ) →+ ℤ`. -/
def packVecHom (H : ℤ) {ℓ : ℕ} : (Fin ℓ → ℤ) →+ ℤ where
  toFun := packVec H
  map_zero' := packVec_zero H
  map_add' := packVec_add H

/-- `packVec` commutes with finite sums: `φ(∑ S) = ∑ φ(S)`.  This is the
additive-transfer step used to compare `Σ(A')` with `Σ(φ(A'))`. -/
theorem packVec_sum (H : ℤ) {ℓ : ℕ} (S : Finset (Fin ℓ → ℤ)) :
    packVec H (∑ x ∈ S, x) = ∑ x ∈ S, packVec H x :=
  map_sum (packVecHom H) _ S

/-- **Balanced-digit uniqueness** for `packVec`: on the box
`|aⱼ| ≤ K` with `2K < H`, the packing `∑ⱼ aⱼ Hʲ` is injective.
This is the injectivity of `φ` on `(−H/2, H/2]^ℓ` used in Appendix A. -/
theorem packVec_inj {H : ℤ} (hH : 0 < H) {K : ℤ} (h2K : 2 * K < H) :
    ∀ {ℓ : ℕ} (a b : Fin ℓ → ℤ),
      (∀ j, |a j| ≤ K) → (∀ j, |b j| ≤ K) →
      packVec H a = packVec H b → a = b := by
  intro ℓ
  induction ℓ with
  | zero => intro a b _ _ _; exact Subsingleton.elim _ _
  | succ ℓ ih =>
    intro a b ha hb hab
    have hsplit : ∀ v : Fin (ℓ + 1) → ℤ,
        packVec H v = v 0 + H * packVec H (fun j ↦ v j.succ) := by
      intro v
      unfold packVec
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsplit a, hsplit b] at hab
    have ha0 : a 0 = b 0 := by
      have h1 : |a 0 - b 0| ≤ 2 * K := by
        have h1 := abs_le.mp (ha 0)
        have h2 := abs_le.mp (hb 0)
        rw [abs_le]
        omega
      have ht : packVec H (fun j ↦ b j.succ) -
          packVec H (fun j ↦ a j.succ) = 0 := by
        have hdvd : a 0 - b 0 =
            H * (packVec H (fun j ↦ b j.succ) - packVec H (fun j ↦ a j.succ)) := by
          linarith
        by_contra hne
        have hge : (1 : ℤ) ≤
            |packVec H (fun j ↦ b j.succ) - packVec H (fun j ↦ a j.succ)| :=
          abs_pos.mpr hne
        rw [hdvd, abs_mul, abs_of_pos hH] at h1
        have hge2 : H * 1 ≤ H *
            |packVec H (fun j ↦ b j.succ) - packVec H (fun j ↦ a j.succ)| :=
          mul_le_mul_of_nonneg_left hge hH.le
        omega
      have hpp : packVec H (fun j ↦ a j.succ) =
          packVec H (fun j ↦ b j.succ) := by omega
      have hHp : H * packVec H (fun j ↦ a j.succ) =
          H * packVec H (fun j ↦ b j.succ) := by rw [hpp]
      omega
    have htail : (fun j : Fin ℓ ↦ a j.succ) = (fun j : Fin ℓ ↦ b j.succ) := by
      have hpeq : packVec H (fun j ↦ a j.succ) = packVec H (fun j ↦ b j.succ) := by
        have hmul : H * packVec H (fun j ↦ a j.succ) =
            H * packVec H (fun j ↦ b j.succ) := by omega
        exact mul_left_cancel₀ hH.ne' hmul
      exact ih _ _ (fun j : Fin ℓ ↦ ha j.succ) (fun j : Fin ℓ ↦ hb j.succ) hpeq
    funext j
    exact Fin.cases ha0 (fun i ↦ congrFun htail i) j

/-- `packVec` is injective on any finite set all of whose elements have
coordinates in `[−K, K]` with `2K < H`. -/
theorem packVec_injOn {H : ℤ} (hH : 0 < H) {K : ℤ} (h2K : 2 * K < H) {ℓ : ℕ}
    (S : Finset (Fin ℓ → ℤ)) (hS : ∀ a ∈ S, ∀ j, |a j| ≤ K) :
    Set.InjOn (packVec H) (↑S : Set (Fin ℓ → ℤ)) :=
  fun a ha b hb hab ↦ packVec_inj hH h2K a b (hS a ha) (hS b hb) hab

/-- The packing preserves cardinality on the balanced box. -/
theorem packVec_image_card {H : ℤ} (hH : 0 < H) {K : ℤ} (h2K : 2 * K < H) {ℓ : ℕ}
    (S : Finset (Fin ℓ → ℤ)) (hS : ∀ a ∈ S, ∀ j, |a j| ≤ K) :
    (S.image (packVec H)).card = S.card :=
  Finset.card_image_of_injOn (packVec_injOn hH h2K S hS)

/-- An axis-aligned box in `ℤ^ℓ`: a product of intervals. -/
def Box (ℓ : ℕ) := Fin ℓ → Finset ℤ

namespace Box

def toFinset (B : Box ℓ) : Finset (Fin ℓ → ℤ) :=
  Fintype.piFinset B

def card (B : Box ℓ) : ℕ := ∏ i, (B i).card

theorem card_toFinset (B : Box ℓ) : B.toFinset.card = B.card :=
  Fintype.card_piFinset B

/-- An *interval* box: each side is `Icc lo hi`.  This is the paper's
"axis-aligned box `B ⊆ ℤ^ℓ`" (arXiv:2410.14624v2, §3).  Interval boxes bound
coordinate *magnitudes* by `|B|` (each sidelength `hi − lo + 1 ≤ |B|` and, for
anchored or symmetric sides, the coordinates themselves), which is what the
Appendix-A `packVec` encoding needs; arbitrary finsets (e.g. `{2^i}`) do not
satisfy the structure theorem. -/
def IsInterval (B : Box ℓ) : Prop :=
  ∀ i, ∃ lo hi : ℤ, B i = Finset.Icc lo hi

/-- An *anchored* box: each side is `Icc 0 N` — the `B = [n]^ℓ` normal form
used in the Appendix-A reduction. -/
def Anchored (B : Box ℓ) : Prop :=
  ∀ i, ∃ N : ℕ, B i = Finset.Icc 0 (N : ℤ)

/-- A *symmetric* box: each side is `Icc (−N) N` — the shape of `ϕ_P(P) − x`
for `x ∈ ϕ_P(P)` in Definition 9, and of the ambient box in Lemma 8. -/
def Symmetric (B : Box ℓ) : Prop :=
  ∀ i, ∃ N : ℕ, B i = Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem Anchored.isInterval {B : Box ℓ} (h : B.Anchored) : B.IsInterval := by
  intro i
  obtain ⟨N, hN⟩ := h i
  exact ⟨0, (N : ℤ), hN⟩

theorem Symmetric.isInterval {B : Box ℓ} (h : B.Symmetric) : B.IsInterval := by
  intro i
  obtain ⟨N, hN⟩ := h i
  exact ⟨-(N : ℤ), (N : ℤ), hN⟩

end Box

/-- `A` is an `(ℓ, β)`-set: a subset of `ℤ^ℓ` contained in an interval box of
size `|B| ≤ |A|^β` (arXiv:2410.14624v2, §3). -/
def IsLBSet (A : Finset (Fin ℓ → ℤ)) (β : ℝ) : Prop :=
  ∃ B : Box ℓ, B.IsInterval ∧ A ⊆ B.toFinset ∧ (B.card : ℝ) ≤ (A.card : ℝ) ^ β

/-! ### Coefficient tuples

A tuple `n : Fin d → ℕ` is a coefficient tuple of `P` iff `n i < P.width i`
for every `i`. -/

/-- A tuple is a coefficient tuple iff it is entrywise below `P.width`. -/
theorem mem_coeffs {P : GAP ℓ d} {n : Fin d → ℕ} :
    n ∈ P.coeffs ↔ ∀ i, n i < P.width i := by
  constructor
  · intro hn i
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hn
    exact (m i).isLt
  · intro h
    exact Finset.mem_image.mpr ⟨fun i ↦ ⟨n i, h i⟩, Finset.mem_univ _, rfl⟩

/-- Every coefficient tuple of `P` is entrywise below `P.width`. -/
theorem coeff_mem_width {P : GAP ℓ d} {n : Fin d → ℕ} (hn : n ∈ P.coeffs)
    (i : Fin d) : n i < P.width i :=
  (mem_coeffs.mp hn) i

/-! ### Padding a GAP with an extra step vector

`P.padStep v w₀` appends a `(d+1)`-st step `v` of width `w₀`: its points are
`p + m • v` for `p ∈ P` and `0 ≤ m < w₀`.  This is the padding machinery used
to absorb a translation (`-lo`) into the GAP itself in the Appendix-A
reduction. -/

/-- Append a step `v` of width `w₀` to `P`. -/
def padStep (P : GAP ℓ d) (v : Fin ℓ → ℤ) (w₀ : ℕ) : GAP ℓ (d + 1) where
  base := P.base
  step := Fin.snoc P.step v
  width := Fin.snoc P.width w₀

@[simp] theorem padStep_base (P : GAP ℓ d) (v : Fin ℓ → ℤ) (w₀ : ℕ) :
    (P.padStep v w₀).base = P.base := rfl

@[simp] theorem padStep_step (P : GAP ℓ d) (v : Fin ℓ → ℤ) (w₀ : ℕ) :
    (P.padStep v w₀).step = Fin.snoc P.step v := rfl

@[simp] theorem padStep_width (P : GAP ℓ d) (v : Fin ℓ → ℤ) (w₀ : ℕ) :
    (P.padStep v w₀).width = Fin.snoc P.width w₀ := rfl

/-- Evaluating a padded GAP splits off the last coefficient. -/
theorem padStep_eval (P : GAP ℓ d) (v : Fin ℓ → ℤ) (w₀ : ℕ)
    (n : Fin (d + 1) → ℕ) :
    (P.padStep v w₀).eval n =
      P.eval (fun i ↦ n i.castSucc) + (n (Fin.last d) : ℤ) • v := by
  simp only [eval, padStep_base, padStep_step]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [add_assoc]

/-- Membership in a padded GAP: `p + m • v` with `p ∈ P` and `m < w₀`,
expressed on coefficients. -/
theorem mem_padStep {P : GAP ℓ d} {v : Fin ℓ → ℤ} {w₀ : ℕ} {x : Fin ℓ → ℤ} :
    x ∈ (P.padStep v w₀).toFinset ↔
      ∃ n : Fin d → ℕ, n ∈ P.coeffs ∧ ∃ m : ℕ, m < w₀ ∧
        x = P.eval n + (m : ℤ) • v := by
  constructor
  · intro hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨fun i ↦ c i.castSucc, ?_, c (Fin.last d), ?_, padStep_eval P v w₀ c⟩
    · rw [mem_coeffs]
      intro i
      show c i.castSucc < P.width i
      have h := (mem_coeffs.mp hc) i.castSucc
      have e : (P.padStep v w₀).width i.castSucc = P.width i := by
        simp only [padStep_width, Fin.snoc_castSucc]
      rwa [e] at h
    · have h := (mem_coeffs.mp hc) (Fin.last d)
      have e : (P.padStep v w₀).width (Fin.last d) = w₀ := by
        simp only [padStep_width, Fin.snoc_last]
      rwa [e] at h
  · rintro ⟨n, hn, m, hm, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(Fin.snoc n m : Fin (d + 1) → ℕ), ?_, ?_⟩
    · rw [mem_coeffs]
      intro i
      rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
      · simp only [padStep_width, Fin.snoc_castSucc]
        exact coeff_mem_width hn j
      · simp only [padStep_width, Fin.snoc_last]
        exact hm
    · have h1 : (fun i : Fin d ↦ (Fin.snoc n m : Fin (d + 1) → ℕ) i.castSucc) = n := by
        funext i
        simp only [Fin.snoc_castSucc]
      have h2 : (Fin.snoc n m : Fin (d + 1) → ℕ) (Fin.last d) = m := by
        simp only [Fin.snoc_last]
      rw [padStep_eval, h1, h2]

/-- The point set of a padded GAP, as an image of `coeffs × [0, w₀)`. -/
theorem padStep_toFinset (P : GAP ℓ d) (v : Fin ℓ → ℤ) (w₀ : ℕ) :
    (P.padStep v w₀).toFinset =
      (P.coeffs ×ˢ Finset.range w₀).image
        fun nm : (Fin d → ℕ) × ℕ ↦ P.eval nm.1 + (nm.2 : ℤ) • v := by
  ext x
  rw [mem_padStep]
  constructor
  · rintro ⟨n, hn, m, hm, rfl⟩
    exact Finset.mem_image.mpr ⟨(n, m),
      Finset.mem_product.mpr ⟨hn, Finset.mem_range.mpr hm⟩, rfl⟩
  · intro hx
    obtain ⟨⟨n, m⟩, hnm, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_product] at hnm
    exact ⟨n, hnm.1, m, Finset.mem_range.mp hnm.2, rfl⟩

/-- The point set of a padded GAP: `{p + m • v : p ∈ P, m < w₀}`. -/
theorem padStep_toFinset_biUnion (P : GAP ℓ d) (v : Fin ℓ → ℤ) (w₀ : ℕ) :
    (P.padStep v w₀).toFinset =
      P.toFinset.biUnion
        fun p ↦ (Finset.range w₀).image fun m : ℕ ↦ p + (m : ℤ) • v := by
  ext x
  rw [mem_padStep, Finset.mem_biUnion]
  constructor
  · rintro ⟨n, hn, m, hm, rfl⟩
    exact ⟨P.eval n, Finset.mem_image.mpr ⟨n, hn, rfl⟩,
      Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩⟩
  · rintro ⟨p, hp, hx⟩
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨n, hn, m, Finset.mem_range.mp hm, rfl⟩

/-- The first `d` coefficients of a padded-GAP coefficient tuple form a
coefficient tuple of `P`. -/
theorem padStep_coeff_init {P : GAP ℓ d} {v : Fin ℓ → ℤ} {w₀ : ℕ}
    {c : Fin (d + 1) → ℕ} (hc : c ∈ (P.padStep v w₀).coeffs) :
    (fun i ↦ c i.castSucc) ∈ P.coeffs := by
  rw [mem_coeffs] at hc ⊢
  intro i
  show c i.castSucc < P.width i
  have h := hc i.castSucc
  rw [padStep_width, Fin.snoc_castSucc] at h
  exact h

/-- The last coefficient of a padded-GAP coefficient tuple is below `w₀`. -/
theorem padStep_coeff_last {P : GAP ℓ d} {v : Fin ℓ → ℤ} {w₀ : ℕ}
    {c : Fin (d + 1) → ℕ} (hc : c ∈ (P.padStep v w₀).coeffs) :
    c (Fin.last d) < w₀ := by
  rw [mem_coeffs] at hc
  have h := hc (Fin.last d)
  rw [padStep_width, Fin.snoc_last] at h
  exact h

/-- A padded GAP is proper if `P` is proper and the extra scalar `m` is
recoverable from `p + m • v` (the "absorbed shift" separation hypothesis). -/
theorem padStep_proper {P : GAP ℓ d} (hP : P.Proper) {v : Fin ℓ → ℤ} {w₀ : ℕ}
    (hsep : ∀ n ∈ P.coeffs, ∀ m < w₀, ∀ n' ∈ P.coeffs, ∀ m' < w₀,
      P.eval n + (m : ℤ) • v = P.eval n' + (m' : ℤ) • v → m = m') :
    (P.padStep v w₀).Proper := by
  intro c hc c' hc' h
  rw [padStep_eval, padStep_eval] at h
  have hm : c (Fin.last d) = c' (Fin.last d) :=
    hsep _ (padStep_coeff_init hc) _ (padStep_coeff_last hc)
      _ (padStep_coeff_init hc') _ (padStep_coeff_last hc') h
  have heval : P.eval (fun i ↦ c i.castSucc) = P.eval (fun i ↦ c' i.castSucc) := by
    rw [hm] at h
    simpa using h
  have hinit := hP (padStep_coeff_init hc) (padStep_coeff_init hc') heval
  funext i
  rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
  · exact congrFun hinit j
  · exact hm

/-- A padded GAP stays homogeneous (extend the base coefficients by `0`). -/
theorem padStep_homogeneous {P : GAP ℓ d} (hP : P.Homogeneous) (v : Fin ℓ → ℤ)
    (w₀ : ℕ) : (P.padStep v w₀).Homogeneous := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨(Fin.snoc c (0 : ℤ) : Fin (d + 1) → ℤ), ?_⟩
  rw [padStep_base, Fin.sum_univ_castSucc]
  simp only [padStep_step, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
  exact hc

/-- Padding with an odd width `2N + 1` preserves symmetry: the new center is
`c + N • v`. -/
theorem padStep_symmetric {P : GAP ℓ d} (hP : P.Symmetric) (v : Fin ℓ → ℤ)
    (N : ℕ) : (P.padStep v (2 * N + 1)).Symmetric := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨c + (N : ℤ) • v, fun x hx ↦ ?_⟩
  obtain ⟨n, hn, m, hm, rfl⟩ := mem_padStep.mp hx
  have hmem : P.eval n ∈ P.toFinset := Finset.mem_image.mpr ⟨n, hn, rfl⟩
  obtain ⟨n', hn', hnn'⟩ := Finset.mem_image.mp (hc _ hmem)
  refine mem_padStep.mpr ⟨n', hn', 2 * N - m, by omega, ?_⟩
  rw [hnn', Nat.cast_sub (by omega : m ≤ 2 * N)]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Int.nsmul_eq_mul]
  push_cast
  ring

/-! ### Subset sums of translated finsets

Subset sums are not translation-invariant, but a `j`-element subset `S ⊆ A₀`
maps to a `j`-element subset `S + lo ⊆ A₀ + lo`, shifting its sum by `j • lo`.
`subsetSumsLCard` packages the fixed-cardinality hypothesis needed for the
Appendix-A anchoring step. -/

/-- Membership in the subset sums of a finset in `ℤ^ℓ`. -/
theorem mem_subsetSumsL {x : Fin ℓ → ℤ} {A : Finset (Fin ℓ → ℤ)} :
    x ∈ subsetSumsL A ↔ ∃ S ⊆ A, S.sum id = x := by
  simp [subsetSumsL]

/-- The `j`-element subset sums of `A`. -/
def subsetSumsLCard (A : Finset (Fin ℓ → ℤ)) (j : ℕ) : Finset (Fin ℓ → ℤ) :=
  (A.powerset.filter fun S ↦ S.card = j).image fun S ↦ ∑ x ∈ S, x

theorem mem_subsetSumsLCard {x : Fin ℓ → ℤ} {A : Finset (Fin ℓ → ℤ)} {j : ℕ} :
    x ∈ subsetSumsLCard A j ↔
      ∃ S : Finset (Fin ℓ → ℤ), S ⊆ A ∧ S.card = j ∧ (∑ i ∈ S, i) = x := by
  simp only [subsetSumsLCard, Finset.mem_image, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨S, ⟨hS, hj⟩, rfl⟩
    exact ⟨S, hS, hj, rfl⟩
  · rintro ⟨S, hS, hj, rfl⟩
    exact ⟨S, ⟨hS, hj⟩, rfl⟩

theorem subsetSumsLCard_subset (A : Finset (Fin ℓ → ℤ)) (j : ℕ) :
    subsetSumsLCard A j ⊆ subsetSumsL A := by
  intro x hx
  obtain ⟨S, hS, -, hsum⟩ := mem_subsetSumsLCard.mp hx
  exact mem_subsetSumsL.mpr ⟨S, hS, hsum⟩

/-- Translating a finset shifts its `j`-element subset sums by `j • lo`. -/
theorem subsetSumsLCard_image_add {A₀ : Finset (Fin ℓ → ℤ)} (lo : Fin ℓ → ℤ)
    (j : ℕ) :
    (subsetSumsLCard A₀ j).image (· + j • lo) ⊆
      subsetSumsLCard (A₀.image (· + lo)) j := by
  intro y hy
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨S, hS, hScard, hsum⟩ := mem_subsetSumsLCard.mp hσ
  apply mem_subsetSumsLCard.mpr
  refine ⟨S.image (· + lo), ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨w, hS hw, rfl⟩
  · calc (S.image (· + lo)).card = S.card :=
        Finset.card_image_of_injective _ fun a b h ↦ by simpa using h
      _ = j := hScard
  · have hinj : Set.InjOn (· + lo) ↑S := fun a _ b _ h ↦ by simpa using h
    calc (∑ i ∈ S.image (· + lo), i) = ∑ x ∈ S, (x + lo) := Finset.sum_image hinj
        _ = (∑ x ∈ S, x) + ∑ _x ∈ S, lo := Finset.sum_add_distrib
        _ = (∑ x ∈ S, x) + j • lo := by rw [Finset.sum_const, hScard]
        _ = σ + j • lo := by rw [hsum]

/-- If every element of `T` is a sum of exactly `j` elements of `A₀`, then
`T + j • lo` consists of subset sums of the translate `A₀ + lo`.  This is the
explicit fixed-cardinality form of the translation non-invariance of `Σ`. -/
theorem subsetSumsL_translate_of_card {A₀ : Finset (Fin ℓ → ℤ)} (lo : Fin ℓ → ℤ)
    {j : ℕ} {T : Finset (Fin ℓ → ℤ)}
    (hcard : ∀ σ ∈ T, ∃ S : Finset (Fin ℓ → ℤ),
      S ⊆ A₀ ∧ S.card = j ∧ (∑ x ∈ S, x) = σ) :
    T.image (· + j • lo) ⊆ subsetSumsL (A₀.image (· + lo)) := by
  intro y hy
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨S, hS, hScard, hsum⟩ := hcard σ hσ
  apply mem_subsetSumsL.mpr
  refine ⟨S.image (· + lo), ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨w, hS hw, rfl⟩
  · have hinj : Set.InjOn (· + lo) ↑S := fun a _ b _ h ↦ by simpa using h
    calc (S.image (· + lo)).sum id = ∑ x ∈ S, (x + lo) := Finset.sum_image hinj
        _ = (∑ x ∈ S, x) + ∑ _x ∈ S, lo := Finset.sum_add_distrib
        _ = (∑ x ∈ S, x) + j • lo := by rw [Finset.sum_const, hScard]
        _ = σ + j • lo := by rw [hsum]

namespace Box

/-- The coordinatewise shift of a box by `−t`. -/
def shift (B : Box ℓ) (t : Fin ℓ → ℤ) : Box ℓ :=
  fun i ↦ (B i).image (· - t i)

/-- Shifting a box preserves its cardinality. -/
theorem shift_card (B : Box ℓ) (t : Fin ℓ → ℤ) : (B.shift t).card = B.card := by
  show (∏ i, ((B i).image (· - t i)).card) = ∏ i, (B i).card
  exact Finset.prod_congr rfl fun i _ ↦
    Finset.card_image_of_injective _ fun _ _ h ↦ by simpa using h

/-- `x ∈ B.shift t` iff `x + t ∈ B`. -/
theorem mem_shift {B : Box ℓ} {t x : Fin ℓ → ℤ} :
    x ∈ (B.shift t).toFinset ↔ x + t ∈ B.toFinset := by
  constructor
  · intro h
    apply Fintype.mem_piFinset.mpr
    intro i
    have hi := Fintype.mem_piFinset.mp h i
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hi
    rw [Pi.add_apply, ← hbx, sub_add_cancel]
    exact hb
  · intro h
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_image.mpr
    refine ⟨x i + t i, ?_, by simp⟩
    have hi := Fintype.mem_piFinset.mp h i
    rwa [Pi.add_apply] at hi

/-- The point set of a shifted box is the translate of the point set. -/
theorem toFinset_shift (B : Box ℓ) (t : Fin ℓ → ℤ) :
    (B.shift t).toFinset = B.toFinset.image (· - t) := by
  ext x
  rw [mem_shift, Finset.mem_image]
  constructor
  · intro h
    exact ⟨x + t, h, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [sub_add_cancel]

/-- Shifting an interval side `[lo, hi]` by `−lo` anchors it at `0`. -/
theorem image_sub_Icc (lo hi : ℤ) :
    (Finset.Icc lo hi).image (· - lo) = Finset.Icc 0 (hi - lo) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨by omega, by omega⟩
  · intro h
    exact ⟨x + lo, ⟨by omega, by omega⟩, by simp⟩

/-- An interval box with lower corner `lo` shifts to an anchored box. -/
theorem shift_anchored_of_interval {B : Box ℓ} {lo : Fin ℓ → ℤ}
    (hB : ∀ i, ∃ hi : ℤ, lo i ≤ hi ∧ B i = Finset.Icc (lo i) hi) :
    (B.shift lo).Anchored := by
  intro i
  obtain ⟨hi, hle, hBi⟩ := hB i
  refine ⟨(hi - lo i).toNat, ?_⟩
  show (B i).image (· - lo i) = Finset.Icc 0 ((hi - lo i).toNat : ℤ)
  rw [hBi, image_sub_Icc]
  congr 1
  exact (Int.toNat_of_nonneg (by omega)).symm

/-- Anchoring an interval box at its lower corner: `B − lo` is an anchored box
of the same cardinality whose point set is the `-lo` translate of `B`'s. -/
theorem exists_anchored_shift {B : Box ℓ} {lo : Fin ℓ → ℤ}
    (hB : ∀ i, ∃ hi : ℤ, lo i ≤ hi ∧ B i = Finset.Icc (lo i) hi) :
    ∃ B' : Box ℓ, B'.Anchored ∧ B'.card = B.card ∧
      B'.toFinset = B.toFinset.image (· - lo) :=
  ⟨B.shift lo, shift_anchored_of_interval hB, shift_card B lo,
    toFinset_shift B lo⟩

/-- For `A` inside an interval box `B` with lower corner `lo`, the translate
`A - lo` lands in an anchored box of cardinality `|B|`. -/
theorem exists_anchored_image_sub {A : Finset (Fin ℓ → ℤ)} {B : Box ℓ}
    {lo : Fin ℓ → ℤ} (hAB : A ⊆ B.toFinset)
    (hB : ∀ i, ∃ hi : ℤ, lo i ≤ hi ∧ B i = Finset.Icc (lo i) hi) :
    ∃ B' : Box ℓ, B'.Anchored ∧ B'.card = B.card ∧
      A.image (· - lo) ⊆ B'.toFinset := by
  obtain ⟨B', hB', hcard, hpts⟩ := exists_anchored_shift hB
  refine ⟨B', hB', hcard, ?_⟩
  rw [hpts]
  exact Finset.image_subset_image hAB

end Box

/-! ### Decoding a `GAP 1` into `ℤ^ℓ` via base-`H` digits

The Appendix-A encoding `φ` is `packVec H`; its inverse on the balanced box
sends a `GAP 1 d` to a `GAP ℓ d` whose steps are the digit vectors `dig i`
with `packVec H (dig i) = P₀.step i 0`. -/

/-- The `ℤ^ℓ` GAP with prescribed base-`H` digit vectors. -/
def unpack (dig : Fin d → Fin ℓ → ℤ) (bdig : Fin ℓ → ℤ) (w : Fin d → ℕ) :
    GAP ℓ d where
  base := bdig
  step := dig
  width := w

@[simp] theorem unpack_base (dig : Fin d → Fin ℓ → ℤ) (bdig : Fin ℓ → ℤ)
    (w : Fin d → ℕ) : (unpack dig bdig w).base = bdig := rfl

@[simp] theorem unpack_step (dig : Fin d → Fin ℓ → ℤ) (bdig : Fin ℓ → ℤ)
    (w : Fin d → ℕ) : (unpack dig bdig w).step = dig := rfl

@[simp] theorem unpack_width (dig : Fin d → Fin ℓ → ℤ) (bdig : Fin ℓ → ℤ)
    (w : Fin d → ℕ) : (unpack dig bdig w).width = w := rfl

/-- The coefficient tuples of the decoded GAP are those of `P₀`. -/
theorem unpack_coeffs {P₀ : GAP 1 d} (dig : Fin d → Fin ℓ → ℤ)
    (bdig : Fin ℓ → ℤ) :
    (unpack dig bdig P₀.width).coeffs = P₀.coeffs := rfl

/-- `packVec` of a sum. -/
theorem packVec_sum' {H : ℤ} {ι : Type*} (s : Finset ι) (f : ι → Fin ℓ → ℤ) :
    packVec H (∑ i ∈ s, f i) = ∑ i ∈ s, packVec H (f i) :=
  map_sum (packVecHom H) f s

/-- **Decoding commutes with evaluation**: `packVec` of a point of the decoded
GAP is the corresponding point of `P₀`, read at coordinate `0`. -/
theorem packVec_unpack_eval {P₀ : GAP 1 d} {H : ℤ} {dig : Fin d → Fin ℓ → ℤ}
    {bdig : Fin ℓ → ℤ} (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0) (n : Fin d → ℕ) :
    packVec H ((unpack dig bdig P₀.width).eval n) = (P₀.eval n) 0 := by
  have hP : (unpack dig bdig P₀.width).eval n =
      bdig + ∑ i, (n i : ℤ) • dig i := rfl
  have hRHS : (P₀.eval n) 0 = P₀.base 0 + ∑ i, (n i : ℤ) * P₀.step i 0 := by
    show (P₀.base + ∑ i, (n i : ℤ) • P₀.step i) 0 = _
    rw [Pi.add_apply, Finset.sum_apply]
    exact congrArg (P₀.base 0 + ·) <|
      Finset.sum_congr rfl fun i _ ↦ by rw [Pi.smul_apply, smul_eq_mul]
  rw [hP, packVec_add, packVec_sum' Finset.univ, hbdig, hRHS]
  exact congrArg (P₀.base 0 + ·) <|
    Finset.sum_congr rfl fun i _ ↦ by rw [packVec_smul, hdig i]

/-- The `packVec` image of the decoded GAP is the `0`-coordinate image of
`P₀`: `packVec` maps `P.toFinset` onto `P₀.toFinset` (read at `0`). -/
theorem unpack_toFinset_image {P₀ : GAP 1 d} {H : ℤ} {dig : Fin d → Fin ℓ → ℤ}
    {bdig : Fin ℓ → ℤ} (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0) :
    (unpack dig bdig P₀.width).toFinset.image (packVec H) =
      P₀.toFinset.image fun x ↦ x 0 := by
  unfold toFinset
  rw [unpack_coeffs, Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun n _ ↦ ?_
  exact packVec_unpack_eval hdig hbdig n

/-- Equality of `Fin 1 → ℤ` functions detected at coordinate `0`. -/
theorem eval_one_eq {P₀ : GAP 1 d} {n m : Fin d → ℕ} :
    P₀.eval n = P₀.eval m ↔ (P₀.eval n) 0 = (P₀.eval m) 0 :=
  ⟨fun h ↦ congrFun h 0,
    fun h ↦ funext fun i ↦ (Fin.eq_zero i).symm ▸ h⟩

/-- **Decoding preserves properness**: provided the points of the decoded GAP
stay in the balanced box `|·| ≤ K` with `2K < H`, the decoded GAP is proper
iff `P₀` is. -/
theorem unpack_proper {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    {K : ℤ} (h2K : 2 * K < H)
    (hbound : ∀ n ∈ P₀.coeffs, ∀ j,
      |(unpack dig bdig P₀.width).eval n j| ≤ K) :
    (unpack dig bdig P₀.width).Proper ↔ P₀.Proper := by
  have hcoe : ∀ {x : Fin d → ℕ}, x ∈ P₀.coeffs →
      x ∈ (unpack dig bdig P₀.width).coeffs := fun h ↦ by
    rw [unpack_coeffs]; exact h
  constructor
  · intro hU n hn m hm h
    have hpack : packVec H ((unpack dig bdig P₀.width).eval n) =
        packVec H ((unpack dig bdig P₀.width).eval m) := by
      rw [packVec_unpack_eval hdig hbdig n,
        packVec_unpack_eval hdig hbdig m, h]
    exact hU (hcoe hn) (hcoe hm)
      (packVec_inj hH h2K _ _ (hbound n hn) (hbound m hm) hpack)
  · intro hP n hn m hm h
    rw [unpack_coeffs] at hn hm
    apply hP hn hm
    apply eval_one_eq.mpr
    rw [← packVec_unpack_eval hdig hbdig n,
      ← packVec_unpack_eval hdig hbdig m, h]

/-- Decoding preserves cardinality on the balanced box. -/
theorem card_unpack_toFinset {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    {K : ℤ} (h2K : 2 * K < H)
    (hbound : ∀ a ∈ (unpack dig bdig P₀.width).toFinset, ∀ j, |a j| ≤ K) :
    (unpack dig bdig P₀.width).toFinset.card = P₀.toFinset.card := by
  have h1 := packVec_image_card hH h2K _ hbound
  rw [unpack_toFinset_image hdig hbdig] at h1
  rw [← h1]
  exact Finset.card_image_of_injective _
    fun a b h ↦ funext fun i ↦ (Fin.eq_zero i).symm ▸ h

/-- Decoding preserves homogeneity: if `P₀.base = ∑ cᵢ • stepᵢ` and the
coefficient combination stays in the balanced box, the decoded base satisfies
`bdig = ∑ cᵢ • dig i`. -/
theorem unpack_homogeneous {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ} {c : Fin d → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    (hc : P₀.base = ∑ i, c i • P₀.step i)
    {K : ℤ} (h2K : 2 * K < H)
    (hb : ∀ j, |bdig j| ≤ K) (hd : ∀ j, |(∑ i, c i • dig i) j| ≤ K) :
    (unpack dig bdig P₀.width).Homogeneous := by
  refine ⟨c, ?_⟩
  apply packVec_inj hH h2K _ _ hb hd
  rw [hbdig, hc, packVec_sum' Finset.univ, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Pi.smul_apply, smul_eq_mul, packVec_smul, hdig i]

end GAP

/-- **CFP23 main theorem** (Conlon–Fox–Pham, Theorem 1.5), quoted as
**Theorem 5** in Pham–Zakharov (arXiv:2410.14624v2).  This is the deep
external input to `cfp_structure`: it is stated here as a black box and is
*not* proved in this file (the placeholder is the quoted theorem itself).

For `A ⊆ [n] ⊆ ℤ` with `|A| = m`, `n ≤ m^β` and
`s ∈ [m^η, c·m / log m]`, it gives `Â ⊆ A` with
`|Â| ≥ m − c⁻¹·s·log m`, a proper `d'`-dimensional (`d' ≤ d`) GAP `P` with
`Â ∪ {0} ⊆ P`, and `A' ⊆ Â` with `|A'| ≤ s` such that `Σ(A')` contains a
homogeneous translate of a `≤ c·s` dilation of `P`, which remains proper.

We phrase it for `ℓ = 1` in the ambient `Fin 1 → ℤ` model used by `GAP`, so
that `cfp_structure` is literally its `ℓ`-dimensional extension obtained by
the Appendix-A base-`H` packing (`GAP.packVec`, `GAP.packVec_inj`). -/
theorem cfp_main {β η : ℝ} (hβ : 1 < β) (hη : 0 < η) (hη1 : η < 1) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
      ∀ (A : Finset (Fin 1 → ℤ)) (n s : ℕ),
        A.Nonempty →
        (∀ a ∈ A, 0 ≤ a 0 ∧ a 0 ≤ (n : ℤ)) →
        (n : ℝ) ≤ (A.card : ℝ) ^ β →
        (A.card : ℝ) ^ η ≤ s →
        (s : ℝ) ≤ c * A.card / Real.log A.card →
        ∃ (Â : Finset (Fin 1 → ℤ)) (d' : ℕ) (P : GAP 1 d'),
          Â ⊆ A ∧
          (A.card : ℝ) - c⁻¹ * s * Real.log A.card ≤ (Â.card : ℝ) ∧
          (d' : ℝ) ≤ d ∧
          P.Symmetric ∧ P.Homogeneous ∧ P.Proper ∧
          (Â ∪ {0}) ⊆ P.toFinset ∧
          ∃ A' ⊆ Â, A'.card ≤ s ∧
            ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ c * s ∧
              ∃ t : Fin 1 → ℤ,
                ((k • P).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
                (k • P).Proper := by
  sorry

/-- **Theorem 3 (CFP structure theorem)**.  For `ℓ, β > 1` and `0 < η < 1`
there are `c, d > 0` such that for any `A ⊆ B ⊆ ℤ^ℓ`, `|A| = m`, `|B| ≤ m^β`
and `s ∈ [m^η, c·m/log m]` there exist `Â ⊆ A` with
`|Â| ≥ m − c⁻¹·s·log m`, an integer `d' ≤ d`, a `d'`-dimensional GAP `P`
containing `Â ∪ {0}`, and `A' ⊆ Â` of size `≤ s` such that `Σ(A')` contains a
homogeneous translate of `csP`, and `csP` is proper.

This is the `ℓ`-dimensional consequence of `cfp_main` via the Appendix-A
base-`H` encoding of Pham–Zakharov.

**Formalization note.**  The quantified `B` is restricted to *interval*
boxes (`GAP.Box.IsInterval`), matching the paper's "axis-aligned box":
with arbitrary finsets the statement is false (e.g. `A = {2^i}` inside a
one-element-per-coordinate box forces `s ≥ m − O(d log m)`, contradicting
`s ≈ m^η`), and `A` is required nonempty (`A = ∅`, `s = 0` would force
`0 < k ≤ c·s = 0`).  See
`discovery/JSP-000179/scratch/cfp_derivation_report.md` for the full
analysis, including the Appendix-A `H`-sizing (`κ = 10ℓ³`, `H = n^κ`,
`cH > n s² (sn)^ℓ`) and the translation subtlety for non-anchored boxes
(`Σ` is not translation-invariant; the paper's `WLOG B = [n]^ℓ` is only
directly justified for anchored boxes, while Lemma-8-style applications
use symmetric boxes — a faithful derivation must resolve this, e.g. by
padding the decoded GAP to absorb the shift). -/
theorem cfp_structure (ℓ : ℕ) {β η : ℝ} (hβ : 1 < β) (hη : 0 < η) (hη1 : η < 1) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ (A : Finset (Fin ℓ → ℤ)) (B : GAP.Box ℓ) (s : ℕ),
      A.Nonempty → B.IsInterval →
      A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      (A.card : ℝ) ^ η ≤ s → (s : ℝ) ≤ c * A.card / Real.log A.card →
      ∃ (Â : Finset (Fin ℓ → ℤ)) (d' : ℕ) (P : GAP ℓ d'),
        Â ⊆ A ∧ (A.card : ℝ) - c⁻¹ * s * Real.log A.card ≤ Â.card ∧
        (d' : ℝ) ≤ d ∧ P.Symmetric ∧
        (Â ∪ {0}) ⊆ P.toFinset ∧
        ∃ A' ⊆ Â, A'.card ≤ s ∧
          ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ c * s ∧
            ∃ t : Fin ℓ → ℤ,
              ((k • P).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
              (k • P).Proper := by
  sorry

/-- **Corollary 5**: Theorem 3 at `s = ⌊m / log² m⌋`; `P` may be taken
symmetric and `kP` proper.  Requires `m ≥ C` so that `s` lies in the
admissible range `[m^{1/2}, c·m/log m]` of Theorem 3. -/
theorem cfp_structure_cor (ℓ : ℕ) {β : ℝ} (hβ : 1 < β) :
    ∃ c d C : ℝ, 0 < c ∧ 0 < d ∧ 0 < C ∧ ∀ (A : Finset (Fin ℓ → ℤ))
      (B : GAP.Box ℓ),
      B.IsInterval →
      A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      C ≤ (A.card : ℝ) →
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
  obtain ⟨c, d, hc, hd, hcfp⟩ :=
    cfp_structure ℓ hβ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)
  -- Eventually `(log m)² ≤ 64·m^{1/8}` (hence `≤ m^{1/4}`), `64 ≤ m^{1/8}`,
  -- `1/c ≤ log m`, `16 ≤ m`.
  have evLog : ∀ᶠ m : ℝ in atTop,
      (Real.log m) ^ 2 ≤ 64 * m ^ ((1 : ℝ) / 8) := by
    have hLo : (fun x : ℝ ↦ (Real.log (x ^ ((1 : ℝ) / 8))) ^ 2) =o[atTop]
        (fun x ↦ x ^ ((1 : ℝ) / 8)) :=
      (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [hLo.bound zero_lt_one, eventually_gt_atTop 0]
      with m hm hm0
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hm
    have hm' : |(Real.log (m ^ ((1 : ℝ) / 8))) ^ 2| ≤ 1 * |m ^ ((1 : ℝ) / 8)| := hm
    rw [one_mul, abs_of_nonneg (Real.rpow_nonneg hm0.le _), Real.log_rpow hm0,
      abs_of_nonneg (sq_nonneg _)] at hm'
    nlinarith [hm']
  have ev64 : ∀ᶠ m : ℝ in atTop, (64 : ℝ) ≤ m ^ ((1 : ℝ) / 8) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually_ge_atTop 64
  have evlog : ∀ᶠ m : ℝ in atTop, (1 : ℝ) / c ≤ Real.log m :=
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / c)
  obtain ⟨C₁, hC₁⟩ := eventually_atTop.mp
    (evLog.and (ev64.and (evlog.and (eventually_ge_atTop (16 : ℝ)))))
  refine ⟨c, d, max C₁ 1, hc, hd,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun A B hBint hsub hB hCm ↦ ?_⟩
  obtain ⟨hlog2, h64, h1c, hm16⟩ :=
    hC₁ (A.card : ℝ) (le_trans (le_max_left _ _) hCm)
  have hmpos : (0 : ℝ) < (A.card : ℝ) := lt_of_lt_of_le (by norm_num) hm16
  have hlpos : (0 : ℝ) < Real.log (A.card : ℝ) := lt_of_lt_of_le (by positivity) h1c
  have hl2pos : (0 : ℝ) < (Real.log (A.card : ℝ)) ^ 2 := sq_pos_of_pos hlpos
  have hq14 : (Real.log (A.card : ℝ)) ^ 2 ≤ (A.card : ℝ) ^ ((1 : ℝ) / 4) := by
    have h18 : (0 : ℝ) ≤ (A.card : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_nonneg hmpos.le _
    have hmul : (64 : ℝ) * (A.card : ℝ) ^ ((1 : ℝ) / 8)
        ≤ (A.card : ℝ) ^ ((1 : ℝ) / 8) * (A.card : ℝ) ^ ((1 : ℝ) / 8) :=
      mul_le_mul_of_nonneg_right h64 h18
    rw [← Real.rpow_add hmpos, show (1 : ℝ) / 8 + 1 / 8 = 1 / 4 by norm_num]
      at hmul
    linarith
  set s := ⌊(A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2⌋₊ with hs_def
  have hs_le : (s : ℝ) ≤ (A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2 :=
    Nat.floor_le (by positivity)
  -- `m^{1/2} + 1 ≤ m / log²m`, so `m^{1/2} ≤ s`.
  have hbig : (A.card : ℝ) ^ ((1 : ℝ) / 2) + 1
      ≤ (A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2 := by
    rw [le_div_iff₀ hl2pos]
    have h1 : ((A.card : ℝ) ^ ((1 : ℝ) / 2) + 1) * (Real.log (A.card : ℝ)) ^ 2
        ≤ ((A.card : ℝ) ^ ((1 : ℝ) / 2) + 1) * (A.card : ℝ) ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left hq14 (by positivity)
    refine h1.trans ?_
    have h2 : ((A.card : ℝ) ^ ((1 : ℝ) / 2) + 1) * (A.card : ℝ) ^ ((1 : ℝ) / 4)
        = (A.card : ℝ) ^ ((3 : ℝ) / 4) + (A.card : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [add_mul, one_mul, ← Real.rpow_add hmpos]
      norm_num
    rw [h2]
    have h3 : (A.card : ℝ) ^ ((1 : ℝ) / 4) ≤ (A.card : ℝ) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le
        (le_trans (by norm_num : (1 : ℝ) ≤ 16) hm16) (by norm_num)
    have h4 : 2 * (A.card : ℝ) ^ ((3 : ℝ) / 4) ≤ (A.card : ℝ) := by
      have h5 : (2 : ℝ) ≤ (A.card : ℝ) ^ ((1 : ℝ) / 4) := by
        have h16 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num,
            show (1 : ℝ) / 4 = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
        calc (2 : ℝ) = (16 : ℝ) ^ ((1 : ℝ) / 4) := h16.symm
          _ ≤ (A.card : ℝ) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hm16) (by norm_num)
      calc 2 * (A.card : ℝ) ^ ((3 : ℝ) / 4)
          ≤ (A.card : ℝ) ^ ((1 : ℝ) / 4) * (A.card : ℝ) ^ ((3 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hmpos.le _)
        _ = (A.card : ℝ) := by
            rw [← Real.rpow_add hmpos]
            norm_num
    linarith
  have hs_ge : (A.card : ℝ) ^ ((1 : ℝ) / 2) ≤ (s : ℝ) := by
    have := Nat.lt_floor_add_one ((A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2)
    linarith [hbig]
  have hs_le2 : (s : ℝ) ≤ c * (A.card : ℝ) / Real.log (A.card : ℝ) := by
    refine hs_le.trans ?_
    rw [div_le_div_iff₀ hl2pos hlpos]
    have hcm : (1 : ℝ) ≤ c * Real.log (A.card : ℝ) := by
      have := (div_le_iff₀ hc).mp h1c
      nlinarith
    calc (A.card : ℝ) * Real.log (A.card : ℝ)
        = 1 * ((A.card : ℝ) * Real.log (A.card : ℝ)) := by ring
      _ ≤ (c * Real.log (A.card : ℝ)) * ((A.card : ℝ) * Real.log (A.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hcm (by positivity)
      _ = c * (A.card : ℝ) * Real.log (A.card : ℝ) ^ 2 := by ring
  have hAne : A.Nonempty :=
    Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_lt_of_le (by norm_num) hm16))
  obtain ⟨Â, d', P, hÂsub, hÂcard, hd'le, hSym, hsub0,
    A', hA'sub, hA'card, k, hkpos, hkle, t, htrans, hprop⟩ :=
    hcfp A B s hAne hBint hsub hB hs_ge hs_le2
  have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
  have hst : (s : ℝ) * Real.log (A.card : ℝ)
      ≤ (A.card : ℝ) / Real.log (A.card : ℝ) := by
    rw [le_div_iff₀ hlpos, mul_assoc, ← sq]
    calc (s : ℝ) * (Real.log (A.card : ℝ)) ^ 2
        ≤ ((A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2)
            * (Real.log (A.card : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hs_le (sq_nonneg _)
      _ = (A.card : ℝ) := by field_simp
  refine ⟨Â, d', P, hÂsub, ?_, hd'le, hSym, hsub0, A', hA'sub, ?_, k, hkpos, ?_,
    t, htrans, hprop⟩
  · refine le_trans ?_ hÂcard
    apply sub_le_sub_left
    have hle : c⁻¹ * (s : ℝ) * Real.log (A.card : ℝ)
        ≤ c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ) := by
      rw [mul_div_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left hst hcinv.le
    exact hle
  · have : (A'.card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hA'card
    exact this.trans hs_le
  · exact hkle.trans (mul_le_mul_of_nonneg_left hs_le hc.le)

end Nonaveraging
