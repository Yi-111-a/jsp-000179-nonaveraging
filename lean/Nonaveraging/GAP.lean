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

@[simp] theorem smul_base (k : ℤ) (P : GAP ℓ d) : (k • P).base = k • P.base := rfl

@[simp] theorem smul_step (k : ℤ) (P : GAP ℓ d) :
    (k • P).step = fun i ↦ k • P.step i := rfl

@[simp] theorem smul_width (k : ℤ) (P : GAP ℓ d) : (k • P).width = P.width := rfl

theorem smul_coeffs (k : ℤ) (P : GAP ℓ d) : (k • P).coeffs = P.coeffs := rfl

theorem nsmul_eq_zsmul (k : ℕ) (P : GAP ℓ d) : (k • P) = ((k : ℤ) • P) := rfl

@[simp] theorem translate_base (P : GAP ℓ d) (t : Fin ℓ → ℤ) :
    (P.translate t).base = t + P.base := rfl

@[simp] theorem translate_step (P : GAP ℓ d) (t : Fin ℓ → ℤ) :
    (P.translate t).step = P.step := rfl

@[simp] theorem translate_width (P : GAP ℓ d) (t : Fin ℓ → ℤ) :
    (P.translate t).width = P.width := rfl

theorem translate_coeffs (P : GAP ℓ d) (t : Fin ℓ → ℤ) :
    (P.translate t).coeffs = P.coeffs := rfl

/-- Evaluating a translate splits off the shift. -/
theorem translate_eval (P : GAP ℓ d) (t : Fin ℓ → ℤ) (n : Fin d → ℕ) :
    (P.translate t).eval n = t + P.eval n := add_assoc _ _ _

/-- Evaluating a dilation distributes over the coefficients. -/
theorem smul_eval (k : ℤ) (P : GAP ℓ d) (n : Fin d → ℕ) :
    (k • P).eval n = k • P.eval n := by
  show (k • P.base) + ∑ i, (n i : ℤ) • (k • P.step i) =
    k • (P.base + ∑ i, (n i : ℤ) • P.step i)
  rw [smul_add, Finset.smul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact (smul_comm k _ _).symm

/-- Width-scaling `cs·P` (the `csP`/`cQ` of Conlon–Fox–Pham, CFP23): same
base and steps, each width multiplied by `k`.  This is the
coefficient-interval scaling — *not* the pointwise dilation `k • P`
(`GAP.smul`), which scales the base and steps instead.  For `k ≥ 1` the
widened progression contains `P` itself (coefficientwise), which is the
`P ⊆ csP` inclusion the Appendix-A decode needs. -/
def widthScale (P : GAP ℓ d) (k : ℕ) : GAP ℓ d :=
  ⟨P.base, P.step, fun i ↦ k * P.width i⟩

@[simp] theorem widthScale_base (P : GAP ℓ d) (k : ℕ) :
    (P.widthScale k).base = P.base := rfl

@[simp] theorem widthScale_step (P : GAP ℓ d) (k : ℕ) :
    (P.widthScale k).step = P.step := rfl

@[simp] theorem widthScale_width (P : GAP ℓ d) (k : ℕ) :
    (P.widthScale k).width = fun i ↦ k * P.width i := rfl

/-- Evaluating a width-scaled GAP is the same coefficient map. -/
theorem widthScale_eval (P : GAP ℓ d) (k : ℕ) (n : Fin d → ℕ) :
    (P.widthScale k).eval n = P.eval n := rfl

/-- Width-scaling commutes with translation. -/
theorem widthScale_translate (P : GAP ℓ d) (k : ℕ) (t : Fin ℓ → ℤ) :
    (P.widthScale k).translate t = (P.translate t).widthScale k := rfl

/-- `widthScale 1` is the identity. -/
theorem widthScale_one (P : GAP ℓ d) : P.widthScale 1 = P := by
  show GAP.mk P.base P.step (fun i ↦ 1 * P.width i) =
    GAP.mk P.base P.step P.width
  congr 1
  funext i
  exact one_mul _

/-- Nested width-scalings compose multiplicatively. -/
theorem widthScale_widthScale (P : GAP ℓ d) (j k : ℕ) :
    (P.widthScale j).widthScale k = P.widthScale (k * j) := by
  show GAP.mk P.base P.step (fun i ↦ k * (j * P.width i)) =
    GAP.mk P.base P.step (fun i ↦ (k * j) * P.width i)
  congr 1
  funext i
  exact (mul_assoc k j (P.width i)).symm

/-- For `1 ≤ k`, the coefficients of `P` remain coefficients of the widened
progression (`wᵢ ≤ k·wᵢ`). -/
theorem coeffs_subset_widthScale (P : GAP ℓ d) {k : ℕ} (hk : 1 ≤ k) :
    P.coeffs ⊆ (P.widthScale k).coeffs := by
  intro n hn
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hn
  refine Finset.mem_image.mpr ⟨fun i ↦ ⟨(m i : ℕ), ?_⟩, Finset.mem_univ _, ?_⟩
  · exact lt_of_lt_of_le (m i).isLt (Nat.le_mul_of_pos_left _ hk)
  · rw [← hm]

/-- For `1 ≤ k`, `P ⊆ widthScale k P` pointwise — the `P ⊆ csP` inclusion
of CFP23 (the undilated steps `qᵢ` and `0` are points of `csP`, used in the
Appendix-A decode to bound digit vectors). -/
theorem toFinset_subset_widthScale (P : GAP ℓ d) {k : ℕ} (hk : 1 ≤ k) :
    P.toFinset ⊆ (P.widthScale k).toFinset := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨n, P.coeffs_subset_widthScale hk hn, rfl⟩

/-- Properness of the widened progression implies properness of `P` (its
coefficients form a subset).  The converse fails — widening can create
collisions — so `csP` properness is a genuine extra conclusion of CFP23's
theorem.  Note also that `widthScale` does not preserve `Symmetric` in
general (the widened center need not be integral), which is why the decode
returns `P` symmetric and `csP` proper separately. -/
theorem Proper.of_widthScale {P : GAP ℓ d} {k : ℕ} (hk : 1 ≤ k)
    (h : (P.widthScale k).Proper) : P.Proper :=
  h.mono (P.coeffs_subset_widthScale hk)

/-- The coefficient index set has cardinality `∏ widthᵢ`. -/
theorem card_coeffs (P : GAP ℓ d) : P.coeffs.card = ∏ i, P.width i := by
  have hinj : Set.InjOn (fun n : Π i, Fin (P.width i) ↦ fun i ↦ (n i : ℕ))
      (Finset.univ : Finset (Π i, Fin (P.width i))) := by
    intro a _ b _ hab
    funext i
    exact Fin.ext (congrFun hab i)
  show (Finset.univ.image fun n : Π i, Fin (P.width i) ↦ fun i ↦ (n i : ℕ)).card
      = ∏ i, P.width i
  rw [Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ ↦ Fintype.card_fin _

/-- Properness gives the sharp cardinality `|P| = ∏ widthᵢ`. -/
theorem card_toFinset_of_proper (P : GAP ℓ d) (hP : P.Proper) :
    P.toFinset.card = ∏ i, P.width i := by
  show (P.coeffs.image P.eval).card = ∏ i, P.width i
  rw [Finset.card_image_of_injOn hP, card_coeffs]

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

/-- Triangle inequality for a difference of integers. -/
theorem abs_sub_le_abs_add {a b : ℤ} : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le a (-b)).trans_eq (by rw [abs_neg])

/-! ### Tight digit bound and interval-box injectivity

`packVec_inj` requires both vectors in the *balanced* box `|a_j| ≤ K` with
`2K < H`.  The Appendix-A applications instead control *differences*: two
points of an interval box `∏ᵢ [loᵢ, hiᵢ]` differ coordinatewise by at most
`hiᵢ − loᵢ`, so `ϕ` is injective as soon as `H` exceeds every sidelength.
The kernel formulation (`packVec_eq_zero`) only needs `|c_j| < H`. -/

/-- **Tight digit uniqueness**: `packVec` has trivial kernel on the strict
box `|c_j| < H`.  Sharper than `packVec_inj` (which needs `2K < H`) because
it applies to a single difference vector rather than two balanced vectors. -/
theorem packVec_eq_zero {H : ℤ} (hH : 0 < H) :
    ∀ {ℓ : ℕ} {c : Fin ℓ → ℤ}, (∀ j, |c j| < H) → packVec H c = 0 → c = 0 := by
  intro ℓ
  induction ℓ with
  | zero => intro c _ _; exact Subsingleton.elim _ _
  | succ ℓ ih =>
    intro c hc hpack
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
    rw [hsplit c] at hpack
    have hp : packVec H (fun j ↦ c j.succ) = 0 := by
      by_contra hne
      have hlt : |c 0| < H := hc 0
      have heq : c 0 = -(H * packVec H (fun j ↦ c j.succ)) := by linarith
      rw [heq, abs_neg, abs_mul, abs_of_pos hH] at hlt
      have hge : (1 : ℤ) ≤ |packVec H (fun j ↦ c j.succ)| := abs_pos.mpr hne
      have hle : H * 1 ≤ H * |packVec H (fun j ↦ c j.succ)| :=
        mul_le_mul_of_nonneg_left hge hH.le
      linarith
    have hc0 : c 0 = 0 := by
      have heq : c 0 = -(H * packVec H (fun j ↦ c j.succ)) := by linarith
      rw [heq, hp, mul_zero, neg_zero]
    have htail : (fun j : Fin ℓ ↦ c j.succ) = 0 :=
      ih (fun j ↦ hc j.succ) hp
    funext j
    refine Fin.cases hc0 (fun i ↦ ?_) j
    exact congrFun htail i

/-- Injectivity of `ϕ` under a coordinate-difference bound: if `a` and `b`
differ by less than `H` in every coordinate then `ϕ a = ϕ b` gives `a = b`. -/
theorem packVec_inj_of_sub_lt {H : ℤ} (hH : 0 < H) {ℓ : ℕ} {a b : Fin ℓ → ℤ}
    (h : ∀ j, |a j - b j| < H) (hab : packVec H a = packVec H b) : a = b := by
  have h0 : packVec H (a - b) = 0 := by rw [packVec_sub, hab, sub_self]
  have hcb := packVec_eq_zero hH (fun j ↦ by rw [Pi.sub_apply]; exact h j) h0
  exact sub_eq_zero.mp hcb

/-- `ϕ` is injective on a product of intervals `∏ᵢ [loᵢ, hiᵢ]` whenever `H`
strictly exceeds every sidelength `hiᵢ − loᵢ`.  This is the form used in
Appendix A (`ϕ : (−H/2, H/2]^ℓ → ℤ` is injective). -/
theorem packVec_injOn_Icc {H : ℤ} (hH : 0 < H) {ℓ : ℕ} {lo hi : Fin ℓ → ℤ}
    (hw : ∀ i, hi i - lo i < H) :
    Set.InjOn (packVec H)
      (↑(Fintype.piFinset fun i ↦ Finset.Icc (lo i) (hi i)) :
        Set (Fin ℓ → ℤ)) := by
  intro a ha b hb hab
  apply packVec_inj_of_sub_lt hH _ hab
  intro j
  have ha' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp ha j)
  have hb' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hb j)
  have hwj := hw j
  rw [abs_lt]
  constructor <;> omega

/-- Range bound: `|ϕ a| ≤ M·ℓ·H^ℓ` when `|a_j| ≤ M` and `1 ≤ H`. -/
theorem abs_packVec_le {ℓ : ℕ} {H : ℤ} (hH : 1 ≤ H) {a : Fin ℓ → ℤ} {M : ℤ}
    (hM : 0 ≤ M) (ha : ∀ j, |a j| ≤ M) :
    |packVec H a| ≤ M * ℓ * H ^ ℓ := by
  unfold packVec
  calc |∑ j : Fin ℓ, a j * H ^ j.val|
      ≤ ∑ j : Fin ℓ, |a j * H ^ j.val| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin ℓ, M * H ^ ℓ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_pow, abs_of_nonneg (by linarith : (0:ℤ) ≤ H)]
        calc |a j| * H ^ j.val ≤ M * H ^ j.val :=
              mul_le_mul_of_nonneg_right (ha j) (pow_nonneg (by linarith) _)
          _ ≤ M * H ^ ℓ :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH j.isLt.le) hM
    _ = M * ℓ * H ^ ℓ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Nonnegativity: `ϕ a ≥ 0` when all coordinates are nonnegative. -/
theorem packVec_nonneg {ℓ : ℕ} {H : ℤ} (hH : 0 ≤ H) {a : Fin ℓ → ℤ}
    (ha : ∀ j, 0 ≤ a j) : 0 ≤ packVec H a :=
  Finset.sum_nonneg fun j _ ↦ mul_nonneg (ha j) (pow_nonneg hH _)

/-- **Digit vectors exist**: a sum of `ϕ`-images of vectors bounded by `N`
is the `ϕ`-image of the coordinatewise sum, bounded by `s.card * N`.  This
produces the `qᵢ = ϕ⁻¹(q_{0i})` of Appendix A from `q_{0i} ∈ 2sQ` (a `2s`-fold
sum of `ϕ`-images of `[−n, n]^ℓ`). -/
theorem exists_digitVec_of_sum {H : ℤ} {ℓ : ℕ} {s : Finset (Fin ℓ → ℤ)}
    {N : ℤ} (_hN : 0 ≤ N) (hs : ∀ a ∈ s, ∀ j, |a j| ≤ N) :
    ∃ v : Fin ℓ → ℤ, packVec H v = ∑ a ∈ s, packVec H a ∧
      ∀ j, |v j| ≤ s.card * N := by
  refine ⟨∑ a ∈ s, a, packVec_sum H s, fun j ↦ ?_⟩
  rw [Finset.sum_apply]
  calc |∑ a ∈ s, a j| ≤ ∑ a ∈ s, |a j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ s, N := Finset.sum_le_sum fun a ha ↦ hs a ha j
    _ = s.card * N := by rw [Finset.sum_const, nsmul_eq_mul]

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

/-- **Interval-box injectivity** (Appendix A): `ϕ` is injective on
`B.toFinset` whenever `B` is the interval box `∏ᵢ [loᵢ, hiᵢ]` and `H`
strictly exceeds every sidelength `hiᵢ − loᵢ`. -/
theorem packVec_injOn_box {H : ℤ} (hH : 0 < H) {ℓ : ℕ} {B : Box ℓ}
    {lo hi : Fin ℓ → ℤ} (hB : ∀ i, B i = Finset.Icc (lo i) (hi i))
    (hw : ∀ i, hi i - lo i < H) :
    Set.InjOn (packVec H) (B.toFinset : Set (Fin ℓ → ℤ)) := by
  have e : B.toFinset = Fintype.piFinset fun i ↦ Finset.Icc (lo i) (hi i) := by
    show Fintype.piFinset B = _
    congr 1
    funext i
    exact hB i
  rw [e]
  exact packVec_injOn_Icc hH hw

/-- The same, packaged against `Box.IsInterval`. -/
theorem packVec_injOn_isInterval {H : ℤ} (hH : 0 < H) {ℓ : ℕ} {B : Box ℓ}
    (hB : B.IsInterval)
    (hw : ∀ i lo hi, B i = Finset.Icc lo hi → hi - lo < H) :
    Set.InjOn (packVec H) (B.toFinset : Set (Fin ℓ → ℤ)) := by
  choose lo hi hB' using hB
  exact packVec_injOn_box hH hB' fun i ↦ hw i (lo i) (hi i) (hB' i)

/-- **Range bound on a box**: `ϕ` maps an interval box into
`[−MℓH^ℓ, MℓH^ℓ]` when `|loᵢ|, |hiᵢ| ≤ M`. -/
theorem packVec_mem_Icc_box {H : ℤ} (hH : 1 ≤ H) {ℓ : ℕ} {B : Box ℓ}
    {lo hi : Fin ℓ → ℤ} (hB : ∀ i, B i = Finset.Icc (lo i) (hi i)) {M : ℤ}
    (hM0 : 0 ≤ M) (hM : ∀ i, |lo i| ≤ M ∧ |hi i| ≤ M) :
    B.toFinset.image (packVec H) ⊆
      Finset.Icc (-(M * ℓ * H ^ ℓ)) (M * ℓ * H ^ ℓ) := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  rw [Finset.mem_Icc]
  have habs : ∀ j, |a j| ≤ M := by
    intro j
    have haj := Fintype.mem_piFinset.mp ha j
    rw [hB j] at haj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp haj
    obtain ⟨hl, hh⟩ := hM j
    rw [abs_le] at hl hh ⊢
    constructor <;> linarith
  exact abs_le.mp (abs_packVec_le hH hM0 habs)

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

/-! ### Pullback of a `GAP 1` through `ϕ` (Appendix A)

The decoded GAP `P = unpack dig bdig P₀.width` satisfies `ϕ(P) = P₀` at
coordinate `0` (`packVec_unpack_eval`).  The lemmas below assemble the
Appendix-A pullback:

* `Proper.unpack` — properness transfers unconditionally;
* `mem_unpack_of_eval`, `subset_unpack_toFinset`, `zero_mem_unpack` — a
  bounded set `T` with `ϕ(T) ⊆ P₀` is contained in the decoded GAP
  (the `Â ∪ {0} ⊆ P` step);
* `unpack_symmetric` — symmetry transfers when the center has a digit
  vector and decoded points are bounded;
* `packVec_sum_smul_dig`, `unpack_digSum_homogeneous` — the homogeneous
  base choice `bdig = ∑ cᵢ • digᵢ` needs no size condition;
* `subsetSumsL_translate_unpack`, `subsetSumsL_smul_translate_unpack` — the
  subset-sum decode `kP₀ + t ⊆ Σ(ϕ A') ⟹ kP + t' ⊆ Σ(A')`;
* `gap_pullback` — the packaged statement. -/

/-- Properness of `P₀` transfers to the decoded GAP unconditionally:
`eval n = eval m` in `ℤ^ℓ` implies equality of `ϕ`-images, hence of the
`P₀`-evaluations, hence of the coefficients. -/
theorem Proper.unpack {P₀ : GAP 1 d} {H : ℤ} {dig : Fin d → Fin ℓ → ℤ}
    {bdig : Fin ℓ → ℤ} (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0) (hP : P₀.Proper) :
    (unpack dig bdig P₀.width).Proper := by
  intro n hn m hm h
  have hn' : n ∈ P₀.coeffs := by rwa [unpack_coeffs] at hn
  have hm' : m ∈ P₀.coeffs := by rwa [unpack_coeffs] at hm
  apply hP hn' hm'
  apply eval_one_eq.mpr
  rw [← packVec_unpack_eval hdig hbdig n,
    ← packVec_unpack_eval hdig hbdig m, h]

/-- `packVec` commutes with `translate`/`eval` on the decoded GAP. -/
theorem packVec_translate_eval {P₀ : GAP 1 d} {H : ℤ}
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    {t₀ : Fin 1 → ℤ} {tdig : Fin ℓ → ℤ} (ht : packVec H tdig = t₀ 0)
    (n : Fin d → ℕ) :
    packVec H (((unpack dig bdig P₀.width).translate tdig).eval n) =
      ((P₀.translate t₀).eval n) 0 := by
  rw [translate_eval, packVec_add, ht, packVec_unpack_eval hdig hbdig n,
    translate_eval, Pi.add_apply]

/-- **Lifting a point through `ϕ`**: if `ϕ x` agrees with the `0`-coordinate
of a `P₀`-coefficient point `eval n`, and `x` is coordinatewise within `H`
of the decoded point `eval n`, then `x` lies in the decoded GAP.  This is
the lifting step `Â ∪ {0} ⊆ P` of Appendix A. -/
theorem mem_unpack_of_eval {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    {n : Fin d → ℕ} (hn : n ∈ P₀.coeffs) {x : Fin ℓ → ℤ}
    (hx : (P₀.eval n) 0 = packVec H x)
    (hclose : ∀ j, |x j - (unpack dig bdig P₀.width).eval n j| < H) :
    x ∈ (unpack dig bdig P₀.width).toFinset := by
  apply Finset.mem_image.mpr
  refine ⟨n, ?_, ?_⟩
  · show n ∈ (unpack dig bdig P₀.width).coeffs
    rw [unpack_coeffs]; exact hn
  · show (unpack dig bdig P₀.width).eval n = x
    apply packVec_inj_of_sub_lt hH _ _
    · intro j; rw [abs_sub_comm]; exact hclose j
    · rw [packVec_unpack_eval hdig hbdig n]; exact hx

/-- **GAP pullback — containment**: if `ϕ(T) ⊆ P₀` (read at coordinate `0`),
every decoded coefficient point is coordinatewise `≤ K`, `T` is
coordinatewise `≤ Kx`, and `K + Kx < H`, then `T` is contained in the
decoded GAP. -/
theorem subset_unpack_toFinset {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    {T : Finset (Fin ℓ → ℤ)}
    (hT : ∀ x ∈ T, (fun _ : Fin 1 ↦ packVec H x) ∈ P₀.toFinset)
    {K : ℤ} (hbound : ∀ n ∈ P₀.coeffs, ∀ j,
      |(unpack dig bdig P₀.width).eval n j| ≤ K)
    {Kx : ℤ} (hx : ∀ x ∈ T, ∀ j, |x j| ≤ Kx)
    (hKH : K + Kx < H) :
    T ⊆ (unpack dig bdig P₀.width).toFinset := by
  intro x hxT
  obtain ⟨n, hn, heval⟩ := Finset.mem_image.mp (hT x hxT)
  have hx0 : (P₀.eval n) 0 = packVec H x := congrFun heval 0
  apply mem_unpack_of_eval hH hdig hbdig hn hx0
  intro j
  have h1 := abs_sub_le_abs_add (a := x j)
    (b := (unpack dig bdig P₀.width).eval n j)
  linarith [h1, hx x hxT j, hbound n hn j]

/-- `0` lies in the decoded GAP when the constant-`0` point lies in `P₀`
and decoded points are bounded by `K < H`. -/
theorem zero_mem_unpack {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    (h0 : (fun _ : Fin 1 ↦ (0 : ℤ)) ∈ P₀.toFinset)
    {K : ℤ} (hbound : ∀ n ∈ P₀.coeffs, ∀ j,
      |(unpack dig bdig P₀.width).eval n j| ≤ K)
    (hKH : K < H) :
    (0 : Fin ℓ → ℤ) ∈ (unpack dig bdig P₀.width).toFinset := by
  obtain ⟨n, hn, heval⟩ := Finset.mem_image.mp h0
  have hx0 : (P₀.eval n) 0 = packVec H (0 : Fin ℓ → ℤ) := by
    rw [packVec_zero]; exact congrFun heval 0
  apply mem_unpack_of_eval hH hdig hbdig hn hx0
  intro j
  rw [Pi.zero_apply, zero_sub, abs_neg]
  exact lt_of_le_of_lt (hbound n hn j) hKH

/-- Symmetry transfers to the decoded GAP when the center has a digit
vector and decoded points are bounded (`2Km + 2K < H`). -/
theorem unpack_symmetric {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    {m₀ : Fin 1 → ℤ} (hm₀ : ∀ x ∈ P₀.toFinset, (2 • m₀ - x) ∈ P₀.toFinset)
    {mdig : Fin ℓ → ℤ} (hm : packVec H mdig = m₀ 0)
    {K Km : ℤ} (hbound : ∀ n ∈ P₀.coeffs, ∀ j,
      |(unpack dig bdig P₀.width).eval n j| ≤ K)
    (hmdig : ∀ j, |mdig j| ≤ Km) (hH2 : 2 * Km + 2 * K < H) :
    (unpack dig bdig P₀.width).Symmetric := by
  have h2v : ∀ v : Fin ℓ → ℤ, packVec H (2 • v) = 2 * packVec H v := by
    intro v
    unfold packVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, Int.nsmul_eq_mul, Nat.cast_ofNat]
    ring
  refine ⟨mdig, fun x hx ↦ ?_⟩
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hn₀ : n ∈ P₀.coeffs := by rwa [unpack_coeffs] at hn
  have hmem : P₀.eval n ∈ P₀.toFinset := Finset.mem_image.mpr ⟨n, hn₀, rfl⟩
  obtain ⟨n', hn', hnn'⟩ := Finset.mem_image.mp (hm₀ _ hmem)
  have hn'' : n' ∈ (unpack dig bdig P₀.width).coeffs := by
    rwa [unpack_coeffs]
  refine Finset.mem_image.mpr ⟨n', hn'', ?_⟩
  apply packVec_inj_of_sub_lt hH
  · intro j
    rw [abs_sub_comm]
    have habs : |(2 • mdig - (unpack dig bdig P₀.width).eval n) j -
        (unpack dig bdig P₀.width).eval n' j| ≤
        2 * |mdig j| + |(unpack dig bdig P₀.width).eval n j| +
          |(unpack dig bdig P₀.width).eval n' j| := by
      have e1 : (2 • mdig - (unpack dig bdig P₀.width).eval n) j =
          2 * mdig j - (unpack dig bdig P₀.width).eval n j := by
        simp [Pi.sub_apply, Nat.cast_ofNat]
      rw [e1]
      have h2a := abs_sub_le_abs_add
        (a := 2 * mdig j - (unpack dig bdig P₀.width).eval n j)
        (b := (unpack dig bdig P₀.width).eval n' j)
      have h2b := abs_sub_le_abs_add (a := 2 * mdig j)
        (b := (unpack dig bdig P₀.width).eval n j)
      have h2c : |2 * mdig j| = 2 * |mdig j| := by
        rw [abs_mul]; norm_num
      linarith
    linarith [habs, hbound n hn₀ j, hbound n' hn' j, hmdig j]
  · rw [packVec_sub, h2v mdig, hm, packVec_unpack_eval hdig hbdig n,
      packVec_unpack_eval hdig hbdig n']
    have e : (P₀.eval n') 0 = 2 * m₀ 0 - (P₀.eval n) 0 := by
      have e := congrFun hnn' 0
      simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.nsmul_eq_mul,
        Nat.cast_ofNat] using e
    exact e

/-- The homogeneous base choice: `ϕ(∑ cᵢ • digᵢ) = ∑ cᵢ • wᵢ = P₀.base 0`
when `P₀` is homogeneous with coefficients `c`.  No size condition is
needed since the base is *defined* by the digit combination. -/
theorem packVec_sum_smul_dig {P₀ : GAP 1 d} {H : ℤ}
    {dig : Fin d → Fin ℓ → ℤ} {c : Fin d → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hc : P₀.base = ∑ i, c i • P₀.step i) :
    packVec H (∑ i, c i • dig i) = P₀.base 0 := by
  rw [hc, packVec_sum' Finset.univ, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [Pi.smul_apply, smul_eq_mul, packVec_smul, hdig i]

/-- The decoded GAP with homogeneous base `∑ cᵢ • digᵢ` is homogeneous
with the same coefficients. -/
theorem unpack_digSum_homogeneous {dig : Fin d → Fin ℓ → ℤ} {c : Fin d → ℤ}
    {w : Fin d → ℕ} :
    (unpack dig (∑ i, c i • dig i) w).Homogeneous := ⟨c, rfl⟩

/-- Bound on decoded coefficient points: `|eval n| ≤ Kb + (∑ wᵢ)·Kd` when the
base digits are `≤ Kb` and the step digits `≤ Kd`.  Feeds the `H`-domination
hypotheses of the pullback lemmas; in Appendix A `Kd ≤ 2sn`
(`qᵢ ∈ [−2sn, 2sn]^ℓ`) and `wᵢ ≤ (sn)^ℓ`. -/
theorem abs_unpack_eval_le {P₀ : GAP 1 d} {dig : Fin d → Fin ℓ → ℤ}
    {bdig : Fin ℓ → ℤ} (n : Fin d → ℕ) (hn : n ∈ P₀.coeffs)
    {Kb Kd : ℤ} (hb : ∀ j, |bdig j| ≤ Kb)
    (hd : ∀ i, ∀ j, |dig i j| ≤ Kd) (_hKd : 0 ≤ Kd) (j : Fin ℓ) :
    |(unpack dig bdig P₀.width).eval n j| ≤
      Kb + (∑ i, (P₀.width i : ℤ)) * Kd := by
  have h1 : (unpack dig bdig P₀.width).eval n j =
      bdig j + ∑ i, (n i : ℤ) * dig i j := by
    show (bdig + ∑ i, (n i : ℤ) • dig i) j = _
    rw [Pi.add_apply, Finset.sum_apply]
    refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [Pi.smul_apply, smul_eq_mul]
  rw [h1]
  have hbound : |∑ i : Fin d, (n i : ℤ) * dig i j| ≤
      ∑ i : Fin d, (P₀.width i : ℤ) * Kd := by
    calc |∑ i, (n i : ℤ) * dig i j| ≤ ∑ i, |(n i : ℤ) * dig i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (P₀.width i : ℤ) * Kd := by
        apply Finset.sum_le_sum
        intro i _
        have hni : (n i : ℤ) ≤ (P₀.width i : ℤ) := by
          exact_mod_cast (coeff_mem_width hn i).le
        have hnn : (0 : ℤ) ≤ (n i : ℤ) := by positivity
        rw [abs_mul, abs_of_nonneg hnn]
        exact mul_le_mul hni (hd i j) (abs_nonneg _) (by positivity)
  calc |bdig j + ∑ i, (n i : ℤ) * dig i j|
      ≤ |bdig j| + |∑ i, (n i : ℤ) * dig i j| := abs_add_le _ _
    _ ≤ Kb + ∑ i, (P₀.width i : ℤ) * Kd := add_le_add (hb j) hbound
    _ = Kb + (∑ i, (P₀.width i : ℤ)) * Kd := by rw [Finset.sum_mul]

/-- **Subset-sum decode** (Appendix A): a translate of `P₀` contained in
`Σ(ϕ A')` pulls back to a translate of the decoded GAP contained in
`Σ(A')`.  The hypotheses say: `A'` has coordinates `≤ Ka` with `2Ka < H`
(so `ϕ` is injective on `A'`), `tdig` is a digit vector of `t₀`, and for
every coefficient tuple `|tdig| + |eval| + |A'|·Ka < H` — the domination
bound that upgrades `ϕ`-equality to pointwise equality. -/
theorem subsetSumsL_translate_unpack {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    {t₀ : Fin 1 → ℤ} {tdig : Fin ℓ → ℤ} (ht : packVec H tdig = t₀ 0)
    {A' : Finset (Fin ℓ → ℤ)} {Ka : ℤ} (hKa0 : 0 ≤ Ka)
    (hKa : ∀ a ∈ A', ∀ j, |a j| ≤ Ka) (h2K : 2 * Ka < H)
    (hsub : (P₀.translate t₀).toFinset ⊆
      subsetSumsL (A'.image fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x))
    (hbound : ∀ n ∈ P₀.coeffs, ∀ j,
      |tdig j| + |(unpack dig bdig P₀.width).eval n j| +
        (A'.card : ℤ) * Ka < H) :
    ((unpack dig bdig P₀.width).translate tdig).toFinset ⊆ subsetSumsL A' := by
  intro y hy
  obtain ⟨n, hn, hny⟩ := Finset.mem_image.mp hy
  have hn₀ : n ∈ P₀.coeffs := by rwa [translate_coeffs, unpack_coeffs] at hn
  -- `ϕ y` is the `0`-coordinate of the corresponding `P₀`-translate point.
  have hmem : (fun _ : Fin 1 ↦ packVec H y) ∈ (P₀.translate t₀).toFinset := by
    apply Finset.mem_image.mpr
    refine ⟨n, by rwa [translate_coeffs], ?_⟩
    funext i
    rw [Fin.eq_zero i]
    show ((P₀.translate t₀).eval n) 0 = packVec H y
    rw [← packVec_translate_eval hdig hbdig ht n, hny]
  obtain ⟨S₀, hS₀, hsum₀⟩ := mem_subsetSumsL.mp (hsub hmem)
  -- Pull `S₀ ⊆ ϕ(A')` back to a subset `S ⊆ A'`.
  obtain ⟨S, hS, rfl⟩ := Finset.subset_image_iff.mp hS₀
  -- `ϕ` is injective on `A'` (coordinates differ by at most `2Ka < H`).
  have hinj : Set.InjOn (fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x)
      ↑A' := by
    intro a ha b hb hab
    apply packVec_inj_of_sub_lt hH _ (congrFun hab 0)
    intro j
    have h1 := abs_le.mp (hKa a ha j)
    have h2 := abs_le.mp (hKa b hb j)
    rw [abs_lt]; constructor <;> linarith
  have hinjS := hinj.mono (Finset.coe_subset.mpr hS)
  -- `ϕ y = ϕ (∑ S)`: both sides agree at coordinate `0`.
  have hpk : packVec H y = packVec H (∑ a ∈ S, a) := by
    have e1 : (∑ b ∈ S.image
        (fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x), b) 0 =
          packVec H y := by
      have hh := congrFun hsum₀ 0
      rw [Finset.sum_apply] at hh ⊢
      exact hh
    have e2 : (∑ b ∈ S.image
        (fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x), b) =
        ∑ a ∈ S, (fun _ : Fin 1 ↦ packVec H a) :=
      Finset.sum_image hinjS
    have e3 : (∑ a ∈ S, (fun _ : Fin 1 ↦ packVec H a)) 0 =
        packVec H (∑ a ∈ S, a) := by
      rw [Finset.sum_apply]
      exact (packVec_sum H S).symm
    rw [← e3, ← e2, e1]
  -- `|σ_j| ≤ |A'|·Ka` for `σ = ∑ S`.
  have hσ : ∀ j, |(∑ a ∈ S, a) j| ≤ (A'.card : ℤ) * Ka := by
    intro j
    rw [Finset.sum_apply]
    calc |∑ a ∈ S, a j| ≤ ∑ a ∈ S, |a j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ S, Ka := Finset.sum_le_sum fun a ha ↦ hKa a (hS ha) j
      _ = (S.card : ℤ) * Ka := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A'.card : ℤ) * Ka := mul_le_mul_of_nonneg_right
          (by exact_mod_cast Finset.card_le_card hS) hKa0
  have hclose : ∀ j, |y j - (∑ a ∈ S, a) j| < H := by
    intro j
    have hyj : y j = tdig j + (unpack dig bdig P₀.width).eval n j := by
      rw [← hny, translate_eval, Pi.add_apply]
    rw [hyj]
    have htr : |tdig j + (unpack dig bdig P₀.width).eval n j - (∑ a ∈ S, a) j|
        ≤ |tdig j| + |(unpack dig bdig P₀.width).eval n j| +
          |(∑ a ∈ S, a) j| := by
      have e1 := abs_sub_le_abs_add (a := tdig j +
        (unpack dig bdig P₀.width).eval n j) (b := (∑ a ∈ S, a) j)
      have e2 := abs_add_le (tdig j) ((unpack dig bdig P₀.width).eval n j)
      linarith
    have hb := hbound n hn₀ j
    have hσj := hσ j
    linarith
  have hyeq : y = ∑ a ∈ S, a := packVec_inj_of_sub_lt hH hclose hpk
  exact mem_subsetSumsL.mpr ⟨S, hS, hyeq.symm⟩

/-- `k • unpack` is the decode of `k • P₀`. -/
theorem smul_unpack (k : ℤ) (dig : Fin d → Fin ℓ → ℤ) (bdig : Fin ℓ → ℤ)
    (w : Fin d → ℕ) :
    k • unpack dig bdig w = unpack (fun i ↦ k • dig i) (k • bdig) w := rfl

/-- Properness of `k • P₀` transfers to `k •` the decoded GAP. -/
theorem Proper.smul_unpack {P₀ : GAP 1 d} {H : ℤ} (k : ℤ)
    {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    (hP : (k • P₀).Proper) : (k • GAP.unpack dig bdig P₀.width).Proper := by
  have hdig' : ∀ i, packVec H (k • dig i) = (k • P₀).step i 0 := fun i ↦ by
    rw [packVec_smul, hdig i]; rfl
  have hbdig' : packVec H (k • bdig) = (k • P₀).base 0 := by
    rw [packVec_smul, hbdig]; rfl
  change (GAP.unpack (fun i ↦ k • dig i) (k • bdig) P₀.width).Proper
  exact Proper.unpack (P₀ := k • P₀) hdig' hbdig' hP

/-- **Subset-sum decode, dilated form**: `k • P₀ + t₀ ⊆ Σ(ϕ A')` pulls back
to `k • P + tdig ⊆ Σ(A')` where `P` is the decoded GAP.  This is the
`x + csP ⊆ Σ(A')` conclusion of Appendix A (with `t = ϕ⁻¹(x₀)` playing the
role of `x`). -/
theorem subsetSumsL_smul_translate_unpack {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    (k : ℤ) {dig : Fin d → Fin ℓ → ℤ} {bdig : Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    (hbdig : packVec H bdig = P₀.base 0)
    {t₀ : Fin 1 → ℤ} {tdig : Fin ℓ → ℤ} (ht : packVec H tdig = t₀ 0)
    {A' : Finset (Fin ℓ → ℤ)} {Ka : ℤ} (hKa0 : 0 ≤ Ka)
    (hKa : ∀ a ∈ A', ∀ j, |a j| ≤ Ka) (h2K : 2 * Ka < H)
    (hsub : ((k • P₀).translate t₀).toFinset ⊆
      subsetSumsL (A'.image fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x))
    (hbound : ∀ n ∈ P₀.coeffs, ∀ j,
      |tdig j| + |(k • unpack dig bdig P₀.width).eval n j|
        + (A'.card : ℤ) * Ka < H) :
    ((k • unpack dig bdig P₀.width).translate tdig).toFinset ⊆
      subsetSumsL A' := by
  have hdig' : ∀ i, packVec H (k • dig i) = (k • P₀).step i 0 := fun i ↦ by
    rw [packVec_smul, hdig i]; rfl
  have hbdig' : packVec H (k • bdig) = (k • P₀).base 0 := by
    rw [packVec_smul, hbdig]; rfl
  rw [smul_unpack]
  exact subsetSumsL_translate_unpack hH hdig' hbdig' ht hKa0 hKa h2K hsub hbound

/-- `ϕ` commutes with subset sums: `ϕ(Σ A') = Σ(ϕ A')` when `ϕ` is
injective on `A'` (coordinates `≤ Ka` with `2Ka < H`).  This is the
`Σ(ϕ '' A') ⊆ ϕ(Σ A')`-type transfer used in the Appendix-A decode. -/
theorem subsetSumsL_image_packVec {H : ℤ} (hH : 0 < H)
    {A' : Finset (Fin ℓ → ℤ)} {Ka : ℤ}
    (hKa : ∀ a ∈ A', ∀ j, |a j| ≤ Ka) (h2K : 2 * Ka < H) :
    (subsetSumsL A').image (fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x) =
      subsetSumsL (A'.image fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x) := by
  have hinj : Set.InjOn (fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x)
      ↑A' := by
    intro a ha b hb hab
    apply packVec_inj_of_sub_lt hH _ (congrFun hab 0)
    intro j
    have h1 := abs_le.mp (hKa a ha j)
    have h2 := abs_le.mp (hKa b hb j)
    rw [abs_lt]; constructor <;> linarith
  ext z
  constructor
  · intro hz
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨S, hS, hsum⟩ := mem_subsetSumsL.mp hσ
    apply mem_subsetSumsL.mpr
    refine ⟨S.image (fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x),
      Finset.image_subset_image hS, ?_⟩
    rw [Finset.sum_image (hinj.mono (Finset.coe_subset.mpr hS))]
    funext i
    rw [Finset.sum_apply]
    show (∑ a ∈ S, packVec H a) = packVec H σ
    rw [← packVec_sum H S]
    exact congrArg (packVec H) hsum
  · intro hz
    obtain ⟨S₀, hS₀, hsum₀⟩ := mem_subsetSumsL.mp hz
    obtain ⟨S, hS, rfl⟩ := Finset.subset_image_iff.mp hS₀
    apply Finset.mem_image.mpr
    refine ⟨∑ a ∈ S, a, mem_subsetSumsL.mpr ⟨S, hS, rfl⟩, ?_⟩
    rw [← hsum₀, Finset.sum_image (hinj.mono (Finset.coe_subset.mpr hS))]
    funext i
    rw [Finset.sum_apply]
    show packVec H (∑ a ∈ S, a) = ∑ a ∈ S, packVec H a
    exact packVec_sum H S

/-- A padded GAP still contains the original progression (take the last
coefficient `0`).  Together with `padStep_proper`/`padStep_homogeneous`/
`padStep_symmetric` this is the "dimension `+1`" padding that absorbs a
translation whose digit vector may have negative entries. -/
theorem toFinset_subset_padStep {P : GAP ℓ d} {v : Fin ℓ → ℤ} {w₀ : ℕ}
    (hw : 0 < w₀) : P.toFinset ⊆ (P.padStep v w₀).toFinset := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  exact mem_padStep.mpr ⟨n, hn, 0, hw, by simp⟩

/-- **The Appendix-A GAP pullback, packaged.**  If `P₀ : GAP 1 d` is proper
and homogeneous with `ϕ`-decodable steps `dig`, base coefficient vector `c`,
and decodable symmetry center `mdig`, and the decoded coefficient points and
the center digits satisfy the displayed domination bounds, then the decoded
GAP `P = unpack dig (∑ cᵢ • digᵢ) P₀.width` is proper, homogeneous,
symmetric, and contains `T ∪ {0}` for every `Kx`-bounded `T` with
`ϕ(T) ⊆ P₀`. -/
theorem gap_pullback {P₀ : GAP 1 d} {H : ℤ} (hH : 0 < H)
    {dig : Fin d → Fin ℓ → ℤ}
    (hdig : ∀ i, packVec H (dig i) = P₀.step i 0)
    {c : Fin d → ℤ} (hc : P₀.base = ∑ i, c i • P₀.step i)
    (hP : P₀.Proper)
    {m₀ : Fin 1 → ℤ} (hm₀ : ∀ x ∈ P₀.toFinset, (2 • m₀ - x) ∈ P₀.toFinset)
    {mdig : Fin ℓ → ℤ} (hm : packVec H mdig = m₀ 0)
    {K Km Kx : ℤ}
    (hbound : ∀ n ∈ P₀.coeffs, ∀ j,
      |(unpack dig (∑ i, c i • dig i) P₀.width).eval n j| ≤ K)
    (hmdig : ∀ j, |mdig j| ≤ Km) (hHm : 2 * Km + 2 * K < H)
    {T : Finset (Fin ℓ → ℤ)}
    (hT : ∀ x ∈ T, (fun _ : Fin 1 ↦ packVec H x) ∈ P₀.toFinset)
    (hx : ∀ x ∈ T, ∀ j, |x j| ≤ Kx) (hKH : K + Kx < H)
    (h0 : (fun _ : Fin 1 ↦ (0 : ℤ)) ∈ P₀.toFinset) (hK0 : K < H) :
    ∃ P : GAP ℓ d, T ∪ {0} ⊆ P.toFinset ∧ P.Proper ∧ P.Homogeneous ∧
      P.Symmetric := by
  have hb := packVec_sum_smul_dig hdig hc
  refine ⟨unpack dig (∑ i, c i • dig i) P₀.width, ?_, ?_, ?_, ?_⟩
  · exact Finset.union_subset
      (subset_unpack_toFinset hH hdig hb hT hbound hx hKH)
      (Finset.singleton_subset_iff.mpr
        (zero_mem_unpack hH hdig hb h0 hbound hK0))
  · exact Proper.unpack hdig hb hP
  · exact ⟨c, rfl⟩
  · exact unpack_symmetric hH hdig hb hm₀ hm hbound hmdig hHm

/-- For `H ≥ 2` the geometric sum `∑_{j < ℓ} H^j` is at most `H^ℓ`
(`∑ H^j ≤ H^{ℓ-1}(1 + … ) ≤ 2H^{ℓ-1} ≤ H·H^{ℓ-1}`).  Used to bound the
base-`H` packing `packVec` of vectors in `[0, n]^ℓ`. -/
theorem geom_sum_le {H : ℤ} (hH : 2 ≤ H) :
    ∀ ℓ : ℕ, ∑ j ∈ Finset.range ℓ, H ^ j ≤ H ^ ℓ := by
  intro ℓ
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [Finset.sum_range_succ]
    calc (∑ j ∈ Finset.range ℓ, H ^ j) + H ^ ℓ
        ≤ H ^ ℓ + H ^ ℓ := by linarith [ih]
      _ = 2 * H ^ ℓ := by ring
      _ ≤ H * H ^ ℓ := mul_le_mul_of_nonneg_right hH (pow_nonneg (by linarith) _)
      _ = H ^ (ℓ + 1) := by rw [← pow_succ']

/-- **Residual input — the Appendix-A decode** (Pham–Zakharov
arXiv:2410.14624v2, Appendix A).  Given a proper, symmetric `P₀ : GAP 1 d'`
covering the `packVec`-image of `Â₀ ⊆ [0,n]^ℓ` together with the
*width-scaled* containment `(widthScale k P₀).translate t ⊆ Σ(ϕ A'₀)`
(the `x₀ + csP₀ ⊆ Σ(A'₀)` of the paper, where `csP₀` is CFP23's
coefficient-scaled `cQ`), the conclusion is a decoded `P : GAP ℓ d'` —
symmetric, containing `Â₀ ∪ {0}` — with `widthScale k P` proper and a
translate of `widthScale k P` inside `Σ(A'₀)`.

The paper's proof in this form: `P₀ ⊆ widthScale k P₀`
(`toFinset_subset_widthScale`, using `k ≥ 1`), so the undilated steps
`q_{0i} ∈ P₀ − P₀ ⊆ widthScale k P₀ − widthScale k P₀ ⊆ 2s·Q`-type subset
sums; unpacking `q_{0i}` via `packVec` yields digit vectors
`dig i : Fin ℓ → ℤ` with `|dig i j| ≤ 2sn`, and the decoded GAP is
`unpack dig (−∑ n⁰ᵢ • dig i) P₀.width` where `n⁰` is the coefficient of `0`
(`Proper.unpack` + `subsetSumsL_translate_unpack` + `unpack_symmetric`),
`hdom` being the paper's domination `cH > ns²(sn)^ℓ`.  The symmetry center
digit vector `m₀` still needs the centered form the paper's Theorem 5
returns (or a parity argument on the coefficient of `0`), and dimensions
with `k·wᵢ = 1` (dead steps, `wᵢ = k = 1`) must be pruned or zeroed before
unpacking — these are the remaining inputs isolated in this lemma.

**Status (round 15).**  The statement is *not* derivable from the listed
hypotheses — two inputs are missing that `cfp_main`'s conclusion does not
supply:

(a) `(P₀.widthScale k).Proper`.  Without it the conclusion is *false*:
take `Â₀ = A'₀ = ∅`, `d' = 1`, `P₀ = ⟨0, 0, 1⟩` (point set `{0}`, proper
and symmetric), `k = 2`, `t = 0`, `hdom` met for large `H`.  Then
`Σ(A'₀) = {0}` and `hcont` holds, but any `P` containing `0` has
`P.width i ≥ 1`, so a proper `P.widthScale 2` has `≥ 2` points and no
translate fits in `{0}`.  The caller `cfp_structure` *does* have this
input in scope (`hkP₀`, currently unused).

(b) A *zero-centred* symmetry `∀ x ∈ P₀.toFinset, -x ∈ P₀.toFinset`
(equivalently odd widths, or a parity input).  The decoded
`P = unpack dig bdig P₀.width` is symmetric iff the vector
`V = 2·bdig + Σᵢ (P₀.width i - 1) • dig i` is componentwise even; the
∃-centre `P₀.Symmetric` only gives `packVec V = 2·m₀ 0` even, and bounded
`packVec`-decodes are unique (`packVec_inj_of_sub_lt`), so no choice of
subset-sum witnesses can repair an odd `V` for `ℓ ≥ 2`.  With `0`-centred
symmetry the centre `M = 0` works directly (the reflection
`eval m ↦ -eval m` is realised on coefficients, and
`u_{m'} - u_{n⁰} = -(u_m - u_{n⁰})` by `packVec`-injectivity on the
bounded box).  This is a statement-fidelity gap in `cfp_main`: CFP23's
`P` may be taken centred (widths `2Nᵢ+1`); see its docstring.

With (a) and (b) the lemma *is* provable: for `n ∈ (P₀.widthScale k).coeffs`
choose `Sₙ ⊆ A'₀` with `packVec (u n) = eval n 0 + t 0`,
`u n := Σ_{a ∈ Sₙ} a` bounded by `sn`; then `dig i := u(eᵢ) - u(0)`
(`k·wᵢ ≥ 2`), `bdig := u(0) - u(n⁰)`, `tdig := u(n⁰)` where `n⁰` is the
coefficient of `0` (so `t = eval n⁰ + t ∈ Σ(ϕA'₀)` itself, giving the
bounded decode of `t`).  Induction on `Σ nᵢ` using
`u_{n-eᵢ} + u_{eᵢ} = u_n + u_0` (both sides `packVec`-equal and `≤ 3sn`)
gives `eval n = u_n - u_{n⁰}`, hence `|eval n j| ≤ 2sn` and the translate
point is *exactly* `u_n ∈ Σ(A'₀)`. -/
theorem appendix_decode {ℓ : ℕ} (hℓ : 0 < ℓ) {H : ℤ} (hH : 1 < H)
    {n s : ℕ} {Â₀ A'₀ : Finset (Fin ℓ → ℤ)}
    (hÂ : ∀ a ∈ Â₀, ∀ j, 0 ≤ a j ∧ a j ≤ (n : ℤ))
    (hA' : ∀ a ∈ A'₀, ∀ j, 0 ≤ a j ∧ a j ≤ (n : ℤ))
    (hA'card : (A'₀.card : ℤ) ≤ (s : ℤ))
    {d' : ℕ} {P₀ : GAP 1 d'} (hP₀ : P₀.Proper) (hP₀s : P₀.Symmetric)
    (hsub : ∀ a ∈ Â₀, (fun _ : Fin 1 ↦ packVec H a) ∈ P₀.toFinset)
    (h0 : (0 : Fin 1 → ℤ) ∈ P₀.toFinset)
    {k : ℕ} (hk : 0 < k) {t : Fin 1 → ℤ}
    (hcont : ((P₀.widthScale k).translate t).toFinset ⊆
      subsetSumsL (A'₀.image fun x : Fin ℓ → ℤ ↦ fun _ : Fin 1 ↦ packVec H x))
    (hdom : (8 : ℤ) * ((k : ℤ) + 1) * ((s : ℤ) + 1) * ((n : ℤ) + 1) *
      (2 * (s : ℤ) * (n : ℤ) + 1) ^ (2 * ℓ) < H) :
    ∃ P : GAP ℓ d', P.Symmetric ∧ (Â₀ ∪ {0}) ⊆ P.toFinset ∧
      ∃ tdig : Fin ℓ → ℤ, ((P.widthScale k).translate tdig).toFinset ⊆
        subsetSumsL A'₀ ∧ (P.widthScale k).Proper := by
  sorry

/-- **Residual input — the unanchored-box lift.**  If the Appendix-A
conclusion holds for the anchored translate `A₀ = A − lo`, it lifts to `A`
itself: a padded `P'` (dimension `d' + 1`, the extra `padStep` absorbing
the corner `lo`) containing `(Â₀ + lo) ∪ {0}`, and a translate of
`widthScale k P'` inside `Σ(A'₀ + lo)`.

The obstruction is the translation non-invariance of `Σ`: an element of
`Σ(A'₀)` is a `j`-element subset sum of `A'₀` shifted by `j • lo`, with `j`
varying over the point, so a *uniform* translate inside `Σ(A'₀ + lo)`
requires the fixed-cardinality machinery of `subsetSumsL_translate_of_card`
— which `cfp_main`'s all-cardinality `Σ` conclusion does not supply.  For
`lo = 0` (the paper's `WLOG B = [n]^ℓ`) it is immediate
(`P' = P.padStep 0 1`, `t = tdig`; `widthScale` commutes with `padStep`
and `translate`, and `P.padStep 0 1` has the same point set as `P`); the
general case is the WLOG step the paper elides. -/
theorem cfp_unshift {ℓ d' : ℕ} {P : GAP ℓ d'} {lo : Fin ℓ → ℤ} {k : ℕ}
    {Â₀ A'₀ : Finset (Fin ℓ → ℤ)} {tdig : Fin ℓ → ℤ}
    (hPmem : Â₀ ∪ {0} ⊆ P.toFinset) (hPs : P.Symmetric)
    (hcont : ((P.widthScale k).translate tdig).toFinset ⊆ subsetSumsL A'₀)
    (hkP : (P.widthScale k).Proper) :
    ∃ P' : GAP ℓ (d' + 1), P'.Symmetric ∧
      (Â₀.image (· + lo) ∪ {0}) ⊆ P'.toFinset ∧
      ∃ t : Fin ℓ → ℤ, ((P'.widthScale k).translate t).toFinset ⊆
        subsetSumsL (A'₀.image (· + lo)) ∧ (P'.widthScale k).Proper := by
  sorry

end GAP

open GAP

/-- **CFP23 main theorem** (Conlon–Fox–Pham, Theorem 1.5), quoted as
**Theorem 5** in Pham–Zakharov (arXiv:2410.14624v2).  This is the deep
external input to `cfp_structure`: it is stated here as a black box and is
*not* proved in this file (the placeholder is the quoted theorem itself).

For `A ⊆ [n] ⊆ ℤ` with `|A| = m`, `n ≤ m^β` and
`s ∈ [m^η, c·m / log m]`, it gives `Â ⊆ A` with
`|Â| ≥ m − c⁻¹·s·log m`, a proper `d'`-dimensional (`d' ≤ d`) GAP `P` with
`Â ∪ {0} ⊆ P`, and `A' ⊆ Â` with `|A'| ≤ s` such that `Σ(A')` contains a
homogeneous translate of a `≤ c·s` *width-scaling* `cs·P` of `P` (CFP23's
coefficient scaling `cQ`, `GAP.widthScale` — not the pointwise dilation
`k • P`), which remains proper.

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
                ((P.widthScale k).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
                (P.widthScale k).Proper := by
  sorry

set_option maxHeartbeats 800000 in
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
`0 < k ≤ c·s = 0`).  A *largeness* hypothesis `N₀(c,ℓ) < |A|` with
`N₀(c,ℓ) = 16·(c+1)·(c/log 2 + 1)²·(2c/log 2 + 1)^{2ℓ}` implements the
paper's "choose `n₀` large" step: it is exactly what makes the
Appendix-A domination `8(k+1)(s+1)(n+1)(2sn+1)^{2ℓ} < n^{10ℓ³} = H`
provable (`s ≤ c·m/log m ≤ (c/log 2)·n`, `k ≤ c·s`, `m ≤ n` bound the
left side by `N₀·n^{4ℓ+3}`, and `10ℓ³ ≥ 4ℓ+4` absorbs `N₀` once
`n > N₀`).  See
`discovery/JSP-000179/scratch/cfp_derivation_report.md` for the full
analysis, including the Appendix-A `H`-sizing (`κ = 10ℓ³`, `H = n^κ`,
`cH > n s² (sn)^ℓ`) and the translation subtlety for non-anchored boxes
(`Σ` is not translation-invariant; the paper's `WLOG B = [n]^ℓ` is only
directly justified for anchored boxes, while Lemma-8-style applications
use symmetric boxes — a faithful derivation must resolve this, e.g. by
padding the decoded GAP to absorb the shift).

**Proof status / missing input.**  The decode lemmas `GAP.gap_pullback`,
`GAP.subsetSumsL_translate_unpack` require digit vectors
`dig i : Fin ℓ → ℤ` of the *undilated* steps `P₀.step i 0` — the paper's
`q_{0i} ∈ 2sQ` step.  There `csP₀` is the coefficient-interval scaling
(CFP23's `cQ`, here `GAP.widthScale`), which contains `P₀` itself since
`0 ∈ P₀`; hence `q_{0i} ∈ P₀ ⊆ csP₀ ⊆ Σ(A'₀) − x₀ ⊆ 2sQ` is a `2s`-fold
sum of `ϕ`-images of `≤ n`-bounded vectors, so `dig i` exists with
`|dig i| ≤ 2sn`.  `cfp_main` now supplies the width-scaled containment
`(widthScale k P₀).translate t₀ ⊆ Σ(ϕ A'₀)`, matching the paper's shape;
the remaining gaps are isolated in `appendix_decode` (digit vectors of the
undilated steps, the symmetry-center parity, dead dimensions `k·wᵢ = 1`)
and `cfp_unshift` (for non-anchored `B` the shift back by `lo` needs
fixed-cardinality subset sums `subsetSumsL_translate_of_card`, which
`cfp_main`'s all-cardinality `Σ` conclusion does not supply). -/
theorem cfp_structure (ℓ : ℕ) {β η : ℝ} (hβ : 1 < β) (hη : 0 < η) (hη1 : η < 1) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ (A : Finset (Fin ℓ → ℤ)) (B : GAP.Box ℓ) (s : ℕ),
      A.Nonempty → B.IsInterval →
      A ⊆ B.toFinset → (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
      (A.card : ℝ) ^ η ≤ s → (s : ℝ) ≤ c * A.card / Real.log A.card →
      16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
        (2 * (c / Real.log 2) + 1) ^ (2 * ℓ) < (A.card : ℝ) →
      ∃ (Â : Finset (Fin ℓ → ℤ)) (d' : ℕ) (P : GAP ℓ d'),
        Â ⊆ A ∧ (A.card : ℝ) - c⁻¹ * s * Real.log A.card ≤ Â.card ∧
        (d' : ℝ) ≤ d ∧ P.Symmetric ∧
        (Â ∪ {0}) ⊆ P.toFinset ∧
        ∃ A' ⊆ Â, A'.card ≤ s ∧
          ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ c * s ∧
            ∃ t : Fin ℓ → ℤ,
              ((P.widthScale k).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
              (P.widthScale k).Proper := by
  classical
  -- Packing pushes the ambient exponent to `β' = (10ℓ⁴ + 1)·β` (the packed
  -- range is `n·H^ℓ = n^{10ℓ⁴ + 1}` with `H = n^κ`, `κ = 10ℓ³` a high power
  -- of the box scale); `cfp_main` is applied at that exponent.
  obtain ⟨c, d, hc, hd, hcfp⟩ :=
    cfp_main (β := β * (10 * (ℓ : ℝ) ^ 4 + 1)) (by
      have h10 : (1 : ℝ) ≤ 10 * (ℓ : ℝ) ^ 4 + 1 := by
        have h0 : (0 : ℝ) ≤ (ℓ : ℝ) ^ 4 := pow_nonneg (Nat.cast_nonneg _) 4
        linarith
      exact (hβ).trans_le (le_mul_of_one_le_right (zero_le_one.trans hβ.le) h10)) hη hη1
  refine ⟨c, d + 1, hc, by linarith, ?_⟩
  intro A B s hA hB hAB hBcard hs1 hs2 hlarge
  rcases ℓ.eq_zero_or_pos with hℓ0 | hℓ
  · -- `ℓ = 0`: `Fin 0 → ℤ` is a subsingleton, so `A.card = 1` and the
    -- hypothesis `s ≤ c·1/log 1 = 0` contradicts `1 = 1^η ≤ s`.
    subst hℓ0
    exfalso
    have hAcard : A.card = 1 := by
      obtain ⟨a₀, ha₀⟩ := hA
      rw [Finset.card_eq_one]
      refine ⟨a₀, ?_⟩
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro _
        exact funext fun i ↦ i.elim0
      · rintro rfl
        exact ha₀
    rw [hAcard] at hs1 hs2
    rw [Nat.cast_one, Real.one_rpow] at hs1
    rw [Nat.cast_one, Real.log_one, mul_one, div_zero] at hs2
    -- `hs1 : (1 : ℝ) ≤ s`, `hs2 : (s : ℝ) ≤ 0`
    linarith
  · -- `ℓ ≥ 1`: the Appendix-A base-`H` packing argument of Pham–Zakharov.
    -- The surrounding derivation (anchoring, packing, `cfp_main` numerics,
    -- cardinalities) is complete; the two paper steps that need more than
    -- the width-scaled `cfp_main` output are isolated in the documented
    -- residual lemmas `appendix_decode` and `cfp_unshift`.
    choose lo hi hBi using (show ∀ i, ∃ lo hi, B i = Finset.Icc lo hi from hB)
    obtain ⟨a₀, ha₀⟩ := hA
    have hlohi : ∀ i, lo i ≤ hi i := by
      intro i
      have hai := Fintype.mem_piFinset.mp (hAB ha₀) i
      rw [hBi i, Finset.mem_Icc] at hai
      exact hai.1.trans hai.2
    obtain ⟨B₀, hB₀a, hB₀card, hA₀sub⟩ :=
      GAP.Box.exists_anchored_image_sub hAB (fun i ↦ ⟨hi i, hlohi i, hBi i⟩)
    choose N hN using
      (show ∀ i, ∃ N : ℕ, B₀ i = Finset.Icc 0 (N : ℤ) from hB₀a)
    set A₀ := A.image (· - lo) with hA₀def
    have hA₀ne : A₀.Nonempty := ⟨_, Finset.mem_image.mpr ⟨a₀, ha₀, rfl⟩⟩
    set n := B.card with hndef
    -- `m = |A| ≥ 2`: `m = 1` gives `s ≤ c·1/log 1 = 0`, contradicting `s ≥ 1^η`.
    have hm2 : 2 ≤ A.card := by
      rcases lt_or_ge A.card 2 with h | h
      · have h1 : A.card = 1 := by
          have := Finset.card_pos.mpr ⟨a₀, ha₀⟩; omega
        simp only [h1, Nat.cast_one, Real.log_one, div_zero, Real.one_rpow,
          Nat.cast_zero] at hs1 hs2
        linarith
      · exact h
    have hBn : A.card ≤ n := by
      rw [hndef, ← GAP.Box.card_toFinset B]
      exact Finset.card_le_card hAB
    have hn2 : 2 ≤ n := hm2.trans hBn
    -- side lengths `N i + 1` and coordinate bounds on `A₀ ⊆ B₀ = ∏ [0, Nᵢ]`
    obtain ⟨b₀, hb₀⟩ := hA₀ne
    have hB₀ne : ∀ i, (B₀ i).Nonempty :=
      fun i ↦ ⟨b₀ i, Fintype.mem_piFinset.mp (hA₀sub hb₀) i⟩
    have hNcard : ∀ i, (B₀ i).card = N i + 1 := by
      intro i
      rw [hN i]
      have hcast' : (↑(N i) + 1 - 0 : ℤ) = ((N i + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [Int.card_Icc, hcast', Int.toNat_natCast]
    have hNle : ∀ i, N i ≤ n := by
      intro i
      have hle : (B₀ i).card ≤ B₀.card := by
        show (B₀ i).card ≤ ∏ j, (B₀ j).card
        have h1 : ∀ j ∈ Finset.univ, (1 : ℕ) ≤ (B₀ j).card :=
          fun j _ ↦ Finset.card_pos.mpr (hB₀ne j)
        exact Finset.single_le_prod h1 (Finset.mem_univ i)
      rw [hNcard i, hB₀card] at hle
      omega
    have hA₀bnd : ∀ a ∈ A₀, ∀ j, 0 ≤ a j ∧ a j ≤ (n : ℤ) := by
      intro a ha j
      have haj := Fintype.mem_piFinset.mp (hA₀sub ha) j
      rw [hN j, Finset.mem_Icc] at haj
      exact ⟨haj.1, haj.2.trans (by exact_mod_cast hNle j)⟩
    -- the packing base `H = n^κ`, `κ = 10ℓ³` (Appendix A)
    set κ : ℕ := 10 * ℓ ^ 3 with hκdef
    have hκ2 : 2 ≤ κ := by
      have h1 : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ
      omega
    set H : ℤ := (n : ℤ) ^ κ with hHdef
    have hH2 : 2 ≤ H := by
      rw [hHdef]
      calc (2 : ℤ) ≤ 2 ^ κ := le_self_pow₀ (by norm_num) (by omega)
        _ ≤ (n : ℤ) ^ κ := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hn2) κ
    have hnH : (n : ℤ) < H := by
      rw [hHdef]
      have hnn : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn2
      calc (n : ℤ) < (n : ℤ) * (n : ℤ) :=
            lt_mul_of_one_lt_right (by linarith) (by linarith)
        _ = (n : ℤ) ^ 2 := by rw [pow_two]
        _ ≤ (n : ℤ) ^ κ := pow_le_pow_right₀ (by linarith) hκ2
    -- `ϕ` is injective on the anchored box (sidelengths `Nᵢ ≤ n < H`)
    have hinj : Set.InjOn (packVec (ℓ := ℓ) H) (B₀.toFinset : Set (Fin ℓ → ℤ)) :=
      packVec_injOn_box (H := H) (B := B₀) (lo := fun _ ↦ 0)
        (hi := fun i ↦ (N i : ℤ)) (by linarith) (fun i ↦ hN i) (fun i ↦ by
          simp only [sub_zero]
          exact lt_of_le_of_lt (by exact_mod_cast hNle i) hnH)
    have hϕinj : Set.InjOn (fun a ↦ fun _ : Fin 1 ↦ packVec H a) ↑A₀ :=
      fun a ha b hb hab ↦ hinj (hA₀sub ha) (hA₀sub hb) (congrFun hab 0)
    -- `A₀' = ϕ(A₀) ⊆ [0, n·H^ℓ]`, `|A₀'| = m`
    have hpacknn : ∀ a ∈ A₀, 0 ≤ packVec H a :=
      fun a ha ↦ packVec_nonneg (by linarith) (fun j ↦ (hA₀bnd a ha j).1)
    have hpackle : ∀ a ∈ A₀, packVec H a ≤ (n : ℤ) * H ^ ℓ := by
      intro a ha
      have hbnd := hA₀bnd a ha
      calc packVec H a = ∑ j : Fin ℓ, a j * H ^ j.val := rfl
        _ ≤ ∑ j : Fin ℓ, (n : ℤ) * H ^ j.val :=
            Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_right (hbnd j).2 (pow_nonneg (by linarith) _)
        _ = (n : ℤ) * ∑ j : Fin ℓ, H ^ j.val := by rw [← Finset.mul_sum]
        _ = (n : ℤ) * ∑ j ∈ Finset.range ℓ, H ^ j := by
            rw [Fin.sum_univ_eq_sum_range]
        _ ≤ (n : ℤ) * H ^ ℓ :=
            mul_le_mul_of_nonneg_left (geom_sum_le hH2 ℓ) (by positivity)
    set n₀ : ℕ := n * (n ^ κ) ^ ℓ with hn₀def
    set A₀' := A₀.image (fun a ↦ fun _ : Fin 1 ↦ packVec H a) with hA₀'def
    have hA₀'ne : A₀'.Nonempty := by
      rw [hA₀'def]
      exact ⟨_, Finset.mem_image.mpr ⟨b₀, hb₀, rfl⟩⟩
    have hA₀'card : A₀'.card = A.card := by
      rw [hA₀'def, Finset.card_image_of_injOn hϕinj]
      refine Finset.card_image_of_injective _ (fun a b h ↦ ?_)
      funext i
      have hi := congrFun h i
      simp only [Pi.sub_apply] at hi
      omega
    have hA₀'bnd : ∀ a' ∈ A₀', 0 ≤ a' 0 ∧ a' 0 ≤ (n₀ : ℤ) := by
      intro a' ha'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
      show 0 ≤ packVec H a ∧ packVec H a ≤ (n₀ : ℤ)
      refine ⟨hpacknn a ha, ?_⟩
      calc packVec H a ≤ (n : ℤ) * H ^ ℓ := hpackle a ha
        _ = (n₀ : ℤ) := by rw [hn₀def, hHdef]; push_cast; ring
    -- `n₀ ≤ m^{β₀}` for `β₀ = β·(10ℓ⁴ + 1)`
    have hn₀le : (n₀ : ℝ) ≤ (A₀'.card : ℝ) ^ (β * (10 * (ℓ : ℝ) ^ 4 + 1)) := by
      have hm0 : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
      have hnle : (n : ℝ) ≤ (A.card : ℝ) ^ β := hBcard
      have hexp : (n * (n ^ κ) ^ ℓ : ℕ) = n ^ (10 * ℓ ^ 4 + 1) := by
        rw [← pow_mul, ← pow_succ', hκdef]
        congr 1
        ring
      have hcast : ((10 * ℓ ^ 4 + 1 : ℕ) : ℝ) = 10 * (ℓ : ℝ) ^ 4 + 1 := by
        push_cast
        ring
      have hn₀eq : (n₀ : ℝ) = ((n ^ (10 * ℓ ^ 4 + 1) : ℕ) : ℝ) := by
        rw [hn₀def, hexp]
      rw [hn₀eq, Nat.cast_pow]
      calc (n : ℝ) ^ (10 * ℓ ^ 4 + 1)
          ≤ ((A.card : ℝ) ^ β) ^ (10 * ℓ ^ 4 + 1) :=
            pow_le_pow_left₀ (by positivity) hnle _
        _ = (A.card : ℝ) ^ (β * ((10 * ℓ ^ 4 + 1 : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
        _ = (A₀'.card : ℝ) ^ (β * (10 * (ℓ : ℝ) ^ 4 + 1)) := by
            rw [hA₀'card, hcast]
    -- admissible `s` for `cfp_main`
    have hs1' : (A₀'.card : ℝ) ^ η ≤ (s : ℝ) := by rwa [hA₀'card]
    have hs2' : (s : ℝ) ≤ c * A₀'.card / Real.log A₀'.card := by rwa [hA₀'card]
    obtain ⟨Â₀', d', P₀, hÂ₀'sub, hÂ₀'card, hd'le, hP₀s, hP₀h, hP₀p, hmemP₀,
      A'₀', hA'₀'sub, hA'₀'card, k, hk0, hkle, t₀, hcont₀, hkP₀⟩ :=
      hcfp A₀' n₀ s hA₀'ne hA₀'bnd hn₀le hs1' hs2'
    -- pull back through `ϕ`
    have hÂ₀'sub' : Â₀' ⊆ A₀.image (fun a ↦ fun _ : Fin 1 ↦ packVec H a) := by
      rw [← hA₀'def]
      exact hÂ₀'sub
    obtain ⟨Â₀, hÂ₀sub, hÂ₀im⟩ := Finset.subset_image_iff.mp hÂ₀'sub'
    have hA'₀subA₀ : A'₀' ⊆ A₀.image (fun a ↦ fun _ : Fin 1 ↦ packVec H a) := by
      rw [← hA₀'def]
      exact hA'₀'sub.trans hÂ₀'sub
    obtain ⟨A'₀, hA'₀sub, hA'₀im⟩ := Finset.subset_image_iff.mp hA'₀subA₀
    have hmemÂ₀ : ∀ a ∈ A₀, (fun _ : Fin 1 ↦ packVec H a) ∈ Â₀' → a ∈ Â₀ := by
      intro a ha hϕa
      rw [← hÂ₀im] at hϕa
      obtain ⟨b, hb, hϕb⟩ := Finset.mem_image.mp hϕa
      have hba : b = a := hϕinj (hÂ₀sub hb) ha hϕb
      exact hba ▸ hb
    have hA'₀subÂ₀ : A'₀ ⊆ Â₀ := by
      intro a ha
      have hmem : (fun _ : Fin 1 ↦ packVec H a) ∈ A'₀' :=
        hA'₀im ▸ Finset.mem_image.mpr ⟨a, ha, rfl⟩
      exact hmemÂ₀ a (hA'₀sub ha) (hA'₀'sub hmem)
    have hÂ₀card : Â₀.card = Â₀'.card := by
      rw [← hÂ₀im]
      exact (Finset.card_image_of_injOn
        (hϕinj.mono (Finset.coe_subset.mpr hÂ₀sub))).symm
    have hA'₀card : A'₀.card = A'₀'.card := by
      rw [← hA'₀im]
      exact (Finset.card_image_of_injOn
        (hϕinj.mono (Finset.coe_subset.mpr hA'₀sub))).symm
    have hsub : ∀ a ∈ Â₀, (fun _ : Fin 1 ↦ packVec H a) ∈ P₀.toFinset := by
      intro a ha
      exact hmemP₀ (Finset.mem_union.mpr (Or.inl
        (hÂ₀im ▸ Finset.mem_image.mpr ⟨a, ha, rfl⟩)))
    have h0 : (0 : Fin 1 → ℤ) ∈ P₀.toFinset :=
      hmemP₀ (Finset.mem_union.mpr (Or.inr
        (Finset.mem_singleton_self (0 : Fin 1 → ℤ))))
    have hcontP₀ : ((P₀.widthScale k).translate t₀).toFinset ⊆
        subsetSumsL (A'₀.image fun x ↦ fun _ : Fin 1 ↦ packVec H x) := by
      rw [← hA'₀im] at hcont₀
      exact hcont₀
    -- the Appendix-A domination `H > ns²(sn)^ℓ`: with the largeness
    -- hypothesis `hlarge` (`m` above the explicit threshold `N₀(c,ℓ)`)
    -- it follows from `H = n^{10ℓ³}`, `s ≤ c·m/log m ≤ (c/log 2)·n`,
    -- `k ≤ c·s` and `m ≤ n`: every factor is a constant times a power of
    -- `n`, so `LHS ≤ N₀·n^{4ℓ+3}`, and `10ℓ³ ≥ 4ℓ+4` lets `n > N₀`
    -- absorb the constant.
    have hdom : (8 : ℤ) * ((k : ℤ) + 1) * ((s : ℤ) + 1) * ((n : ℤ) + 1) *
        (2 * (s : ℤ) * (n : ℤ) + 1) ^ (2 * ℓ) < H := by
      have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hmR : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hm2
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
      have hlogm : Real.log 2 ≤ Real.log (A.card : ℝ) :=
        Real.log_le_log (by norm_num) hmR
      have hc2nn : (0 : ℝ) ≤ c / Real.log 2 := (div_pos hc hL2).le
      -- `s ≤ (c / log 2) · n` from `s ≤ c·m / log m`, `log 2 ≤ log m`, `m ≤ n`
      have hsR : (s : ℝ) ≤ (c / Real.log 2) * (n : ℝ) := by
        calc (s : ℝ) ≤ c * (A.card : ℝ) / Real.log (A.card : ℝ) := hs2
          _ ≤ c * (A.card : ℝ) / Real.log 2 :=
              div_le_div_of_nonneg_left (mul_nonneg hc.le (by positivity)) hL2 hlogm
          _ ≤ c * (n : ℝ) / Real.log 2 :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by exact_mod_cast hBn) hc.le) hL2.le
          _ = (c / Real.log 2) * (n : ℝ) := by ring
      -- factor bounds, each a constant times a power of `n`
      have hF1 : (k : ℝ) + 1 ≤ (c + 1) * (c / Real.log 2 + 1) * (n : ℝ) := by
        have hks : (k : ℝ) ≤ c * ((c / Real.log 2) * (n : ℝ)) :=
          hkle.trans (mul_le_mul_of_nonneg_left hsR hc.le)
        nlinarith [hks, hn1, mul_nonneg hc.le hnR0.le, mul_nonneg hc2nn hnR0.le]
      have hF2 : (s : ℝ) + 1 ≤ (c / Real.log 2 + 1) * (n : ℝ) := by
        nlinarith [hsR, hn1]
      have hF3 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
      have hF4 : 2 * (s : ℝ) * (n : ℝ) + 1 ≤
          (2 * (c / Real.log 2) + 1) * (n : ℝ) ^ 2 := by
        have hsn : (s : ℝ) * (n : ℝ) ≤ (c / Real.log 2) * (n : ℝ) ^ 2 := by
          have h := mul_le_mul_of_nonneg_right hsR hnR0.le
          calc (s : ℝ) * (n : ℝ) ≤ (c / Real.log 2) * (n : ℝ) * (n : ℝ) := h
            _ = (c / Real.log 2) * (n : ℝ) ^ 2 := by ring
        have hn2' : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
        have h2sn : 2 * (s : ℝ) * (n : ℝ) ≤
            2 * ((c / Real.log 2) * (n : ℝ) ^ 2) := by linarith [hsn]
        calc 2 * (s : ℝ) * (n : ℝ) + 1
            ≤ 2 * ((c / Real.log 2) * (n : ℝ) ^ 2) + (n : ℝ) ^ 2 := by
              linarith [h2sn, hn2']
          _ = (2 * (c / Real.log 2) + 1) * (n : ℝ) ^ 2 := by ring
      have hF5 : (2 * (s : ℝ) * (n : ℝ) + 1) ^ (2 * ℓ) ≤
          ((2 * (c / Real.log 2) + 1) * (n : ℝ) ^ 2) ^ (2 * ℓ) :=
        pow_le_pow_left₀ (by positivity) hF4 _
      have hmul : (8 : ℝ) * ((k : ℝ) + 1) * ((s : ℝ) + 1) * ((n : ℝ) + 1) *
          (2 * (s : ℝ) * (n : ℝ) + 1) ^ (2 * ℓ) ≤
          (8 : ℝ) * ((c + 1) * (c / Real.log 2 + 1) * (n : ℝ)) *
            ((c / Real.log 2 + 1) * (n : ℝ)) * (2 * (n : ℝ)) *
            ((2 * (c / Real.log 2) + 1) * (n : ℝ) ^ 2) ^ (2 * ℓ) :=
        mul_le_mul
          (mul_le_mul
            (mul_le_mul
              (mul_le_mul (le_refl (8 : ℝ)) hF1 (by positivity) (by positivity))
              hF2 (by positivity) (by positivity))
            hF3 (by positivity) (by positivity))
          hF5 (by positivity) (by positivity)
      have hpow : ((2 * (c / Real.log 2) + 1) * (n : ℝ) ^ 2) ^ (2 * ℓ) =
          (2 * (c / Real.log 2) + 1) ^ (2 * ℓ) * (n : ℝ) ^ (4 * ℓ) := by
        rw [mul_pow, ← pow_mul, show 2 * (2 * ℓ) = 4 * ℓ from by ring]
      have hC₀ltn : 16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
          (2 * (c / Real.log 2) + 1) ^ (2 * ℓ) < (n : ℝ) :=
        lt_of_lt_of_le hlarge (by exact_mod_cast hBn)
      have hExp : 4 * ℓ + 3 + 1 ≤ κ := by
        have hℓ3 : ℓ ≤ ℓ ^ 3 := le_self_pow₀ (by omega) (by norm_num)
        rw [hκdef]
        omega
      have key : (8 : ℝ) * ((k : ℝ) + 1) * ((s : ℝ) + 1) * ((n : ℝ) + 1) *
          (2 * (s : ℝ) * (n : ℝ) + 1) ^ (2 * ℓ) < (n : ℝ) ^ κ := by
        calc (8 : ℝ) * ((k : ℝ) + 1) * ((s : ℝ) + 1) * ((n : ℝ) + 1) *
            (2 * (s : ℝ) * (n : ℝ) + 1) ^ (2 * ℓ)
            ≤ (8 : ℝ) * ((c + 1) * (c / Real.log 2 + 1) * (n : ℝ)) *
              ((c / Real.log 2 + 1) * (n : ℝ)) * (2 * (n : ℝ)) *
              ((2 * (c / Real.log 2) + 1) * (n : ℝ) ^ 2) ^ (2 * ℓ) := hmul
          _ = (16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
              (2 * (c / Real.log 2) + 1) ^ (2 * ℓ)) * (n : ℝ) ^ (4 * ℓ + 3) := by
            rw [hpow, pow_add]
            ring
          _ < (n : ℝ) ^ κ := by
            calc (16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
                (2 * (c / Real.log 2) + 1) ^ (2 * ℓ)) * (n : ℝ) ^ (4 * ℓ + 3)
                < (n : ℝ) * (n : ℝ) ^ (4 * ℓ + 3) :=
                  mul_lt_mul_of_pos_right hC₀ltn (pow_pos hnR0 _)
              _ = (n : ℝ) ^ (4 * ℓ + 3 + 1) := by rw [← pow_succ']
              _ ≤ (n : ℝ) ^ κ := pow_le_pow_right₀ hn1 hExp
      rw [hHdef]
      exact_mod_cast key
    obtain ⟨P, hPs, hPmem0, tdig, hcontP, hkP⟩ :=
      appendix_decode hℓ (by linarith)
        (fun a ha j ↦ hA₀bnd a (hÂ₀sub ha) j)
        (fun a ha j ↦ hA₀bnd a (hA'₀sub ha) j)
        (by rw [hA'₀card]; exact_mod_cast hA'₀'card)
        hP₀p hP₀s hsub h0 hk0 hcontP₀ hdom
    obtain ⟨P', hP's, hP'mem, t', hcont', hkP'⟩ :=
      cfp_unshift (P := P) (lo := lo) (k := k) (Â₀ := Â₀) (A'₀ := A'₀)
        (tdig := tdig) hPmem0 hPs hcontP hkP
    refine ⟨Â₀.image (· + lo), d' + 1, P', ?_, ?_, ?_, hP's, hP'mem,
      A'₀.image (· + lo), ?_, ?_, k, hk0, hkle, t', hcont', hkP'⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp (hÂ₀sub ha)
      simpa using ha'
    · have hcard : (Â₀.image (· + lo)).card = Â₀.card := by
        refine Finset.card_image_of_injective _ (fun a b h ↦ ?_)
        funext i
        have hi := congrFun h i
        simp only [Pi.add_apply] at hi
        omega
      rw [hcard, hÂ₀card]
      rwa [hA₀'card] at hÂ₀'card
    · push_cast
      linarith [hd'le]
    · exact Finset.image_subset_image hA'₀subÂ₀
    · have hcard : (A'₀.image (· + lo)).card = A'₀.card := by
        refine Finset.card_image_of_injective _ (fun a b h ↦ ?_)
        funext i
        have hi := congrFun h i
        simp only [Pi.add_apply] at hi
        omega
      rw [hcard, hA'₀card]
      exact hA'₀'card

/-- **Corollary 5**: Theorem 3 at `s = ⌊m / log² m⌋`; `P` may be taken
symmetric and `csP` proper.  Requires `m ≥ C` so that `s` lies in the
admissible range `[m^{1/2}, c·m/log m]` of Theorem 3 and the largeness
threshold `N₀(c,ℓ)` is met. -/
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
              ((P.widthScale k).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
              (P.widthScale k).Proper := by
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
  -- enlarge `C` so the largeness hypothesis of `cfp_structure` holds
  have hC₀pos : (0 : ℝ) < 16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
      (2 * (c / Real.log 2) + 1) ^ (2 * ℓ) + 1 := by
    have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨c, d, max C₁ (16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
      (2 * (c / Real.log 2) + 1) ^ (2 * ℓ) + 1), hc, hd,
    lt_of_lt_of_le hC₀pos (le_max_right _ _), fun A B hBint hsub hB hCm ↦ ?_⟩
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
  have hlarge : 16 * (c + 1) * (c / Real.log 2 + 1) ^ 2 *
      (2 * (c / Real.log 2) + 1) ^ (2 * ℓ) < (A.card : ℝ) :=
    lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one)
      (le_trans (le_max_right _ _) hCm)
  obtain ⟨Â, d', P, hÂsub, hÂcard, hd'le, hSym, hsub0,
    A', hA'sub, hA'card, k, hkpos, hkle, t, htrans, hprop⟩ :=
    hcfp A B s hAne hBint hsub hB hs_ge hs_le2 hlarge
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
