import Nonaveraging.Structure

/-!
# A faithful restatement of Lemma 10 (`irreduciblization`)

`Structure.irreduciblization` is currently **vacuous**: the witness constant
`ct` is existentially quantified *per* `A`, so its proof chooses
`ct = (log |A|)⁻¹`, making the `|Â|` lower bound
`|A| − ct⁻¹·|A|/log|A| = 0` degenerate; `SubSumWitness.degenerate`
(`Â = ∅`, `0`-dimensional singleton GAP) then satisfies `Irreducible`
vacuously, since `ϕ_P(∅) = ∅` has no subset of size `≥ δ·|A|`.

This file kills that escape and builds the honest scaffolding of Lemma 10
(arXiv:2410.14624v2, §3.2):

* **Non-degeneracy of fixed-constant witnesses**
  (`SubSumWitness.half_le_Ah_card`, `SubSumWitness.one_le_dim`,
  `exists_forall_dim_pos`, `faithful_witness_genuine`): for a *fixed*
  `c > 0`, every `SubSumWitness` on a large set satisfies
  `|Â| ≥ |A|/2` and `d ≥ 1`.  The `0`-dimensional degenerate witness is
  impossible once `|A|` exceeds an explicit threshold in `c`.
* **The zeroth move** (`DerivedFrom.imageAh_step`, `exists_first_move`):
  `Ã := ϕ_P(Â)` for the canonical witness `W` is `DerivedFrom A δ`
  (take `x = 0`), non-averaging, and `|Ã| ≥ |A|(1 − (c·log|A|)⁻¹)`.
* **The symmetric ambient box** (`GAP.symmCoeffBox`): `ϕ_P(P) − x ⊆
  ∏ᵢ [−wᵢ, wᵢ]` for `x ∈ ϕ_P(P)` — the symmetric box that Lemma 8 of the
  paper applies to, plus interval-box bookkeeping
  (`GAP.Box.IsInterval.translate`, `DerivedFrom.exists_interval_box`).
* **Counting form of Lemma 8** (`subsetSumsL_card_le_symmetric_box`,
  `SubSumWitness.card_P_le_dilate`, `SubSumWitness.card_P_le_s_pow`,
  `SubSumWitness.card_P'_le_of_imageAh_sub_witness`): every subset sum of
  `A' ⊆ B` (B symmetric) lies in the `|A'|`-fold dilate of `B`, hence
  `|P| ≤ |Σ(A')| ≤ (2|A'|+1)^ℓ·|B| ≤ (2·s(A)+1)^ℓ·|B|`.  This is the
  elementary counting bound; the paper's Lemma 8 sharpens it to `≪_d |B|`
  (removing the `s(A)^ℓ` factor) via the discrete John lemma and covolume
  arguments that are not yet in the formalization.
* **The down/up/shrink trichotomy** (`DerivedFrom.step_cases`): failure of
  `(δ,γ)`-irreducibility at the minimal-dimension witness produces a move
  with `d₁ < d` (down), `d₁ > d` (up), or `d₁ = d` with
  `|P₁| < γ·|P|` (shrink) — the equation-(8) bookkeeping input.
* **`irreduciblization_faithful`**: the faithful statement — `c₀`, `c'` are
  *universal constants* (quantified outside `∀ A`, as supplied by
  `cfp_structure_cor`/`subSumDim_exists`), `dt ≤ D` is recorded, and `Wt`'s
  `hAhcard` field reads `|At| − c₀⁻¹·|At|/log|At| ≤ |Ât|` with `c₀`
  independent of `A`.  The proof is a gap: it needs Lemmas 6/8
  (`|P(A)| ≪_d |P|`, `|P|·s(A)^{−(d₁−d)}` bounds) plus the paper's
  equation-(8)/(9)/(10) termination bookkeeping.
-/

open Finset

namespace Nonaveraging

/-- Shifting by `0` is the identity on finsets of integer vectors. -/
theorem image_sub_zero {n : ℕ} (s : Finset (Fin n → ℤ)) :
    s.image (· - (0 : Fin n → ℤ)) = s := by
  simp

/-! ### Size thresholds -/

/-- For `N = ⌈max 4 (exp t)⌉`, any `A` with `|A| ≥ N` satisfies
`4 ≤ |A|` and `t ≤ log|A|`. -/
theorem exists_card_ge_exp (t : ℝ) :
    ∃ N : ℕ, ∀ {n : ℕ} {A : Finset (Fin n → ℤ)}, N ≤ A.card →
      (4 : ℝ) ≤ (A.card : ℝ) ∧ t ≤ Real.log (A.card : ℝ) := by
  refine ⟨⌈max 4 (Real.exp t)⌉₊, fun {n} {A} hN ↦ ?_⟩
  have hN' : (max 4 (Real.exp t) : ℝ) ≤ (A.card : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h2 : (4 : ℝ) ≤ (A.card : ℝ) := (le_max_left _ _).trans hN'
  have hpos : (0 : ℝ) < (A.card : ℝ) := by linarith
  exact ⟨h2,
    (Real.le_log_iff_exp_le hpos).mpr ((le_max_right _ _).trans hN')⟩

namespace SubSumWitness

variable {m d : ℕ} {c : ℝ} {A : Finset (Fin m → ℤ)} (W : SubSumWitness A c d)

/-- `|Â| ≥ |A|·(1 − (c·log|A|)⁻¹)` — restating `hAhcard` multiplicatively:
a fixed-constant witness captures a `1 − o(1)` fraction of `A`. -/
theorem one_sub_inv_mul_le_Ah_card :
    (A.card : ℝ) * (1 - (c * Real.log (A.card : ℝ))⁻¹) ≤
      (W.Ah.card : ℝ) := by
  have h := W.hAhcard
  have e : c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ)
      = (A.card : ℝ) * (c * Real.log (A.card : ℝ))⁻¹ := by
    rw [mul_inv, div_eq_mul_inv]
    ring
  rw [e] at h
  rw [mul_sub, mul_one]
  linarith

/-- Once `log|A| ≥ 2c⁻¹`, a witness captures at least half of `A`. -/
theorem half_le_Ah_card (hA : (0 : ℝ) < (A.card : ℝ))
    (hlog : 2 * c⁻¹ ≤ Real.log (A.card : ℝ)) :
    (A.card : ℝ) / 2 ≤ (W.Ah.card : ℝ) := by
  have hcc : (0 : ℝ) < c⁻¹ := inv_pos.mpr W.cpos
  have hlp : (0 : ℝ) < Real.log (A.card : ℝ) := by linarith
  have hsub : c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ)
      ≤ (A.card : ℝ) / 2 := by
    rw [div_le_iff₀ hlp]
    have hc2 : c⁻¹ ≤ Real.log (A.card : ℝ) / 2 := by linarith
    calc c⁻¹ * (A.card : ℝ)
        ≤ (Real.log (A.card : ℝ) / 2) * (A.card : ℝ) :=
          mul_le_mul_of_nonneg_right hc2 hA.le
      _ = (A.card : ℝ) / 2 * Real.log (A.card : ℝ) := by ring
  have := W.hAhcard
  linarith

/-- A witness on a set with `|A| − c⁻¹·|A|/log|A| > 1` has positive
dimension: the `0`-dimensional degenerate case `|Â| ≤ 1` is excluded. -/
theorem one_le_dim {d' : ℕ} (W' : SubSumWitness A c d')
    (h : (1 : ℝ) < (A.card : ℝ)
      - c⁻¹ * (A.card : ℝ) / Real.log (A.card : ℝ)) : 1 ≤ d' := by
  rcases Nat.eq_zero_or_pos d' with rfl | hd
  · exfalso
    exact W'.not_dim_zero_of_one_lt h
  · exact hd

/-- `∏ᵢ wᵢ ≤ |Σ(A')|`: the only size control `SubSumWitness` supplies —
the proper `kP + t ⊆ Σ(A')` has `∏ᵢ wᵢ` points. -/
theorem prod_width_le_card_subsetSums :
    ∏ i, W.P.width i ≤ (GAP.subsetSumsL W.A').card := by
  have hcard : ((W.k • W.P).translate W.t).toFinset.card
      = ∏ i, W.P.width i := by
    rw [GAP.card_toFinset_translate, GAP.card_toFinset_of_proper _ W.hproper]
    exact Finset.prod_congr rfl fun i _ ↦ rfl
  rw [← hcard]
  exact Finset.card_le_card W.htranslate

/-- `0 ∈ ϕ_P(P)`: the coefficient box contains the zero vector since `P`
is nonempty and each width is positive.  (Extracted from the proof of
`embedded_in_mu_convex_position`.) -/
theorem zero_mem_imageP : (0 : Fin d → ℤ) ∈ W.imageP := by
  have hproper : W.P.Proper :=
    (GAP.proper_smul_iff (by exact_mod_cast W.kpos.ne')).mp W.hproper
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

/-- The shifted embedded image is non-averaging (translate of the injective
coefficient image of `Â ⊆ A`). -/
theorem nonAveraging_imageAh_sub (hA : NonAveraging A) (x : Fin d → ℤ) :
    NonAveraging (W.imageAh.image (· - x)) := by
  have hAhNA : NonAveraging W.Ah := NonAveraging.mono W.hAh hA
  have himNA : NonAveraging W.imageAh :=
    W.P.nonAveraging_ptCoeffImage W.hAhP hAhNA
  simpa [sub_eq_add_neg] using himNA.translate (-x)

end SubSumWitness

/-- With a *fixed* constant `c`, every structure witness on a large enough
set is genuine: `d ≥ 1` and `|Â| ≥ |A|/2`.  The `0`-dimensional
`SubSumWitness.degenerate` used by the vacuous `irreduciblization` proof
cannot occur once `|A| ≥ max 4 (exp (2c⁻¹))`. -/
theorem exists_forall_dim_pos {c : ℝ} (_hc : 0 < c) :
    ∃ N : ℕ, ∀ {d m : ℕ} {A : Finset (Fin m → ℤ)}
      (W : SubSumWitness A c d), N ≤ A.card →
      1 ≤ d ∧ (A.card : ℝ) / 2 ≤ (W.Ah.card : ℝ) := by
  obtain ⟨N, hN⟩ := exists_card_ge_exp (2 * c⁻¹)
  refine ⟨N, fun {d} {m} {A} W hNA ↦ ?_⟩
  obtain ⟨h2, hlog⟩ := hN hNA
  have hApos : (0 : ℝ) < (A.card : ℝ) := by linarith
  have hhalf := W.half_le_Ah_card hApos hlog
  refine ⟨?_, hhalf⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    have h1 : (W.Ah.card : ℝ) ≤ 1 := by exact_mod_cast W.card_Ah_le_one
    linarith
  · exact hd

/-! ### The symmetric coefficient box -/

namespace GAP

variable {n d : ℕ} (P : GAP n d)

/-- The symmetric coefficient box `∏ᵢ [−wᵢ, wᵢ] ⊆ ℤ^d` — the ambient
symmetric box of `ϕ_P(P) − x` in Definition 9 and Lemma 8. -/
def symmCoeffBox : GAP.Box d :=
  fun i ↦ Finset.Icc (-(P.width i : ℤ)) (P.width i)

theorem symmCoeffBox_symmetric : P.symmCoeffBox.Symmetric :=
  fun i ↦ ⟨P.width i, rfl⟩

theorem symmCoeffBox_isInterval : P.symmCoeffBox.IsInterval :=
  P.symmCoeffBox_symmetric.isInterval

theorem mem_symmCoeffBox {x : Fin d → ℤ} :
    x ∈ P.symmCoeffBox.toFinset ↔ ∀ i, |x i| ≤ (P.width i : ℤ) := by
  simp only [GAP.Box.mem_toFinset, symmCoeffBox, Finset.mem_Icc]
  exact forall_congr' fun i ↦ abs_le.symm

theorem symmCoeffBox_card :
    P.symmCoeffBox.card = ∏ i, (2 * P.width i + 1) := by
  show ∏ i, (Finset.Icc (-(P.width i : ℤ)) (P.width i)).card = _
  apply Finset.prod_congr rfl
  intro i _
  rw [Int.card_Icc]
  have e : ((P.width i : ℤ) + 1 - (-(P.width i : ℤ)))
      = ((2 * P.width i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.toNat_natCast]

/-- `∏ᵢ(2wᵢ+1) ≤ 3^d·∏ᵢwᵢ` when all widths are positive. -/
theorem symmCoeffBox_card_le (hw : ∀ i, 1 ≤ P.width i) :
    P.symmCoeffBox.card ≤ 3 ^ d * ∏ i, P.width i := by
  rw [symmCoeffBox_card]
  calc ∏ i, (2 * P.width i + 1)
      ≤ ∏ i, (3 * P.width i) :=
        Finset.prod_le_prod fun i _ ↦ by have := hw i; omega
    _ = 3 ^ d * ∏ i, P.width i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- `ϕ_P(P) − x ⊆ ∏ᵢ[−wᵢ, wᵢ]` for `x ∈ ϕ_P(P)` — the shifted coefficient
image always lands in the symmetric coefficient box. -/
theorem imageP_sub_subset_symmCoeffBox {x : Fin d → ℤ}
    (hx : x ∈ P.ptCoeffImage P.toFinset (Subset.refl _)) :
    (P.ptCoeffImage P.toFinset (Subset.refl _)).image (· - x) ⊆
      P.symmCoeffBox.toFinset := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_symmCoeffBox]
  intro i
  have hzB := P.ptCoeffImage_subset_coeffBox _ _ hz
  have hxB := P.ptCoeffImage_subset_coeffBox _ _ hx
  rw [GAP.Box.mem_toFinset] at hzB hxB
  have hz' : z i ∈ Finset.Ico (0 : ℤ) (P.width i) := hzB i
  have hx' : x i ∈ Finset.Ico (0 : ℤ) (P.width i) := hxB i
  rw [Finset.mem_Ico] at hz' hx'
  rw [Pi.sub_apply, abs_le]
  constructor <;> omega

end GAP

namespace SubSumWitness

variable {m d : ℕ} {c : ℝ} {A : Finset (Fin m → ℤ)} (W : SubSumWitness A c d)

/-- `ϕ_P(Â) − x ⊆ ∏ᵢ[−wᵢ, wᵢ]` for `x ∈ ϕ_P(P)`. -/
theorem imageAh_sub_subset_symmCoeffBox (x : Fin d → ℤ) (hx : x ∈ W.imageP) :
    W.imageAh.image (· - x) ⊆ W.P.symmCoeffBox.toFinset :=
  (Finset.image_subset_image W.imageAh_subset_imageP).trans
    (GAP.imageP_sub_subset_symmCoeffBox W.P hx)

/-- Every `x ∈ ϕ_P(P)` forces all widths of `P` to be positive. -/
theorem one_le_width_of_mem_imageP {x : Fin d → ℤ} (hx : x ∈ W.imageP)
    (i : Fin d) : 1 ≤ W.P.width i := by
  have hxB := W.imageP_subset_coeffBox hx
  rw [GAP.Box.mem_toFinset] at hxB
  have hi : x i ∈ Finset.Ico (0 : ℤ) (W.P.width i) := hxB i
  rw [Finset.mem_Ico] at hi
  have hpos : (0 : ℤ) < (W.P.width i : ℤ) := lt_of_le_of_lt hi.1 hi.2
  exact_mod_cast hpos

end SubSumWitness

/-! ### Interval-box bookkeeping for the moves -/

namespace GAP.Box

/-- A coordinatewise translate of an interval box is an interval box. -/
theorem IsInterval.translate {n : ℕ} {B : GAP.Box n} (hB : B.IsInterval)
    (t : Fin n → ℤ) : (B.translate t).IsInterval := by
  intro i
  obtain ⟨lo, hi, h⟩ := hB i
  refine ⟨lo + t i, hi + t i, ?_⟩
  show (B i).image (· + t i) = Finset.Icc (lo + t i) (hi + t i)
  rw [h, Finset.image_add_right_Icc]

/-- The translated coefficient box `∏ᵢ[0,wᵢ) + t` is the interval box
`∏ᵢ[tᵢ, wᵢ+tᵢ−1]`. -/
theorem coeffBox_translate_isInterval {n d : ℕ} (P : GAP n d)
    (t : Fin d → ℤ) : (P.coeffBox.translate t).IsInterval := by
  intro i
  refine ⟨t i, (P.width i : ℤ) + t i - 1, ?_⟩
  show (Finset.Ico (0 : ℤ) (P.width i)).image (· + t i)
      = Finset.Icc (t i) ((P.width i : ℤ) + t i - 1)
  rw [Finset.image_add_right_Ico, ← Finset.Icc_sub_one_right_eq_Ico]
  simp

end GAP.Box

variable {ℓ : ℕ}

/-- Upgrade of `DerivedFrom.exists_box`: every derived set is contained in
an *interval* box of size `≤ 2^{|A|} + |B_A|` (the crude bound; the paper's
`|A|^{O(1)}` bound needs Lemmas 6–8). -/
theorem DerivedFrom.exists_interval_box {A : Finset (Fin ℓ → ℤ)} {δ : ℝ}
    (BA : GAP.Box ℓ) (hBAi : BA.IsInterval) (hBA : A ⊆ BA.toFinset) {n : ℕ}
    {B : Finset (Fin n → ℤ)} (h : DerivedFrom A δ B) :
    ∃ B' : GAP.Box n, B'.IsInterval ∧ B ⊆ B'.toFinset ∧
      (B'.card : ℝ) ≤ (2 : ℝ) ^ A.card + (BA.card : ℝ) := by
  induction h with
  | refl =>
    exact ⟨BA, hBAi, hBA,
      le_add_of_nonneg_left (pow_nonneg (by norm_num) _)⟩
  | step hder W _ x _ hC _ _ =>
    refine ⟨W.P.coeffBox.translate (-x),
      GAP.Box.coeffBox_translate_isInterval _ _,
      hC.trans (W.imageAh_sub_subset_coeffBox_translate x), ?_⟩
    rw [GAP.Box.card_translate, GAP.coeffBox_card]
    have hA'le : W.A'.card ≤ A.card :=
      (Finset.card_le_card (W.hA'.trans W.hAh)).trans hder.card_le
    have hw : ((∏ i, W.P.width i : ℕ) : ℝ) ≤ (2 : ℝ) ^ W.A'.card := by
      exact_mod_cast W.prod_width_le_two_pow_card_A'
    calc ((∏ i, W.P.width i : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ W.A'.card := hw
      _ ≤ (2 : ℝ) ^ A.card := pow_le_pow_right₀ (by norm_num) hA'le
      _ ≤ (2 : ℝ) ^ A.card + (BA.card : ℝ) :=
          le_add_of_nonneg_right (Nat.cast_nonneg _)

/-! ### Counting bounds for `|P|` (elementary half of Lemma 8) -/

/-- Every subset sum of `A' ⊆ B`, `B` a symmetric box `∏ᵢ[−Nᵢ,Nᵢ]`, lies in
the `|A'|`-fold dilate `∏ᵢ[−|A'|Nᵢ, |A'|Nᵢ]`; hence
`|Σ(A')| ≤ (2|A'|+1)^m·|B|`. -/
theorem subsetSumsL_card_le_symmetric_box {m : ℕ}
    {A' : Finset (Fin m → ℤ)} {B : GAP.Box m} (hB : B.Symmetric)
    (hsub : A' ⊆ B.toFinset) :
    (GAP.subsetSumsL A').card ≤ (2 * A'.card + 1) ^ m * B.card := by
  classical
  choose N hN using hB
  set s := A'.card with hs
  let D : GAP.Box m :=
    fun i ↦ Finset.Icc (-((s : ℤ) * (N i : ℤ))) ((s : ℤ) * (N i : ℤ))
  have hDi : ∀ i, D i =
      Finset.Icc (-((s : ℤ) * (N i : ℤ))) ((s : ℤ) * (N i : ℤ)) :=
    fun _ ↦ rfl
  have hsub' : GAP.subsetSumsL A' ⊆ D.toFinset := by
    intro x hx
    rw [GAP.mem_subsetSumsL] at hx
    obtain ⟨S, hS, rfl⟩ := hx
    rw [GAP.Box.mem_toFinset]
    intro i
    rw [hDi i]
    have hcoord : |∑ a ∈ S, a i| ≤ (s : ℤ) * (N i : ℤ) := by
      have hNnn : (0 : ℤ) ≤ (N i : ℤ) := Nat.cast_nonneg _
      calc |∑ a ∈ S, a i|
          ≤ ∑ a ∈ S, |a i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ S, (N i : ℤ) :=
            Finset.sum_le_sum fun a ha ↦ by
              have haB := hsub (hS ha)
              rw [GAP.Box.mem_toFinset] at haB
              have hai : a i ∈ Finset.Icc (-(N i : ℤ)) (N i : ℤ) := by
                rw [← hN i]
                exact haB i
              rw [Finset.mem_Icc] at hai
              rw [abs_le]
              exact hai
        _ = (S.card : ℤ) * (N i : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (s : ℤ) * (N i : ℤ) :=
            mul_le_mul_of_nonneg_right
              (by exact_mod_cast Finset.card_le_card hS) hNnn
    have hid : (S.sum id) i = ∑ a ∈ S, a i := by
      simp only [Finset.sum_apply, id_eq]
    show (S.sum id) i ∈ Finset.Icc (-((s : ℤ) * (N i : ℤ)))
        ((s : ℤ) * (N i : ℤ))
    rw [Finset.mem_Icc, hid]
    exact abs_le.mp hcoord
  have hcardB : B.card = ∏ i, (2 * N i + 1) := by
    show ∏ i, (B i).card = _
    apply Finset.prod_congr rfl
    intro i _
    rw [hN i, Int.card_Icc]
    have e : ((N i : ℤ) + 1 - (-(N i : ℤ)))
        = ((2 * N i + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e, Int.toNat_natCast]
  calc (GAP.subsetSumsL A').card
      ≤ D.toFinset.card := Finset.card_le_card hsub'
    _ = ∏ i, (2 * s * N i + 1) := by
        rw [GAP.Box.card_toFinset]
        apply Finset.prod_congr rfl
        intro i _
        rw [hDi i, Int.card_Icc]
        have e : ((s : ℤ) * (N i : ℤ) + 1 - (-((s : ℤ) * (N i : ℤ))))
            = ((2 * s * N i + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e, Int.toNat_natCast]
    _ ≤ ∏ i, ((2 * s + 1) * (2 * N i + 1)) := by
        apply Finset.prod_le_prod
        intro i _
        rw [show (2 * s + 1) * (2 * N i + 1)
            = (2 * s * N i + 1) + (2 * s * N i + 2 * s + 2 * N i) by ring]
        exact Nat.le_add_right _ _
    _ = (2 * s + 1) ^ m * ∏ i, (2 * N i + 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
    _ = (2 * A'.card + 1) ^ m * B.card := by rw [hcardB]

/-- **Interval-box form of the subset-sum counting bound** (no symmetry
needed): for `A' ⊆ B`, `B` an interval box `∏ᵢ[loᵢ,hiᵢ]` with nonempty
sides, the `i`-th coordinate of a subset sum `Σ_{a∈S} a`, `|S| = k ≤ s`,
lies in `[k·loᵢ, k·hiᵢ]`, so `|Σ(A')| ≤ ∏ᵢ (s+1)·(s·|Bᵢ|+1)
≤ (s+1)^{2m}·|B|`.  Unlike `subsetSumsL_card_le_symmetric_box` this
applies to the *non-symmetric* ambient box `B` of an `(ℓ,β)`-set —
supplying a *polynomial* bound `|Σ(A')| ≤ (s+1)^{2ℓ}|B|` where the
trivial bound `|Σ(A')| ≤ 2^{|A'|}` is exponential. -/
theorem subsetSumsL_card_le_interval_box {m : ℕ}
    {A' : Finset (Fin m → ℤ)} {B : GAP.Box m} (hB : B.IsInterval)
    (hne : ∀ i, (B i).Nonempty) (hsub : A' ⊆ B.toFinset) :
    (GAP.subsetSumsL A').card ≤ (A'.card + 1) ^ (2 * m) * B.card := by
  classical
  choose lo hi hBi using hB
  set s := A'.card with hs
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    obtain ⟨b, hb⟩ := hne i
    rw [hBi i] at hb
    exact (Finset.mem_Icc.mp hb).1.trans (Finset.mem_Icc.mp hb).2
  have hBi_card : ∀ i, ((B i).card : ℤ) = hi i - lo i + 1 := by
    intro i
    rw [hBi i, Int.card_Icc,
      show hi i + 1 - lo i = hi i - lo i + 1 by ring]
    exact Int.toNat_of_nonneg
      (show (0 : ℤ) ≤ hi i - lo i + 1 by have := hlohi i; omega)
  -- Per-coordinate landing zone:
  -- `Uᵢ = ⋃_{k ≤ s} [k·loᵢ, k·hiᵢ]`.
  set U : Fin m → Finset ℤ := fun i ↦
    (Finset.range (s + 1)).biUnion
      fun k ↦ Finset.Icc ((k : ℤ) * lo i) ((k : ℤ) * hi i)
  have hsubU : GAP.subsetSumsL A' ⊆ Fintype.piFinset U := by
    intro x hx
    rw [GAP.mem_subsetSumsL] at hx
    obtain ⟨S, hS, rfl⟩ := hx
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_biUnion]
    refine ⟨S.card, Finset.mem_range.mpr
      (Nat.lt_succ_iff.mpr (Finset.card_le_card hS)), ?_⟩
    have hcoord : ∀ a ∈ S, lo i ≤ a i ∧ a i ≤ hi i := by
      intro a ha
      have haB := hsub (hS ha)
      rw [GAP.Box.mem_toFinset] at haB
      have hai := haB i
      rw [hBi i] at hai
      exact Finset.mem_Icc.mp hai
    have hsum : (S.sum id) i = ∑ a ∈ S, a i := by simp [Finset.sum_apply]
    rw [Finset.mem_Icc, hsum]
    constructor
    · calc (S.card : ℤ) * lo i = ∑ _a ∈ S, lo i := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ a ∈ S, a i := Finset.sum_le_sum fun a ha ↦ (hcoord a ha).1
    · calc ∑ a ∈ S, a i ≤ ∑ _a ∈ S, hi i :=
            Finset.sum_le_sum fun a ha ↦ (hcoord a ha).2
        _ = (S.card : ℤ) * hi i := by
            rw [Finset.sum_const, nsmul_eq_mul]
  -- `|Uᵢ| ≤ (s+1)·(s·|Bᵢ| + 1) ≤ (s+1)²·|Bᵢ|`.
  have hcardU : ∀ i, (U i).card ≤ (s + 1) ^ 2 * (B i).card := by
    intro i
    have hper : ∀ k ∈ Finset.range (s + 1),
        (Finset.Icc ((k : ℤ) * lo i) ((k : ℤ) * hi i)).card
          ≤ s * (B i).card + 1 := by
      intro k hk
      rw [Int.card_Icc, Int.toNat_le]
      have hks : (k : ℤ) ≤ s := by
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hnn : (0 : ℤ) ≤ hi i - lo i := sub_nonneg.mpr (hlohi i)
      have hkhi : (k : ℤ) * (hi i - lo i) ≤ (s : ℤ) * (hi i - lo i) :=
        mul_le_mul hks le_rfl hnn (Nat.cast_nonneg _)
      have h1 : (s : ℤ) * (hi i - lo i) ≤ (s : ℤ) * (B i).card :=
        mul_le_mul_of_nonneg_left (by linarith [hnn, hBi_card i])
          (Nat.cast_nonneg _)
      push_cast
      linarith [hkhi, h1]
    calc (U i).card
        ≤ ∑ k ∈ Finset.range (s + 1),
            (Finset.Icc ((k : ℤ) * lo i) ((k : ℤ) * hi i)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Finset.range (s + 1), (s * (B i).card + 1) :=
          Finset.sum_le_sum hper
      _ = (s + 1) * (s * (B i).card + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ (s + 1) ^ 2 * (B i).card := by
          have hpos : 1 ≤ (B i).card := Finset.card_pos.mpr (hne i)
          nlinarith [hpos]
  calc (GAP.subsetSumsL A').card
      ≤ (Fintype.piFinset U).card := Finset.card_le_card hsubU
    _ = ∏ i, (U i).card := Fintype.card_piFinset U
    _ ≤ ∏ i, ((s + 1) ^ 2 * (B i).card) :=
        Finset.prod_le_prod fun i _ ↦ hcardU i
    _ = (s + 1) ^ (2 * m) * B.card := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, pow_mul]
        rfl

namespace SubSumWitness

variable {m d : ℕ} {c : ℝ} {A : Finset (Fin m → ℤ)} (W : SubSumWitness A c d)

/-- **Lemma 8, counting form**: for a witness `W` of `A ⊆ B` with `B`
symmetric, `|P| ≤ |Σ(A')| ≤ (2·|A'|+1)^m·|B|`.  (The paper's Lemma 8
sharpens the `(2|A'|+1)^m ≈ s(A)^m` factor away via covolume arguments.) -/
theorem card_P_le_dilate {B : GAP.Box m} (hB : B.Symmetric)
    (hsub : A ⊆ B.toFinset) :
    (W.P.toFinset.card : ℝ)
      ≤ (2 * (W.A'.card : ℝ) + 1) ^ m * (B.card : ℝ) := by
  have h : W.P.toFinset.card ≤ (2 * W.A'.card + 1) ^ m * B.card :=
    (W.P.card_toFinset_le.trans W.prod_width_le_card_subsetSums).trans
      (subsetSumsL_card_le_symmetric_box hB (W.hA'.trans (W.hAh.trans hsub)))
  exact_mod_cast h

/-- The `s(A)`-form: `|P| ≤ (2·s(A)+1)^m·|B|` with
`s(A) = |A|/log²|A|`. -/
theorem card_P_le_s_pow {B : GAP.Box m} (hB : B.Symmetric)
    (hsub : A ⊆ B.toFinset) :
    (W.P.toFinset.card : ℝ)
      ≤ (2 * ((A.card : ℝ) / (Real.log (A.card : ℝ)) ^ 2) + 1) ^ m *
          (B.card : ℝ) := by
  refine (W.card_P_le_dilate hB hsub).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  have := W.hA'card
  linarith

/-- **Lemma 8 applied to a move** (counting form): a `c'`-witness `W'` of a
shifted subset `X = ϕ_P(Â) − x` satisfies
`|P'| ≤ (2|W'.A'|+1)^d·3^d·∏ᵢwᵢ` — the ambient symmetric box is the
coefficient box of the *previous* witness. -/
theorem card_P'_le_of_imageAh_sub_witness {x : Fin d → ℤ} (hx : x ∈ W.imageP)
    {d' : ℕ} {c' : ℝ}
    (W' : SubSumWitness (W.imageAh.image (· - x)) c' d') :
    (W'.P.toFinset.card : ℝ)
      ≤ (2 * (W'.A'.card : ℝ) + 1) ^ d * (3 : ℝ) ^ d *
          ∏ i, (W.P.width i : ℝ) := by
  have hsub' := W.imageAh_sub_subset_symmCoeffBox x hx
  have h1 := W'.card_P_le_dilate W.P.symmCoeffBox_symmetric hsub'
  have hw : ∀ i, 1 ≤ W.P.width i := W.one_le_width_of_mem_imageP hx
  have h2 : (W.P.symmCoeffBox.card : ℝ)
      ≤ (3 : ℝ) ^ d * ∏ i, (W.P.width i : ℝ) := by
    exact_mod_cast W.P.symmCoeffBox_card_le hw
  calc (W'.P.toFinset.card : ℝ)
      ≤ (2 * (W'.A'.card : ℝ) + 1) ^ d * (W.P.symmCoeffBox.card : ℝ) := h1
    _ ≤ (2 * (W'.A'.card : ℝ) + 1) ^ d *
          ((3 : ℝ) ^ d * ∏ i, (W.P.width i : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (by positivity) _)
    _ = _ := by ring

/-- **Interval-box form of Lemma 8's counting half**: for a witness `W` of
`A ⊆ B` with `B` an *interval* box (the situation of the ambient box of
an `(ℓ,β)`-set — not necessarily symmetric),
`|P| ≤ (|A'|+1)^{2m}·|B|`, a *polynomial* bound improving the trivial
`|P| ≤ 2^{|A'|}` (`card_le_two_pow_card_A'`).  The paper's
`|P| ≪_d |B|` removes the `(s+1)^{2m}` factor entirely (covolume
arguments — the genuinely missing part of Lemma 8). -/
theorem card_P_le_interval {B : GAP.Box m} (hB : B.IsInterval)
    (hsub : A ⊆ B.toFinset) :
    (W.P.toFinset.card : ℝ)
      ≤ ((W.A'.card : ℝ) + 1) ^ (2 * m) * (B.card : ℝ) := by
  have hne : ∀ i, (B i).Nonempty := by
    intro i
    by_contra hni
    rw [Finset.not_nonempty_iff_eq_empty] at hni
    have hA2 := W.two_le_card
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    have haB := (GAP.Box.mem_toFinset.mp (hsub ha)) i
    rw [hni] at haB
    exact Finset.notMem_empty _ haB
  have h : W.P.toFinset.card ≤ (W.A'.card + 1) ^ (2 * m) * B.card :=
    (W.P.card_toFinset_le.trans W.prod_width_le_card_subsetSums).trans
      (subsetSumsL_card_le_interval_box hB hne
        (W.hA'.trans (W.hAh.trans hsub)))
  exact_mod_cast h

/-- **Lemma 8 for a move, at `|P|`**: a `c'`-witness `W'` of a shifted
subset `X = ϕ_P(Â) − x` satisfies `|P'| ≤ (|W'.A'|+1)^{2d}·3^d·|P|` —
the interval-box form (`card_P_le_interval`) applied to the ambient
symmetric coefficient box, with `∏ᵢ wᵢ = |P|` by properness. -/
theorem card_P'_le_move_of_imageAh_sub_witness {x : Fin d → ℤ}
    (hx : x ∈ W.imageP) {d' : ℕ} {c' : ℝ}
    (W' : SubSumWitness (W.imageAh.image (· - x)) c' d') :
    (W'.P.toFinset.card : ℝ)
      ≤ ((W'.A'.card : ℝ) + 1) ^ (2 * d) * (3 : ℝ) ^ d *
          (W.P.toFinset.card : ℝ) := by
  have hsub' := W.imageAh_sub_subset_symmCoeffBox x hx
  have h1 := W'.card_P_le_interval W.P.symmCoeffBox_isInterval hsub'
  have hw : ∀ i, 1 ≤ W.P.width i := W.one_le_width_of_mem_imageP hx
  have h2 : (W.P.symmCoeffBox.card : ℝ)
      ≤ (3 : ℝ) ^ d * ∏ i, (W.P.width i : ℝ) := by
    exact_mod_cast W.P.symmCoeffBox_card_le hw
  have hP : (W.P.toFinset.card : ℝ) = ∏ i, (W.P.width i : ℝ) := by
    have hproper : W.P.Proper :=
      (GAP.proper_smul_iff (by exact_mod_cast W.kpos.ne')).mp W.hproper
    exact_mod_cast (GAP.card_toFinset_of_proper _ hproper)
  calc (W'.P.toFinset.card : ℝ)
      ≤ ((W'.A'.card : ℝ) + 1) ^ (2 * d) * (W.P.symmCoeffBox.card : ℝ) := h1
    _ ≤ ((W'.A'.card : ℝ) + 1) ^ (2 * d) *
          ((3 : ℝ) ^ d * ∏ i, (W.P.width i : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (by positivity) _)
    _ = _ := by rw [hP]; ring

end SubSumWitness

/- **Constant rigidity** (a formalization caveat, no statement):
`SubSumWitness A c d` mixes two monotonicity directions in `c`:
`hk : k ≤ c·s(A)` is easier for *larger* `c`, while
`hAhcard : |A| − c⁻¹·|A|/log|A| ≤ |Â|` is easier for *smaller* `c`.
Hence a `c`-witness upgrades to *no* other constant — in particular
there is no `SubSumWitness.of_le_const`.  The paper suppresses this:
its `d(A)` (and hence `P(A)` in Definition 9/Lemma 10) is computed at
the Corollary-5 constant of the *ambient class of each set*, while the
Lean `Irreducible`/`SubSumDim` check every moved set at the *single*
constant `c'`.  Discharging `Nonempty (SubSumWitness X' c' d)` for all
moves `X' ⊆ ℤ^{d'}` uniformly therefore requires a uniform Cor-5
constant valid for all `(d',β')`-classes, `d' ≤ D` — a statement that
is *not* implied by `cfp_structure_cor` (which supplies one constant
per class).  This is isolated as the predicate `UniformCor5` below. -/

/-- `c'` is a *Cor-5 constant for `(n,β')`-sets above `C₀`*: every
`X ⊆ ℤⁿ` in an interval box `B'` with `|B'| ≤ |X|^β'` and
`C₀ ≤ |X|` admits a `c'`-witness (so `SubSumDim X c'` is attained).
`subSumDim_exists` gives `∃ c' …` for each fixed `n`; the Lemma-10
iteration needs *one* `c'` for all `n ≤ D` (see the constant-rigidity
note above). -/
def UniformCor5 (c' β' : ℝ) (n : ℕ) (C₀ : ℝ) : Prop :=
  ∀ (X : Finset (Fin n → ℤ)) (B' : GAP.Box n), B'.IsInterval →
    X ⊆ B'.toFinset → (B'.card : ℝ) ≤ (X.card : ℝ) ^ β' →
    C₀ ≤ (X.card : ℝ) → ∃ d', Nonempty (SubSumWitness X c' d')

/-! ### Non-vacuity of `Irreducible` and the move trichotomy -/

/-- Irreducibility applied to `A' = ϕ_P(Â)` itself and `x = 0` (the
"identity" instance of Definition 9): the unshifted embedded image already
has subset-sum dimension `d` at the constant `c'`, and every `d`-dimensional
`c'`-witness satisfies `|P'| ≥ γ|P|`.  This makes `Irreducible` visibly
non-vacuous — the quantifier is instantiated by `ϕ_P(Â)`. -/
theorem Irreducible.apply_imageAh {d : ℕ} {c c' δ γ : ℝ}
    {m : ℕ} {A : Finset (Fin m → ℤ)} (W : SubSumWitness A c d)
    (hI : Irreducible W c' δ γ)
    (hδ : (δ : ℝ) * (A.card : ℝ) ≤ (W.imageAh.card : ℝ)) :
    Nonempty (SubSumWitness W.imageAh c' d) ∧
      SubSumDim W.imageAh c' = d ∧
      ∀ (W' : SubSumWitness W.imageAh c' d),
        (γ : ℝ) * (W.P.toFinset.card : ℝ) ≤ (W'.P.toFinset.card : ℝ) := by
  have h := hI.2 W.imageAh 0 (Subset.refl _) hδ W.zero_mem_imageP
  rwa [image_sub_zero] at h

/-- **The zeroth move of Lemma 10.**  For `W` the canonical (minimal
dimension) witness of `A` with `δ·|A| ≤ |Â|`, the embedded image
`Ã = ϕ_P(Â) ⊆ ℤ^{d(A)}` is obtained from `A` by a single
`DerivedFrom`-move with `x = 0 ∈ ϕ_P(P)`. -/
theorem DerivedFrom.imageAh_step {A : Finset (Fin ℓ → ℤ)} {δ : ℝ}
    {d : ℕ} {c : ℝ} (W : SubSumWitness A c d) (hd : SubSumDim A c = d)
    (hδ : (δ : ℝ) * (A.card : ℝ) ≤ (W.imageAh.card : ℝ)) :
    DerivedFrom A δ W.imageAh := by
  refine DerivedFrom.step DerivedFrom.refl W hd 0 W.zero_mem_imageP
    (C := W.imageAh) ?_ hδ
  intro y hy
  rwa [image_sub_zero]

/-- **Lemma 10, zeroth move (bundled).**  Every sufficiently large
`(ℓ,β)`-set `A` has a canonical witness `W` at `d = d(A)` and the embedded
image `Ã = ϕ_P(Â)` is a `DerivedFrom A δ` non-averaging set with
`|Ã| ≥ |A|(1 − (c·log|A|)⁻¹)`.  The paper's iteration then applies
down/up/shrink moves starting from this `Ã`. -/
theorem exists_first_move {δ β : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hβ : 1 < β) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧
      ∀ {A : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ},
        B.IsInterval → NonAveraging A → A ⊆ B.toFinset →
        (B.card : ℝ) ≤ (A.card : ℝ) ^ β → N ≤ A.card →
      ∃ (d : ℕ) (W : SubSumWitness A c d),
        SubSumDim A c = d ∧
        DerivedFrom A δ W.imageAh ∧
        NonAveraging W.imageAh ∧
        (A.card : ℝ) * (1 - (c * Real.log (A.card : ℝ))⁻¹) ≤
          (W.imageAh.card : ℝ) := by
  obtain ⟨c, C, hc, hCpos, hwit⟩ := subSumDim_exists (ℓ := ℓ) hβ
  obtain ⟨N₀, hN₀⟩ := exists_card_ge_exp (max (2 * c⁻¹) (1 / (c * (1 - δ))))
  refine ⟨c, max N₀ ⌈C⌉₊, hc, fun {A} {B} hBi hNA hsubB hB hN ↦ ?_⟩
  have hCm : C ≤ (A.card : ℝ) :=
    (Nat.le_ceil C).trans
      (by exact_mod_cast (Nat.le_max_right _ _).trans hN)
  obtain ⟨d₀, ⟨W₀⟩⟩ := hwit A B hBi hsubB hB hCm
  obtain ⟨h2, hlog⟩ := hN₀ ((Nat.le_max_left _ _).trans hN)
  have hApos : (0 : ℝ) < (A.card : ℝ) := by linarith
  have hlp : (0 : ℝ) < Real.log (A.card : ℝ) := by
    have hcc : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
    have := (le_max_left _ _).trans hlog
    linarith
  obtain ⟨W⟩ := subSumDim_mem (A := A) (c := c) ⟨d₀, ⟨W₀⟩⟩
  have hAh := W.one_sub_inv_mul_le_Ah_card
  -- `δ·|A| ≤ |Â|` since `(c·log|A|)⁻¹ ≤ 1−δ`.
  have hδcard : (δ : ℝ) * (A.card : ℝ) ≤ (W.Ah.card : ℝ) := by
    have hclog : (0 : ℝ) < c * Real.log (A.card : ℝ) := mul_pos hc hlp
    have h1d : (0 : ℝ) < 1 - δ := sub_pos.mpr hδ1
    have hinv : (c * Real.log (A.card : ℝ))⁻¹ ≤ 1 - δ := by
      rw [inv_le_iff_one_le_mul₀ hclog]
      have h' := (div_le_iff₀ (mul_pos hc h1d)).mp
        ((le_max_right _ _).trans hlog)
      have e : (1 - δ) * (c * Real.log (A.card : ℝ))
          = Real.log (A.card : ℝ) * (c * (1 - δ)) := by ring
      rwa [e]
    calc (δ : ℝ) * (A.card : ℝ)
        ≤ (1 - (c * Real.log (A.card : ℝ))⁻¹) * (A.card : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hApos.le
      _ = (A.card : ℝ) * (1 - (c * Real.log (A.card : ℝ))⁻¹) := mul_comm _ _
      _ ≤ (W.Ah.card : ℝ) := hAh
  refine ⟨SubSumDim A c, W, rfl, ?_, ?_, ?_⟩
  · exact DerivedFrom.imageAh_step W rfl (by rwa [W.card_imageAh])
  · exact W.P.nonAveraging_ptCoeffImage
      (fun _ ha ↦ W.hsub (Finset.mem_union_left _ ha))
      (NonAveraging.mono W.hAh hNA)
  · rwa [W.card_imageAh]

/-- **The down/up/shrink trichotomy** (paper §3.2, the three moves of
Lemma 10).  If `W` is `A`'s minimal-dimension witness (`d = d(A) ≥ 1`)
and `W` is not `(δ,γ)`-irreducible at the constant `c'`, some `A' ⊆ ϕ_P(Â)`,
`|A'| ≥ δ|A|`, `x ∈ ϕ_P(P)` yields a derived set `A' − x` which is either
a *down-move* (`d(A'−x) < d`), an *up-move* (`d(A'−x) > d`), or a
*shrink-move* (`d(A'−x) = d` with a witness `|P'| < γ|P|`). -/
theorem DerivedFrom.step_cases {A : Finset (Fin ℓ → ℤ)} {δ γ c' : ℝ}
    {d : ℕ} {c : ℝ} (W : SubSumWitness A c d) (hd : SubSumDim A c = d)
    (hdpos : 1 ≤ d) (hnir : ¬ Irreducible W c' δ γ) :
    ∃ (A' : Finset (Fin d → ℤ)) (x : Fin d → ℤ),
      A' ⊆ W.imageAh ∧ x ∈ W.imageP ∧
      (δ : ℝ) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      DerivedFrom A δ (A'.image (· - x)) ∧
      (SubSumDim (A'.image (· - x)) c' < d ∨
        d < SubSumDim (A'.image (· - x)) c' ∨
        (SubSumDim (A'.image (· - x)) c' = d ∧
          ∃ W' : SubSumWitness (A'.image (· - x)) c' d,
            (W'.P.toFinset.card : ℝ)
              < (γ : ℝ) * (W.P.toFinset.card : ℝ))) := by
  obtain ⟨A', x, hA'sub, hx, hcard, hder, hcon⟩ :=
    DerivedFrom.step_of_not_irreducible DerivedFrom.refl W hd hnir
  refine ⟨A', x, hA'sub, hx, hcard, hder, ?_⟩
  set X := A'.image (· - x) with hX
  rcases Nat.lt_trichotomy (SubSumDim X c') d with h | h | h
  · exact Or.inl h
  · right; right
    refine ⟨h, ?_⟩
    have hne : ∃ d', Nonempty (SubSumWitness X c' d') := by
      by_contra hnone
      have hS : SubSumDim X c' = 0 := by
        unfold SubSumDim
        have hSet : {d' : ℕ | Nonempty (SubSumWitness X c' d')} = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr fun d' hh ↦ hnone ⟨d', hh⟩
        rw [hSet, Nat.sInf_empty]
      omega
    have hW : Nonempty (SubSumWitness X c' d) := by
      have h0 := subSumDim_mem hne
      rwa [h] at h0
    exact hcon hW h
  · exact Or.inr (Or.inl h)

/-- Non-vacuity certificate for the faithful statement below: with a fixed
universal constant `c₀`, any produced witness on a large `At` is genuine —
`dt ≥ 1` and `|Ât| ≥ |At|/2`.  The degenerate escape
(`ct := (log|A|)⁻¹`, `Â = ∅`, `dt = 0`) is excluded. -/
theorem faithful_witness_genuine {n : ℕ} {At : Finset (Fin n → ℤ)} {c₀ : ℝ}
    {dt : ℕ} (Wt : SubSumWitness At c₀ dt)
    (hlog : 2 * c₀⁻¹ ≤ Real.log (At.card : ℝ))
    (h4 : (4 : ℝ) ≤ (At.card : ℝ)) :
    1 ≤ dt ∧ (At.card : ℝ) / 2 ≤ (Wt.Ah.card : ℝ) := by
  have hApos : (0 : ℝ) < (At.card : ℝ) := by linarith
  have hhalf := Wt.half_le_Ah_card hApos hlog
  refine ⟨?_, hhalf⟩
  rcases Nat.eq_zero_or_pos dt with rfl | hd
  · exfalso
    have h1 : (Wt.Ah.card : ℝ) ≤ 1 := by exact_mod_cast Wt.card_Ah_le_one
    linarith
  · exact hd

/-! ### The Lemma-10 iteration: missing inputs and skeleton

The remaining proof obligations of `irreduciblization_faithful` are
isolated into three named lemmas:

* `lem68_move_bound` — the *content* of Lemmas 6 and 8 in move form
  (the covolume/discrete-John input): a move `X' = A₁ − x` which admits
  `c'`-witnesses has a canonical `c'`-witness obeying
  `|P'| ≤ C₆₈·sMin^{−max(0,d'−d)}·|P|`;
* `uniform_cor5_exists` — the *uniform-constant* input: a single `c'`
  serving as a Cor-5 constant for every `(d,β')`-class `d ≤ D`
  (see the constant-rigidity note above — the paper uses per-class
  constants, so this needs either a `∀ c ≥ c₀` strengthening of
  `cfp_structure_cor` or a reformulation of `Irreducible`);
* `iterates_to_irreducible` — the *bookkeeping* input (equations
  (8)–(10)): the measure-descent loop. -/

/-- **The covolume bridge** — the single remaining mathematical input
of Lemma 10 in this file (paper Lemmas 6 + 8, which in turn need the
discrete John lemma 7 = `discrete_john_strong` and the Lemmas 11–14
covolume machinery).  For a set `X' ⊆ ℤⁿ` contained in an interval box
`B'`, *every* canonical `c'`-witness `W'` (i.e. a witness at the minimal
subset-sum dimension `d' = SubSumDim X' c'`) obeys

  `|P'| ≤ C · sMin^{−max(0, d'−n)} · |B'|`.

In the paper: for `d' ≤ n` this is Lemma 8's `|P| ≪_d |B|`, proved via
`x + csP ⊆ Σ(A') ⊆ sB''` where `B'' = P(v,N)` is the symmetric GAP that
`discrete_john_strong` sandwiches around `H ∩ B` (`H = span P`,
`dim H ≤ d'`), giving `(cs)^{d'}|P| ≲ |csP| ≤ |sB''| ≈ s^{dim H}|B''|
≲ s^{d'}|B|`; for `d' > n` it is Lemma 6's `|P| ≪_d s^{−(d'−n)}|B|`,
the same count read off the GAP `B'`.  The `s^{d'}` factor on the left
is the *width*-scaled `csP` of CFP23; in the `SubSumWitness` encoding it
is folded into `P` itself (witnesses produced by `uniform_cor5_of_family`
have `P = Q.widthScale k`, `k_wit = 1`).

*Faithfulness caveat.*  The implied constant is a genuine `C_n > 1`
(Lemma 7's `c_d^{−dim H}` and the `|B''| ≲ |B|` factor), so the statement
is honest only at `C ≥ C_n` with `sMin` a uniform lower bound on the
`s(A_j)` of the iteration; with free `C`, `sMin` it inherits the
degenerate-instantiation caveat documented at `lem68_move_bound`. -/
theorem lem68_covolume {n : ℕ} {X' : Finset (Fin n → ℤ)}
    {B' : GAP.Box n} {c' sMin C : ℝ}
    (_hB : B'.IsInterval) (_hsub : X' ⊆ B'.toFinset)
    (W' : SubSumWitness X' c' (SubSumDim X' c')) :
    (W'.P.toFinset.card : ℝ) ≤
      C * sMin ^ (-(max 0 ((SubSumDim X' c' : ℝ) - (n : ℝ)))) *
        (B'.card : ℝ) := by
  sorry

/-- **Lemmas 6 + 8, move form** — the covolume input to Lemma 10.
For a move `X' = A₁ − x` of a canonical witness (`A₁ ⊆ ϕ_P(Â)`,
`|A₁| ≥ δ|X|`, `x ∈ ϕ_P(P)`), provided `X'` admits `c'`-witnesses at
all (`hwit`), its *canonical* `c'`-witness `W'` obeys

  `|P'| ≤ C₆₈ · sMin^{−max(0, d'−d)} · |P|`

where `d' = SubSumDim X' c'` and `sMin` is a uniform lower bound on the
Cor-5 parameters `s(A_j)` along the iteration.  For down-moves
(`d' < d`) this is Lemma 8's `|P'| ≪_d |P|` (via `X' ⊆ P.symmCoeffBox`,
`W.imageAh_sub_subset_symmCoeffBox`); for up-moves (`d' > d`) it is
Lemma 6's `|P'| ≪_d s(A₁)^{-(d'−d)}|P|`.  Both estimates need the
discrete-John/covolume machinery (paper Lemmas 7, 11–14); the
elementary bound currently available is the much weaker
`SubSumWitness.card_P'_le_move_of_imageAh_sub_witness`
(`|P'| ≤ (s'+1)^{2d}·3^d·|P|`).

The proof produces the canonical witness `W'` via `subSumDim_mem` and
applies the covolume bridge `lem68_covolume` to the ambient box
`B' = coeffBox P − x` — which is an interval box
(`GAP.Box.coeffBox_translate_isInterval`) containing `X'`
(`SubSumWitness.imageAh_sub_subset_coeffBox_translate`) and has
`|B'| = ∏ᵢ wᵢ = |P|` exactly (`GAP.coeffBox_card` +
`GAP.card_toFinset_of_proper` applied to `P`, proper since `kP` is). -/
theorem lem68_move_bound {n : ℕ} {X : Finset (Fin n → ℤ)} {d : ℕ}
    {c' δ sMin C₆₈ : ℝ}
    (W : SubSumWitness X c' d) (hd : SubSumDim X c' = d)
    {A₁ : Finset (Fin d → ℤ)} {x : Fin d → ℤ}
    (hA₁ : A₁ ⊆ W.imageAh) (hx : x ∈ W.imageP)
    (hA₁card : δ * (X.card : ℝ) ≤ (A₁.card : ℝ))
    (hwit : ∃ d', Nonempty (SubSumWitness (A₁.image (· - x)) c' d')) :
    ∃ W' : SubSumWitness (A₁.image (· - x)) c'
        (SubSumDim (A₁.image (· - x)) c'),
      (W'.P.toFinset.card : ℝ) ≤
        C₆₈ * sMin ^
            (-(max 0 ((SubSumDim (A₁.image (· - x)) c' : ℝ) - (d : ℝ))))
          * (W.P.toFinset.card : ℝ) := by
  obtain ⟨W'⟩ := subSumDim_mem hwit
  refine ⟨W', ?_⟩
  -- `X' = A₁ − x ⊆ coeffBox P − x`, an interval box of cardinality `|P|`.
  have hsub' : A₁.image (· - x) ⊆
      (W.P.coeffBox.translate (-x)).toFinset :=
    (Finset.image_subset_image hA₁).trans
      (W.imageAh_sub_subset_coeffBox_translate x)
  have hPcard : ((W.P.coeffBox.translate (-x)).card : ℝ)
      = (W.P.toFinset.card : ℝ) := by
    rw [GAP.Box.card_translate, GAP.coeffBox_card]
    have hproper : W.P.Proper :=
      (GAP.proper_smul_iff (by exact_mod_cast W.kpos.ne')).mp W.hproper
    exact_mod_cast (GAP.card_toFinset_of_proper _ hproper).symm
  rw [← hPcard]
  exact lem68_covolume (GAP.Box.coeffBox_translate_isInterval _ _)
    hsub' W'

/-- **Lemmas-6/8 move bound, hypothesis form** — the `∀`-statement of
`lem68_move_bound` with the constants `c' δ sMin C₆₈` fixed.  Passed to
`iterates_to_irreducible`/`l10_descent` as `hmove`; the call site
supplies `lem68_move_bound`. -/
abbrev MoveBound68 (c' δ sMin C₆₈ : ℝ) : Prop :=
  ∀ {n : ℕ} {X : Finset (Fin n → ℤ)} {d : ℕ}
    (W : SubSumWitness X c' d), SubSumDim X c' = d →
    ∀ {A₁ : Finset (Fin d → ℤ)} {x : Fin d → ℤ},
    A₁ ⊆ W.imageAh → x ∈ W.imageP →
      δ * (X.card : ℝ) ≤ (A₁.card : ℝ) →
      (∃ d', Nonempty (SubSumWitness (A₁.image (· - x)) c' d')) →
      ∃ W' : SubSumWitness (A₁.image (· - x)) c'
          (SubSumDim (A₁.image (· - x)) c'),
        (W'.P.toFinset.card : ℝ) ≤
          C₆₈ * sMin ^
              (-(max 0 ((SubSumDim (A₁.image (· - x)) c' : ℝ) - (d : ℝ))))
            * (W.P.toFinset.card : ℝ)

/-- `DerivedFrom` is transitive (concatenate the two move chains). -/
theorem DerivedFrom.trans {A : Finset (Fin ℓ → ℤ)} {δ : ℝ}
    {m n : ℕ} {X : Finset (Fin m → ℤ)} {Y : Finset (Fin n → ℤ)}
    (h : DerivedFrom A δ X) (h' : DerivedFrom X δ Y) :
    DerivedFrom A δ Y := by
  induction h' with
  | refl => exact h
  | step hder W hd' x hx hC hCcard ih =>
      exact DerivedFrom.step ih W hd' x hx hC hCcard

/-- The down/up/shrink trichotomy at a *derived* set `X` — the
`hder = DerivedFrom.refl` case is `DerivedFrom.step_cases`. -/
theorem DerivedFrom.step_cases_of_derived {A : Finset (Fin ℓ → ℤ)}
    {δ γ c' : ℝ} {n : ℕ} {X : Finset (Fin n → ℤ)} {d : ℕ} {c : ℝ}
    (hder : DerivedFrom A δ X) (W : SubSumWitness X c d)
    (hd : SubSumDim X c = d) (hdpos : 1 ≤ d)
    (hnir : ¬ Irreducible W c' δ γ) :
    ∃ (A' : Finset (Fin d → ℤ)) (x : Fin d → ℤ),
      A' ⊆ W.imageAh ∧ x ∈ W.imageP ∧
      (δ : ℝ) * (X.card : ℝ) ≤ (A'.card : ℝ) ∧
      DerivedFrom A δ (A'.image (· - x)) ∧
      (SubSumDim (A'.image (· - x)) c' < d ∨
        d < SubSumDim (A'.image (· - x)) c' ∨
        (SubSumDim (A'.image (· - x)) c' = d ∧
          ∃ W' : SubSumWitness (A'.image (· - x)) c' d,
            (W'.P.toFinset.card : ℝ)
              < (γ : ℝ) * (W.P.toFinset.card : ℝ))) := by
  obtain ⟨A', x, hA'sub, hx, hcard, hder', hcon⟩ :=
    DerivedFrom.step_of_not_irreducible hder W hd hnir
  refine ⟨A', x, hA'sub, hx, hcard, hder', ?_⟩
  rcases Nat.lt_trichotomy (SubSumDim (A'.image (· - x)) c') d with h | h | h
  · exact Or.inl h
  · right; right
    refine ⟨h, ?_⟩
    have hne : ∃ d', Nonempty (SubSumWitness (A'.image (· - x)) c' d') := by
      by_contra hnone
      have hS : SubSumDim (A'.image (· - x)) c' = 0 := by
        unfold SubSumDim
        have hSet :
            {d' : ℕ | Nonempty (SubSumWitness (A'.image (· - x)) c' d')} = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr fun d' hh ↦ hnone ⟨d', hh⟩
        rw [hSet, Nat.sInf_empty]
      omega
    have hW : Nonempty (SubSumWitness (A'.image (· - x)) c' d) := by
      have h0 := subSumDim_mem hne
      rwa [h] at h0
    exact hcon hW h
  · exact Or.inr (Or.inl h)

/-- `|P.toFinset| ≥ 1`: the base point lies in `P` since
`(Â ∪ {0}) ⊆ P.toFinset`. -/
theorem SubSumWitness.one_le_card_P {n : ℕ} {X : Finset (Fin n → ℤ)}
    {c : ℝ} {d : ℕ} (W : SubSumWitness X c d) :
    (1 : ℝ) ≤ (W.P.toFinset.card : ℝ) := by
  have hne : W.P.toFinset.Nonempty :=
    ⟨0, W.hsub (Finset.mem_union_right _ (Finset.mem_singleton_self 0))⟩
  have h : 0 < W.P.toFinset.card := Finset.card_pos.mpr hne
  exact_mod_cast h

/-- A canonical `c'`-witness with `|ϕ_P(Â)| < δ·|X|` is vacuously
`(δ,γ)`-irreducible: the `∀`-quantifier has no data to check. -/
theorem irreducible_of_imageAh_small {n : ℕ} {X : Finset (Fin n → ℤ)}
    {c' δ γ : ℝ} (W : SubSumWitness X c' (SubSumDim X c'))
    (hsmall : (W.imageAh.card : ℝ) < δ * (X.card : ℝ)) :
    Irreducible W c' δ γ := by
  refine ⟨rfl, ?_⟩
  intro A' x hA'sub hcard hx
  exfalso
  have h1 : (A'.card : ℝ) ≤ (W.imageAh.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hA'sub
  linarith

/-- **Residual of `moved_set_is_lb`** — the `|B'| ≤ |X'|^{β'}` half of
the `(d,β')`-set property of a move `X' = A₁ − x`, instantiated at the
ambient interval box `B' = coeffBox P − x` (whose cardinality is
`∏ᵢ wᵢ = |P|` exactly, `GAP.coeffBox_card` + `card_toFinset_of_proper`).

Paper content: Lemma 8 applied to `X`'s `(n,β)`-box `B_X` gives
`|P| ≪_d |B_X|` (the same `lem68_covolume` input), then
`|P| ≲ |B_X| ≤ |X|^β ≲ δ^{−β}|X'|^β ≤ |X'|^{β'}` — the last step needs
`β < β'` and `|X'|` large enough to absorb the `C·δ^{−β}` factor.
*Faithfulness caveat*: `X`'s ambient `(n,β)`-box is the `(d,β')`-set
invariant that `L10Stage` does not currently track (the crude
`DerivedFrom.exists_interval_box` bound `2^{|A|} + |B_A|` is
exponential), and `β'`, `δ` are free here, so this is honest only at the
intended instantiation `β' = 3β`, `|X'|` large. -/
theorem moved_set_card_residual {n d : ℕ} {X : Finset (Fin n → ℤ)}
    {c' δ β' : ℝ} {A₁ : Finset (Fin d → ℤ)} {x : Fin d → ℤ}
    (W : SubSumWitness X c' d) (_hA₁ : A₁ ⊆ W.imageAh)
    (_hx : x ∈ W.imageP)
    (_hcard : δ * (X.card : ℝ) ≤ (A₁.card : ℝ)) :
    ((∏ i, W.P.width i : ℕ) : ℝ) ≤
      ((A₁.image (· - x)).card : ℝ) ^ β' := by
  sorry

/-- **Lemma 8, `(d,β')`-set form** — a move `A₁ − x` of a canonical
`c'`-witness is a `(d,β')`-set: it is contained in the interval box
`coeffBox P − x` (membership is proved, see
`SubSumWitness.imageAh_sub_subset_coeffBox_translate`) whose size `|P|`
is `≪_d |A₁−x|^{β'}`.  *Faithful gap*: the bound
`|P| ≪_d |B_X|` for the ambient box of `X` is the same
discrete-John/covolume input as `lem68_move_bound`; what remains is
`moved_set_card_residual` (`∏ᵢ wᵢ = |P| ≤ |X'|^{β'}`). -/
theorem moved_set_is_lb {n d : ℕ} {X : Finset (Fin n → ℤ)}
    {c' δ β' : ℝ} {A₁ : Finset (Fin d → ℤ)} {x : Fin d → ℤ}
    (W : SubSumWitness X c' d) (hA₁ : A₁ ⊆ W.imageAh) (hx : x ∈ W.imageP)
    (hcard : δ * (X.card : ℝ) ≤ (A₁.card : ℝ)) :
    ∃ B' : GAP.Box d, B'.IsInterval ∧ A₁.image (· - x) ⊆ B'.toFinset ∧
      (B'.card : ℝ) ≤ ((A₁.image (· - x)).card : ℝ) ^ β' := by
  refine ⟨W.P.coeffBox.translate (-x),
    GAP.Box.coeffBox_translate_isInterval _ _, ?_, ?_⟩
  · exact (Finset.image_subset_image hA₁).trans
      (W.imageAh_sub_subset_coeffBox_translate x)
  · rw [GAP.Box.card_translate, GAP.coeffBox_card]
    exact_mod_cast moved_set_card_residual W hA₁ hx hcard

/-- **Lemmas 6 + 8, initial-set form** — the `|P(A)|` bound at the start
of the iteration, `|P₀| ≪ s(A)^{−max(0,d₀−ℓ)}·|B|` (Lemma 6 when
`d₀ > ℓ`; Lemma 8's `|P| ≪_d |B|` otherwise).  Same covolume/discrete-John
input as `lem68_move_bound`. -/
theorem lem68_initial_bound {A : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ}
    {c' sMin C₆₈ : ℝ}
    (hBint : B.IsInterval) (hsub : A ⊆ B.toFinset)
    (W : SubSumWitness A c' (SubSumDim A c')) :
    (W.P.toFinset.card : ℝ) ≤
      C₆₈ * sMin ^ (-(max 0 ((SubSumDim A c' : ℝ) - (ℓ : ℝ))))
        * (B.card : ℝ) :=
  lem68_covolume hBint hsub W

/-- **Per-dimension Cor-5 family**: apply `cfp_structure` (at `η = 1/2`)
in every ambient dimension `d` and collect the constants into functions
`cf`, `df`.  The produced `hcfp d` is Theorem 3 of the paper for
`(d,β')`-sets with the explicit admissible range
`m^{1/2} ≤ s ≤ cf_d·m/log m` on the subset-size parameter `s`. -/
theorem cfp_structure_family {β' : ℝ} (hβ' : 1 < β') :
    ∃ (cf df : ℕ → ℝ), (∀ d, 0 < cf d) ∧ (∀ d : ℕ,
      ∀ (A : Finset (Fin d → ℤ)) (B : GAP.Box d) (s : ℕ),
        A.Nonempty → B.IsInterval → A ⊆ B.toFinset →
        (B.card : ℝ) ≤ (A.card : ℝ) ^ β' →
        (A.card : ℝ) ^ ((1 : ℝ) / 2) ≤ (s : ℝ) →
        (s : ℝ) ≤ cf d * (A.card : ℝ) / Real.log (A.card : ℝ) →
        16 * (cf d + 1) * (cf d / Real.log 2 + 1) ^ 2 *
          (2 * (cf d / Real.log 2) + 1) ^ (2 * d) < (A.card : ℝ) →
        ∃ (Â : Finset (Fin d → ℤ)) (d' : ℕ) (P : GAP d d'),
          Â ⊆ A ∧
          (A.card : ℝ) - (cf d)⁻¹ * (s : ℝ) * Real.log (A.card : ℝ)
            ≤ (Â.card : ℝ) ∧
          (d' : ℝ) ≤ df d ∧ P.Symmetric ∧ (Â ∪ {0}) ⊆ P.toFinset ∧
          ∃ A' ⊆ Â, A'.card ≤ s ∧
            ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ cf d * (s : ℝ) ∧
              ∃ t : Fin d → ℤ,
                ((P.widthScale k).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
                (P.widthScale k).Proper) := by
  classical
  choose cf df hcf using fun d : ℕ ↦
    cfp_structure d hβ' (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)
  exact ⟨cf, df, fun d ↦ (hcf d).1, fun d ↦ (hcf d).2.2⟩

/-- **Uniform Cor-5 constant via the `s`-parameter rescaling** (the step
that resolves the constant-rigidity obstruction of the earlier round-6
note): given a per-dimension family of `cfp_structure`-type outputs with
constants `cf d`, take `c' := min_{d ≤ D} cf d`.  For a `(d,β')`-set `X`
with `|X|` large, apply `hcfp` *not* at `s = s(X)` but at the rescaled
choice `s := ⌊(c'/cf_d)·s(X)⌋₊` where `s(X) = |X|/log²|X|`.  Then

* `|A'| ≤ s ≤ (c'/cf_d)·s(X) ≤ s(X)` and `k ≤ cf_d·s ≤ c'·s(X)`
  (using `c' ≤ cf d`);
* `|Â| ≥ |X| − cf_d⁻¹·s·log|X| ≥ |X| − c'⁻¹·|X|/log|X|`, since
  `cf_d⁻¹·s·log|X| ≈ (c'/cf_d²)·|X|/log|X| ≤ c'⁻¹·|X|/log|X|`
  (again `c' ≤ cf d`).

The largeness `|X| ≥ C₀ d` supplies the admissible range
`|X|^{1/2} ≤ s ≤ cf_d·|X|/log|X|`: the needed bounds `log²|X| ≤
|X|^{1/4}`, `2·cf_d/c' ≤ |X|^{1/4}` and `c'/cf_d² ≤ log|X|` are all
eventual in `|X|`.  The dimension bound is `d' ≤ ⌈df d⌉₊` — a uniform
`O_{d,β'}(1)` cap, *not* `d' ≤ d` (proper GAPs in `ℤ^d` can have rank
greater than `d`, e.g. steps `3,5,7` with widths `2,2,2` give a proper
`GAP 1 3`). -/
theorem uniform_cor5_of_family {β' : ℝ} (hβ' : 1 < β')
    {cf df : ℕ → ℝ} (hcf : ∀ d, 0 < cf d)
    (hcfp : ∀ d : ℕ,
      ∀ (A : Finset (Fin d → ℤ)) (B : GAP.Box d) (s : ℕ),
        A.Nonempty → B.IsInterval → A ⊆ B.toFinset →
        (B.card : ℝ) ≤ (A.card : ℝ) ^ β' →
        (A.card : ℝ) ^ ((1 : ℝ) / 2) ≤ (s : ℝ) →
        (s : ℝ) ≤ cf d * (A.card : ℝ) / Real.log (A.card : ℝ) →
        16 * (cf d + 1) * (cf d / Real.log 2 + 1) ^ 2 *
          (2 * (cf d / Real.log 2) + 1) ^ (2 * d) < (A.card : ℝ) →
        ∃ (Â : Finset (Fin d → ℤ)) (d' : ℕ) (P : GAP d d'),
          Â ⊆ A ∧
          (A.card : ℝ) - (cf d)⁻¹ * (s : ℝ) * Real.log (A.card : ℝ)
            ≤ (Â.card : ℝ) ∧
          (d' : ℝ) ≤ df d ∧ P.Symmetric ∧ (Â ∪ {0}) ⊆ P.toFinset ∧
          ∃ A' ⊆ Â, A'.card ≤ s ∧
            ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ cf d * (s : ℝ) ∧
              ∃ t : Fin d → ℤ,
                ((P.widthScale k).translate t).toFinset ⊆ GAP.subsetSumsL A' ∧
                (P.widthScale k).Proper)
    (D : ℕ) :
    ∃ (c' : ℝ) (C₀ : ℕ → ℝ), 0 < c' ∧
      ∀ ⦃d : ℕ⦄, d ≤ D → ∀ {X : Finset (Fin d → ℤ)} {B' : GAP.Box d},
        B'.IsInterval → X ⊆ B'.toFinset →
        (B'.card : ℝ) ≤ (X.card : ℝ) ^ β' → (C₀ d : ℝ) ≤ (X.card : ℝ) →
        ∃ d' ≤ ⌈df d⌉₊, Nonempty (SubSumWitness X c' d') := by
  classical
  have hne : (Finset.range (D + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  set c' := (Finset.range (D + 1)).inf' hne cf with hc'
  have hc'pos : (0 : ℝ) < c' := by
    rw [hc', Finset.lt_inf'_iff]
    exact fun d _ ↦ hcf d
  have hc'le : ∀ d ≤ D, c' ≤ cf d := fun d hd ↦
    Finset.inf'_le cf (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hd))
  have evLog : ∀ᶠ m : ℝ in Filter.atTop,
      (Real.log m) ^ 2 ≤ 64 * m ^ ((1 : ℝ) / 8) := by
    have hLo : (fun x : ℝ ↦ (Real.log (x ^ ((1 : ℝ) / 8))) ^ 2) =o[Filter.atTop]
        (fun x ↦ x ^ ((1 : ℝ) / 8)) :=
      (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [hLo.bound zero_lt_one, Filter.eventually_gt_atTop 0]
      with m hm hm0
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hm
    have hm' : |(Real.log (m ^ ((1 : ℝ) / 8))) ^ 2|
        ≤ 1 * |m ^ ((1 : ℝ) / 8)| := hm
    rw [one_mul, abs_of_nonneg (Real.rpow_nonneg hm0.le _), Real.log_rpow hm0,
      abs_of_nonneg (sq_nonneg _)] at hm'
    nlinarith [hm']
  have hN : ∀ d ≤ D, ∃ N : ℝ, ∀ m : ℝ, N ≤ m →
      (16 : ℝ) ≤ m ∧ c' / (cf d) ^ 2 ≤ Real.log m ∧
        (Real.log m) ^ 2 ≤ 64 * m ^ ((1 : ℝ) / 8) ∧
        max (64 : ℝ) (2 * cf d / c') ≤ m ^ ((1 : ℝ) / 8) ∧
        (Real.log m) ^ 2 ≤ c' * m ∧
        16 * (cf d + 1) * (cf d / Real.log 2 + 1) ^ 2 *
          (2 * (cf d / Real.log 2) + 1) ^ (2 * d) < m := by
    intro d _
    have ev16 : ∀ᶠ m : ℝ in Filter.atTop, (16 : ℝ) ≤ m :=
      Filter.eventually_ge_atTop 16
    have evlog : ∀ᶠ m : ℝ in Filter.atTop, c' / (cf d) ^ 2 ≤ Real.log m :=
      Real.tendsto_log_atTop.eventually_ge_atTop _
    have evpow : ∀ᶠ m : ℝ in Filter.atTop,
        max (64 : ℝ) (2 * cf d / c') ≤ m ^ ((1 : ℝ) / 8) :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually_ge_atTop _
    have evcm : ∀ᶠ m : ℝ in Filter.atTop, (Real.log m) ^ 2 ≤ c' * m := by
      filter_upwards
        [(Real.isLittleO_pow_log_id_atTop (n := 2)).bound hc'pos,
          Filter.eventually_gt_atTop (0 : ℝ)] with m hm hm0
      rwa [id_eq, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _), abs_of_pos hm0] at hm
    have evbig : ∀ᶠ m : ℝ in Filter.atTop,
        16 * (cf d + 1) * (cf d / Real.log 2 + 1) ^ 2 *
          (2 * (cf d / Real.log 2) + 1) ^ (2 * d) < m :=
      Filter.eventually_gt_atTop _
    exact Filter.eventually_atTop.mp
      (ev16.and (evlog.and (evLog.and (evpow.and (evcm.and evbig)))))
  refine ⟨c', (fun d ↦ if h : d ≤ D then Classical.choose (hN d h) else 0),
    hc'pos, ?_⟩
  intro d hd X B' hBi hsubX hBX hC₀
  set m : ℝ := (X.card : ℝ)
  have hCd : (fun d ↦ if h : d ≤ D then Classical.choose (hN d h) else 0) d =
      Classical.choose (hN d hd) := dif_pos hd
  obtain ⟨h16, hlog, hlog8, hp8, hlogcm, hbig⟩ :=
    Classical.choose_spec (hN d hd) m (hCd ▸ hC₀)
  have hmpos : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hlogm : (0 : ℝ) < Real.log m := Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < (Real.log m) ^ 2 := sq_pos_of_pos hlogm
  have h64 : (64 : ℝ) ≤ m ^ ((1 : ℝ) / 8) := le_trans (le_max_left _ _) hp8
  have h2cf : 2 * cf d / c' ≤ m ^ ((1 : ℝ) / 8) :=
    le_trans (le_max_right _ _) hp8
  have hlog4 : (Real.log m) ^ 2 ≤ m ^ ((1 : ℝ) / 4) := by
    have h18 : (0 : ℝ) ≤ m ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hmpos.le _
    have hmul : (64 : ℝ) * m ^ ((1 : ℝ) / 8)
        ≤ m ^ ((1 : ℝ) / 8) * m ^ ((1 : ℝ) / 8) :=
      mul_le_mul_of_nonneg_right h64 h18
    rw [← Real.rpow_add hmpos, show (1 : ℝ) / 8 + 1 / 8 = 1 / 4 by norm_num]
      at hmul
    linarith [hlog8]
  have hq14 : m ^ ((1 : ℝ) / 8) ≤ m ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hcf4 : 2 * cf d / c' ≤ m ^ ((1 : ℝ) / 4) := le_trans h2cf hq14
  set r : ℝ := (c' / cf d) * (m / (Real.log m) ^ 2) with hr
  set s : ℕ := ⌊r⌋₊ with hsdef
  have hr0 : (0 : ℝ) ≤ r := by
    rw [hr]
    exact mul_nonneg (div_nonneg hc'pos.le (hcf d).le)
      (div_nonneg hmpos.le (sq_nonneg _))
  have hcfne : cf d ≠ 0 := ne_of_gt (hcf d)
  have hc'ne : c' ≠ 0 := ne_of_gt hc'pos
  have hlogne : Real.log m ≠ 0 := ne_of_gt hlogm
  have hm34 : m ^ ((3 : ℝ) / 4) ≤ m / (Real.log m) ^ 2 := by
    have h1 : m / m ^ ((1 : ℝ) / 4) ≤ m / (Real.log m) ^ 2 :=
      div_le_div_of_nonneg_left hmpos.le hlog2 hlog4
    have heq : m / m ^ ((1 : ℝ) / 4) = m ^ ((3 : ℝ) / 4) := by
      rw [show (3 : ℝ) / 4 = 1 - 1 / 4 by norm_num, Real.rpow_sub hmpos,
        Real.rpow_one]
    rwa [heq] at h1
  have hrge : m ^ ((1 : ℝ) / 2) + 1 ≤ r := by
    have hcc : (0 : ℝ) ≤ c' / cf d := div_nonneg hc'pos.le (hcf d).le
    have he : m ^ ((3 : ℝ) / 4) = m ^ ((1 : ℝ) / 2) * m ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hmpos,
        show (1 : ℝ) / 2 + 1 / 4 = 3 / 4 by norm_num]
    have h1 : (c' / cf d) * m ^ ((3 : ℝ) / 4) ≤ r := by
      rw [hr]; exact mul_le_mul_of_nonneg_left hm34 hcc
    have h2 : (c' / cf d) * (m ^ ((1 : ℝ) / 2) * m ^ ((1 : ℝ) / 4)) ≥
        (c' / cf d) * (m ^ ((1 : ℝ) / 2) * (2 * cf d / c')) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcf4 (Real.rpow_nonneg hmpos.le _)) hcc
    have h3 : (c' / cf d) * (m ^ ((1 : ℝ) / 2) * (2 * cf d / c')) =
        2 * m ^ ((1 : ℝ) / 2) := by
      field_simp
    have h4 : (1 : ℝ) ≤ m ^ ((1 : ℝ) / 2) := Real.one_le_rpow hm1 (by norm_num)
    calc m ^ ((1 : ℝ) / 2) + 1 ≤ 2 * m ^ ((1 : ℝ) / 2) := by linarith
      _ = (c' / cf d) * (m ^ ((1 : ℝ) / 2) * (2 * cf d / c')) := h3.symm
      _ ≤ (c' / cf d) * (m ^ ((1 : ℝ) / 2) * m ^ ((1 : ℝ) / 4)) := h2
      _ = (c' / cf d) * m ^ ((3 : ℝ) / 4) := by rw [← he]
      _ ≤ r := h1
  have hs_ge : m ^ ((1 : ℝ) / 2) ≤ (s : ℝ) := by
    have h := Nat.lt_floor_add_one r
    rw [← hsdef] at h
    linarith [hrge]
  have hs1 : (s : ℝ) ≤ r := by
    have h := Nat.floor_le hr0
    rwa [← hsdef] at h
  have hs_le : (s : ℝ) ≤ cf d * m / Real.log m := by
    refine le_trans hs1 ?_
    have hstep : r ≤ cf d * m / Real.log m := by
      rw [hr, le_div_iff₀ hlogm]
      have e : (c' / cf d) * (m / (Real.log m) ^ 2) * Real.log m =
          (c' / (cf d) ^ 2 / Real.log m) * (cf d * m) := by
        field_simp
      rw [e]
      -- `c'/cf_d²/log m ≤ 1`, i.e. `c'/cf_d² ≤ log m` (`hlog`).
      have h1 : c' / (cf d) ^ 2 / Real.log m ≤ 1 :=
        (div_le_iff₀ hlogm).mpr (by simpa using hlog)
      calc (c' / (cf d) ^ 2 / Real.log m) * (cf d * m)
          ≤ 1 * (cf d * m) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg (hcf d).le hmpos.le)
        _ = cf d * m := one_mul _
    exact hstep
  have hXne : X.Nonempty :=
    Finset.card_pos.mp (Nat.cast_pos.mp (by linarith : (0 : ℝ) < m))
  obtain ⟨Â, d', P, hÂsub, hÂcard, hd'le, hPsym, hsub0, A', hA'sub, hA'card,
    k, hkpos, hkle, t, htrans, hprop⟩ :=
      hcfp d X B' s hXne hBi hsubX hBX hs_ge hs_le hbig
  have hcc2 : c' / (cf d) ^ 2 ≤ (c')⁻¹ := by
    rw [div_le_iff₀ (pow_pos (hcf d) 2), inv_mul_eq_div, le_div_iff₀ hc'pos]
    nlinarith [hc'le d hd, hcf d, hc'pos]
  -- The witness uses the coefficient-width scaling `P.widthScale k` returned
  -- by `cfp_structure`, dilated pointwise by `k' = 1` (so `1 • P.widthScale k
  -- = P.widthScale k` via `GAP.nsmul_eq_zsmul`/`GAP.one_smul'`).
  refine ⟨d', ?_, ⟨⟨Â, A', P.widthScale k, 1, t, hc'pos, Nat.one_pos, ?_,
    hÂsub, hA'sub, ?_, ?_,
    hsub0.trans (GAP.toFinset_subset_widthScale _ hkpos), ?_, ?_⟩⟩⟩
  · have : (d' : ℝ) ≤ (⌈df d⌉₊ : ℝ) := le_trans hd'le (Nat.le_ceil _)
    exact_mod_cast this
  · -- `hk` at `k' = 1`: `1 ≤ c'·s(X)` follows from `log² m ≤ c'·m`.
    rw [← mul_div_assoc]
    exact_mod_cast (one_le_div hlog2).mpr hlogcm
  · calc (A'.card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hA'card
      _ ≤ r := hs1
      _ ≤ m / (Real.log m) ^ 2 := by
          rw [hr]
          have hcc : c' / cf d ≤ 1 := by
            rw [div_le_iff₀ (hcf d), one_mul]; exact hc'le d hd
          calc (c' / cf d) * (m / (Real.log m) ^ 2)
              ≤ 1 * (m / (Real.log m) ^ 2) :=
                mul_le_mul_of_nonneg_right hcc
                  (div_nonneg hmpos.le (sq_nonneg _))
            _ = m / (Real.log m) ^ 2 := one_mul _
  · have hstep : (cf d)⁻¹ * (s : ℝ) * Real.log m ≤ c'⁻¹ * m / Real.log m := by
      calc (cf d)⁻¹ * (s : ℝ) * Real.log m
          ≤ (cf d)⁻¹ * r * Real.log m :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hs1 (inv_nonneg.mpr (hcf d).le))
              hlogm.le
        _ = (c' / (cf d) ^ 2) * m / Real.log m := by
            rw [hr]; field_simp; try ring
        _ ≤ c'⁻¹ * m / Real.log m := by
            have hmL : (0 : ℝ) ≤ m / Real.log m :=
              div_nonneg hmpos.le hlogm.le
            have h := mul_le_mul_of_nonneg_right hcc2 hmL
            rwa [← mul_div_assoc, ← mul_div_assoc] at h
    calc m - c'⁻¹ * m / Real.log m
        ≤ m - (cf d)⁻¹ * (s : ℝ) * Real.log m := sub_le_sub_left hstep _
      _ ≤ (Â.card : ℝ) := hÂcard
  · rw [GAP.nsmul_eq_zsmul, Nat.cast_one, GAP.one_smul']
    exact htrans
  · rw [GAP.nsmul_eq_zsmul, Nat.cast_one, GAP.one_smul']
    exact hprop

/-- **Uniform Cor-5 with bounded dimension** — a single `c'` that is a
Cor-5 constant for every `(d,β')`-class with `d ≤ D`, with witnesses
produced at a dimension `d' ≤ G d` where `G d = ⌈df d⌉₊` is the
per-class rank bound of `cfp_structure`.  `D` is chosen to dominate
`ℓ + G ℓ + F` — the ambient dimension `ℓ` plus the initial-witness rank
cap plus a caller-chosen reserve `F` (used for the iteration's
`sd ≤ ⌈(2ℓ+β+2)/(1-ε)⌉₊` dimension budget).  This is the faithful
repair of the earlier `d' ≤ d` formulation, which is false in general:
proper GAPs in `ℤ^d` can have rank exceeding `d`. -/
theorem uniform_cor5_bounded_exists {β' : ℝ} (hβ' : 1 < β') (F : ℕ) :
    ∃ (c' : ℝ) (G : ℕ → ℕ) (C₀ : ℕ → ℝ) (D : ℕ), 0 < c' ∧
      ℓ + G ℓ + F ≤ D ∧
      ∀ ⦃d : ℕ⦄, d ≤ D → ∀ {X : Finset (Fin d → ℤ)} {B' : GAP.Box d},
        B'.IsInterval → X ⊆ B'.toFinset →
        (B'.card : ℝ) ≤ (X.card : ℝ) ^ β' → (C₀ d : ℝ) ≤ (X.card : ℝ) →
        ∃ d' ≤ G d, Nonempty (SubSumWitness X c' d') := by
  obtain ⟨cf, df, hcf, hcfp⟩ := cfp_structure_family hβ'
  obtain ⟨c', C₀, hc', hval⟩ :=
    uniform_cor5_of_family hβ' hcf hcfp (ℓ + ⌈df ℓ⌉₊ + F)
  exact ⟨c', fun d ↦ ⌈df d⌉₊, C₀, ℓ + ⌈df ℓ⌉₊ + F, hc', le_refl _, hval⟩

/-- A stage of the Lemma-10 iteration: a derived set `X` together with
its canonical `c'`-witness `W` and the running bookkeeping.  `nd`, `nu`,
`ns` count the down/up/shrink moves; `sd`, `sdd` accumulate the
dimension increments `d_{j+1} − d_j` and decrements `d_j − d_{j+1}`.
The invariants are `δ^{nd+nu+ns}·|A| ≤ |X|`,
`|P(X)| ≤ C₆₈^{nd+nu}·γ^{ns}·sMin^{−sd}·P₀` (eq. (8)) and
`d(X) = dinit + sd − sdd` (dimension conservation). -/
structure L10Stage (A : Finset (Fin ℓ → ℤ)) (δ ε γ : ℝ) (c' : ℝ) (D : ℕ)
    (sMin C₆₈ P0 : ℝ) (dinit : ℕ) where
  n : ℕ
  X : Finset (Fin n → ℤ)
  der : DerivedFrom A δ X
  W : SubSumWitness X c' (SubSumDim X c')
  dim : SubSumDim X c' ≤ D
  size : (A.card : ℝ) ^ (1 - ε / 2) ≤ (X.card : ℝ)
  nd : ℕ
  nu : ℕ
  ns : ℕ
  sd : ℕ
  sdd : ℕ
  hsz : (δ : ℝ) ^ (nd + nu + ns) * (A.card : ℝ) ≤ (X.card : ℝ)
  hPb : (W.P.toFinset.card : ℝ) ≤
      C₆₈ ^ (nd + nu : ℕ) * γ ^ (ns : ℕ) * sMin ^ (-(sd : ℝ)) * P0
  hdim : (SubSumDim X c' : ℤ) = (dinit : ℤ) + (sd : ℤ) - (sdd : ℤ)
  hnu : nu ≤ sd
  hnd : nd ≤ sdd

/-- The descent potential `Φ = log|P| + t·d` at the canonical witness,
with `t = log sMin / 2`. -/
noncomputable def L10Stage.pot {A : Finset (Fin ℓ → ℤ)} {δ ε γ : ℝ}
    {c' : ℝ} {D : ℕ} {sMin C₆₈ P0 : ℝ} {dinit : ℕ}
    (s : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit) : ℝ :=
  Real.log (s.W.P.toFinset.card : ℝ) +
    (Real.log sMin / 2) * (SubSumDim s.X c' : ℝ)

/-- The strict-decrease gap `η = min(t − log C₆₈, −log γ)` of the
potential: every move drops `Φ` by at least `η`. -/
noncomputable def L10η (γ sMin C₆₈ : ℝ) : ℝ :=
  min (Real.log sMin / 2 - Real.log C₆₈) (-Real.log γ)

theorem L10η_pos {γ sMin C₆₈ : ℝ} (hC₆₈ : 0 < C₆₈) (hsMin : 1 < sMin)
    (hCs : C₆₈ ^ 2 < sMin) (hγ : 0 < γ) (hγ1 : γ < 1) :
    0 < L10η γ sMin C₆₈ := by
  have hls : 0 < Real.log sMin := Real.log_pos hsMin
  have hlg : Real.log γ < 0 := Real.log_neg hγ hγ1
  have h2 : 2 * Real.log C₆₈ < Real.log sMin := by
    have h := Real.log_lt_log (show (0:ℝ) < C₆₈ ^ 2 by positivity) hCs
    rwa [Real.log_pow] at h
  unfold L10η
  rw [lt_min_iff]
  exact ⟨by linarith, by linarith⟩

/-- The `ℕ`-valued measure `⌈Φ/η⌉`: strictly descending along moves. -/
noncomputable def L10Stage.μ {A : Finset (Fin ℓ → ℤ)} {δ ε γ : ℝ}
    {c' : ℝ} {D : ℕ} {sMin C₆₈ P0 : ℝ} {dinit : ℕ}
    (s : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit) : ℕ :=
  ⌈s.pot / L10η γ sMin C₆₈⌉₊

/-- If `Φ' ≤ Φ − η` and `Φ > 0` then `μ' < μ`. -/
theorem L10Stage.μ_lt {A : Finset (Fin ℓ → ℤ)} {δ ε γ : ℝ} {c' : ℝ}
    {D : ℕ} {sMin C₆₈ P0 : ℝ} {dinit : ℕ}
    {s s' : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit}
    (hη : 0 < L10η γ sMin C₆₈)
    (hdrop : s'.pot ≤ s.pot - L10η γ sMin C₆₈) (hpos : 0 < s.pot) :
    s'.μ < s.μ := by
  have hμ : 0 < s.μ := Nat.ceil_pos.mpr (div_pos hpos hη)
  have hle : s'.pot / L10η γ sMin C₆₈ ≤ ((s.μ - 1 : ℕ) : ℝ) := by
    have h1 : s.pot / L10η γ sMin C₆₈ ≤ (s.μ : ℝ) := Nat.le_ceil _
    have h2 : s'.pot / L10η γ sMin C₆₈ ≤
        s.pot / L10η γ sMin C₆₈ - 1 := by
      have h3 := div_le_div_of_nonneg_right hdrop hη.le
      rwa [sub_div, div_self (ne_of_gt hη)] at h3
    have h4 : ((s.μ - 1 : ℕ) : ℝ) = (s.μ : ℝ) - 1 :=
      Nat.cast_pred hμ
    rw [h4]; linarith
  have hle2 : s'.μ ≤ s.μ - 1 := by
    unfold L10Stage.μ
    rw [Nat.ceil_le]
    exact hle
  omega

/-- **Size-stop exclusion** (eq. (10)): a move cannot land below the
running threshold `|A|^{1−ε/2}`.  From `δ^{i+1}|A| ≤ |X'| < |A|^{1−ε/2}`
the move count is `i + 1 ≥ ε·log|A| / (2·log(1/δ))`; the eq.-(8) bound
`|P'| ≤ C₆₈^{nd+nu}·γ^{ns}·sMin^{−sd}·P₀` with `|P'| ≥ 1` and the count
bounds `nd ≤ dinit + sd`, `nu ≤ sd` then give
`ns·log(1/γ) ≤ O_β(log|A|)`, hence `γ^{i−O_β(1)} ≤ |A|^{O_β(1)}` —
contradicting `γ ≤ δ^K` once `K ≥ C_{β,ε}` (`hKbig`, the threshold the
ambient hypotheses do not supply).

**Status note (round 6, superseded).**  The hypotheses `hsMinA`
(`sMin ≥ |A|^{1−ε}` — the paper's `s(A_j) ≥ |A|^{1−ε}` bookkeeping),
`hP0` (`P0 ≤ |A|^{2ℓ+β+2}`), the strict `hKbig` (`K > 2(2ℓ+β+2)/ε`)
and the largeness `hLarg` (`K·log(1/δ)·Q ≤ (Kε/2−(2ℓ+β+2))·log|A|`,
with `Q` an upper bound on the initial dimension `dinit`) make the
contradiction derivable — this lemma is now fully proved.  `Q` is a
parameter so that the caller can feed the global cap `D` (the initial
witness is only known to satisfy `dinit ≤ G ℓ`, not `dinit ≤ ℓ`). -/
theorem size_stop_absurd {A : Finset (Fin ℓ → ℤ)} {δ ε γ K : ℝ} {β : ℝ}
    {c' sMin C₆₈ : ℝ} {d' : ℕ} {X' : Finset (Fin d' → ℤ)}
    {nd nu ns sd dinit : ℕ} {W' : SubSumWitness X' c' (SubSumDim X' c')}
    {P0 : ℝ} {Q : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hε3 : ε < 1 / 3) (hγ : 0 < γ)
    (hγδ : γ ≤ δ ^ K)
    (hKbig : (2 : ℝ) * (2 * ℓ + β + 2) / ε < K) (hβ : 1 < β)
    (hC₆₈ : 0 < C₆₈) (hC₆₈1 : C₆₈ ≤ 1) (hsMin : 1 < sMin)
    (hsMinA : (A.card : ℝ) ^ (1 - ε) ≤ sMin)
    (hδA : (1 / δ) ^ (2 * K) ≤ (A.card : ℝ) ^ (1 - ε))
    (hLarg : K * Real.log (1 / δ) * Q ≤
        (K * ε / 2 - (2 * ℓ + β + 2)) * Real.log (A.card : ℝ))
    (hsize : (δ : ℝ) ^ (nd + nu + ns) * (A.card : ℝ) ≤ (X'.card : ℝ))
    (hsmall : (X'.card : ℝ) < (A.card : ℝ) ^ (1 - ε / 2))
    (hPb : (W'.P.toFinset.card : ℝ) ≤
        C₆₈ ^ (nd + nu : ℕ) * γ ^ (ns : ℕ) * sMin ^ (-(sd : ℝ)) * P0)
    (hP0 : P0 ≤ (A.card : ℝ) ^ (2 * ℓ + β + 2))
    (hP1 : (1 : ℝ) ≤ (W'.P.toFinset.card : ℝ))
    (hnd : (nd : ℝ) ≤ dinit + sd) (hnu : nu ≤ sd)
    (hdinit : (dinit : ℝ) ≤ Q) :
    False := by
  set L := Real.log (A.card : ℝ) with hL
  set t := Real.log (1 / δ) with ht
  -- `|A| ≥ 1` (else `|X'| < 0`).
  have hApos : (0 : ℝ) < (A.card : ℝ) := by
    by_contra h0
    push_neg at h0
    have hz : (A.card : ℝ) = 0 := le_antisymm h0 (Nat.cast_nonneg _)
    rw [hz, Real.zero_rpow (show (1 : ℝ) - ε / 2 ≠ 0 by linarith)] at hsmall
    exact not_lt.mpr (Nat.cast_nonneg _) hsmall
  have hA1 : (1 : ℝ) ≤ (A.card : ℝ) := by
    have h1 : 1 ≤ A.card := by
      rcases Nat.eq_zero_or_pos A.card with h | h
      · exfalso; rw [h, Nat.cast_zero] at hApos; exact lt_irrefl _ hApos
      · exact h
    exact_mod_cast h1
  -- `δ < 1` (else `|A| ≤ δ^M·|A| ≤ |X'| < |A|^{1-ε/2} ≤ |A|`).
  have hδ1 : δ < 1 := by
    by_contra h1
    push_neg at h1
    have hM : (1 : ℝ) ≤ δ ^ (nd + nu + ns) := one_le_pow₀ h1
    have hle : (A.card : ℝ) ≤ δ ^ (nd + nu + ns) * (A.card : ℝ) := by
      calc (A.card : ℝ) = 1 * (A.card : ℝ) := (one_mul _).symm
        _ ≤ δ ^ (nd + nu + ns) * (A.card : ℝ) :=
          mul_le_mul_of_nonneg_right hM hApos.le
    have hle2 : (A.card : ℝ) ^ (1 - ε / 2) ≤ (A.card : ℝ) := by
      calc (A.card : ℝ) ^ (1 - ε / 2)
          ≤ (A.card : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
        _ = (A.card : ℝ) := Real.rpow_one _
    linarith [hsize, hsmall, hle, hle2]
  have ht0 : (0 : ℝ) < t := by
    rw [ht]
    exact Real.log_pos ((one_lt_div hδ).mpr hδ1)
  -- `|A| ≥ 2` (the `|A| = 1` case gives `δ^M ≤ |X'| < 1`, impossible).
  have hA2 : (2 : ℝ) ≤ (A.card : ℝ) := by
    by_contra h2
    push_neg at h2
    have hA1n : 1 ≤ A.card := by exact_mod_cast hA1
    have hlt : A.card < 2 := by exact_mod_cast h2
    have hAeq : A.card = 1 := by omega
    have hAeqr : (A.card : ℝ) = 1 := by exact_mod_cast hAeq
    rw [hAeqr, Real.one_rpow] at hsmall
    have hX0 : X'.card = 0 := by
      by_contra hc
      have : (1 : ℝ) ≤ (X'.card : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
      linarith
    have hXr : (X'.card : ℝ) = 0 := by exact_mod_cast hX0
    rw [hAeqr, hXr] at hsize
    have hδM : (0 : ℝ) < δ ^ (nd + nu + ns) := pow_pos hδ _
    linarith [hsize, hδM]
  have hL0 : (0 : ℝ) < L := by
    rw [hL]; exact Real.log_pos (by linarith : (1 : ℝ) < (A.card : ℝ))
  have hβnn : (0 : ℝ) ≤ 2 * ℓ + β + 2 := by
    have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
    linarith
  have hK0 : (0 : ℝ) < K := by
    have h1 : (0 : ℝ) ≤ 2 * (2 * ℓ + β + 2) / ε :=
      div_nonneg (by linarith [hβnn]) hε.le
    linarith [hKbig]
  have hlogδ : Real.log δ = -t := by
    rw [ht, one_div, Real.log_inv, neg_neg]
  have hlogγ : Real.log γ ≤ K * Real.log δ := by
    have h := Real.log_le_log hγ hγδ
    rwa [Real.log_rpow hδ] at h
  have hlogC : Real.log C₆₈ ≤ 0 := Real.log_nonpos hC₆₈.le hC₆₈1
  have hlogs : (1 - ε) * L ≤ Real.log sMin := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hApos _) hsMinA
    rwa [Real.log_rpow hApos, ← hL] at h
  have hC3 : 2 * K * t ≤ (1 - ε) * L := by
    have hpos' : (0 : ℝ) < (1 / δ) ^ (2 * K) :=
      Real.rpow_pos_of_pos (by positivity) _
    have h := Real.log_le_log hpos' hδA
    rw [Real.log_rpow (by positivity : (0 : ℝ) < 1 / δ),
      Real.log_rpow hApos, ← ht, ← hL] at h
    exact h
  have hP0pos : (0 : ℝ) < P0 := by
    by_contra hp
    push_neg at hp
    have hsMinpos : (0 : ℝ) < sMin := lt_trans zero_lt_one hsMin
    have hfac : (0 : ℝ) ≤ C₆₈ ^ (nd + nu) * γ ^ ns * sMin ^ (-(sd : ℝ)) := by
      positivity
    have : C₆₈ ^ (nd + nu) * γ ^ ns * sMin ^ (-(sd : ℝ)) * P0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfac hp
    linarith [hP1, hPb]
  have hlogP0 : Real.log P0 ≤ (2 * ℓ + β + 2) * L := by
    have h := Real.log_le_log hP0pos hP0
    rwa [Real.log_rpow hApos, ← hL] at h
  -- Taking logs in `1 ≤ C₆₈^{nd+nu}·γ^ns·sMin^{-sd}·P0` gives eq. (8):
  -- `ns·K·t + sd·log sMin ≤ (2ℓ+β+2)·L`.
  have hprod : (0 : ℝ) ≤ ((nd + nu : ℕ) : ℝ) * Real.log C₆₈ +
      (ns : ℝ) * Real.log γ - (sd : ℝ) * Real.log sMin + Real.log P0 := by
    have h1 : (1 : ℝ) ≤
        C₆₈ ^ (nd + nu) * γ ^ ns * sMin ^ (-(sd : ℝ)) * P0 :=
      le_trans hP1 hPb
    have hlog := Real.log_nonneg h1
    have hCpos : (0 : ℝ) < C₆₈ ^ (nd + nu) := pow_pos hC₆₈ _
    have hγpos : (0 : ℝ) < γ ^ ns := pow_pos hγ _
    have hspos : (0 : ℝ) < sMin ^ (-(sd : ℝ)) :=
      Real.rpow_pos_of_pos (by linarith) _
    rw [Real.log_mul (ne_of_gt (mul_pos (mul_pos hCpos hγpos) hspos))
        (ne_of_gt hP0pos),
      Real.log_mul (ne_of_gt (mul_pos hCpos hγpos)) (ne_of_gt hspos),
      Real.log_mul (ne_of_gt hCpos) (ne_of_gt hγpos),
      Real.log_pow, Real.log_pow,
      Real.log_rpow (by linarith : (0 : ℝ) < sMin)] at hlog
    push_cast at hlog ⊢
    linarith [hlog]
  have key : (ns : ℝ) * K * t + (sd : ℝ) * Real.log sMin ≤
      (2 * ℓ + β + 2) * L := by
    have hUlog : ((nd + nu : ℕ) : ℝ) * Real.log C₆₈ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hlogC
    have hnsγ : (ns : ℝ) * Real.log γ ≤ -((ns : ℝ) * K * t) := by
      have hKδ : K * Real.log δ = -(K * t) := by rw [hlogδ]; ring
      have h1 : Real.log γ ≤ -(K * t) := by linarith [hlogγ]
      calc (ns : ℝ) * Real.log γ ≤ (ns : ℝ) * (-(K * t)) :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg ns)
        _ = -((ns : ℝ) * K * t) := by ring
    linarith [hprod, hUlog, hnsγ, hlogP0]
  -- Taking logs in `δ^{nd+nu+ns}·|A| < |A|^{1-ε/2}`:
  -- `(nd+nu+ns)·t > (ε/2)·L`.
  have hsz : δ ^ (nd + nu + ns) * (A.card : ℝ) < (A.card : ℝ) ^ (1 - ε / 2) :=
    lt_of_le_of_lt hsize hsmall
  have hsplit : (A.card : ℝ) ^ (1 - ε / 2) =
      (A.card : ℝ) * (A.card : ℝ) ^ (-(ε / 2)) := by
    rw [show (1 : ℝ) - ε / 2 = 1 + -(ε / 2) by ring,
      Real.rpow_add hApos, Real.rpow_one]
  have hδpow : δ ^ (nd + nu + ns) < (A.card : ℝ) ^ (-(ε / 2)) := by
    rw [hsplit, mul_comm (A.card : ℝ) _] at hsz
    exact (mul_lt_mul_iff_left₀ hApos).mp hsz
  have htM : (ε / 2) * L < ((nd : ℝ) + (nu : ℝ) + (ns : ℝ)) * t := by
    have hposδ : (0 : ℝ) < δ ^ (nd + nu + ns) := pow_pos hδ _
    have h' := Real.log_lt_log hposδ hδpow
    rw [Real.log_pow, Real.log_rpow hApos, hlogδ, ← hL] at h'
    push_cast at h'
    linarith [h']
  -- Multiply by `K`, use `nd + nu ≤ dinit + 2·sd` and combine with `key`.
  have hnslb : K * ((ε / 2) * L - ((nd : ℝ) + (nu : ℝ)) * t) <
      K * ((ns : ℝ) * t) := by
    have h1 : (ε / 2) * L - ((nd : ℝ) + (nu : ℝ)) * t < (ns : ℝ) * t := by
      linarith [htM]
    exact mul_lt_mul_of_pos_left h1 hK0
  have hnd' : ((nd : ℝ) + (nu : ℝ)) ≤ (dinit : ℝ) + 2 * (sd : ℝ) := by
    have hnur : (nu : ℝ) ≤ (sd : ℝ) := by exact_mod_cast hnu
    linarith [hnd]
  have hKUt : K * ((nd : ℝ) + (nu : ℝ)) * t ≤
      K * ((dinit : ℝ) + 2 * (sd : ℝ)) * t := by
    have hKt0 : (0 : ℝ) ≤ K * t := mul_nonneg hK0.le ht0.le
    have h2 : (0 : ℝ) ≤
        (K * t) * ((dinit : ℝ) + 2 * (sd : ℝ) - ((nd : ℝ) + (nu : ℝ))) :=
      mul_nonneg hKt0 (by linarith [hnd'])
    linarith [h2]
  have hstep : (ε / 2) * K * L + (sd : ℝ) * (Real.log sMin - 2 * K * t) <
      K * t * (dinit : ℝ) + (2 * ℓ + β + 2) * L := by
    linarith [key, hnslb, hKUt]
  have hsd0 : (0 : ℝ) ≤ (sd : ℝ) * (Real.log sMin - 2 * K * t) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [hlogs, hC3])
  have hKtQ : K * t * (dinit : ℝ) ≤ K * t * Q :=
    mul_le_mul_of_nonneg_left hdinit (mul_nonneg hK0.le ht0.le)
  -- `(ε/2)·K·L < K·t·Q + (2ℓ+β+2)·L ≤ (K·ε/2)·L`, a contradiction.
  have hcontra : (ε / 2) * K * L < (K * ε / 2) * L := by
    linarith [hstep, hsd0, hKtQ, hLarg]
  have heq : (ε / 2) * K * L = (K * ε / 2) * L := by ring
  linarith [hcontra, heq]

/-- **Final `|P̃|` bounds** (eq. (10) chained with the initial bound):
at the terminal stage the accumulated multiplier
`C₆₈^{nd+nu}·γ^{ns}·sMin^{−sd}` composed with
`|P₀| ≤ C₆₈·sMin^{−max(0,dinit−ℓ)}·|B|` gives the three bounds —
`|P̃| ≲ |A|^{−(1−ε)(dt−ℓ)}·|B|` for `dt > ℓ` (each net dimension increase
costs a factor `sMin^{-1}` paid for by the `|A|^{−(1−ε)}` shrink),
`|P̃| ≲ (|Ã|/|A|)^K·|B|` for `dt = ℓ` (all moves were shrink-moves), and
`|P̃| ≲ |B|` for `dt < ℓ`.

**Status note (round 6).**  Not derivable from the recorded invariants:
`C₆₈^{nd+nu}` is uncontrolled (no `C₆₈² < sMin` here), `sMin^{-sd}` cannot
deliver `|A|^{-(1-ε)(dt-ℓ)}` since `sMin` is a constant rather than
`≈ |A|^{1-ε}`, and the `dt = ℓ` bound needs `δ^{ns} ≤ |X̃|/|A|` while
`s.hsz` only controls `δ^{nd+nu+ns}` jointly (the `nd + nu > 0` slack is
not absorbable: `ns = 0`, `nu = 1`, `sd = sdd = 1`, `dinit = ℓ` is a
legal stage with `|X̃|/|A| = δ`, where `hPb` gives `|P̃| ≤ sMin^{-1}|B|`
but the goal wants `|P̃| ≤ C₆₈·δ^K·|B|`). -/
theorem final_P_bounds {A : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ}
    {δ ε γ K : ℝ} {c' sMin C₆₈ : ℝ} {β β' : ℝ} {D : ℕ} {P0 : ℝ} {dinit : ℕ}
    (s : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit)
    (hβ : 1 < β) (hε : 0 < ε) (hε3 : ε < 1 / 3) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hγ : 0 < γ) (hγδ : γ ≤ δ ^ K)
    (hKbig : (2 : ℝ) * (2 * ℓ + β + 2) / ε < K)
    (hC₆₈ : 0 < C₆₈) (hC₆₈1 : C₆₈ ≤ 1) (hsMin : 1 < sMin)
    (hA1 : (1 : ℝ) ≤ (A.card : ℝ))
    (hsMinA : (A.card : ℝ) ^ (1 - ε) ≤ sMin)
    (hδsMin : (1 / δ) ^ (2 * K) ≤ sMin)
    (hBβ : (B.card : ℝ) ≤ (A.card : ℝ) ^ β)
    (hinit : P0 ≤
      C₆₈ * sMin ^ (-(max 0 ((dinit : ℝ) - (ℓ : ℝ)))) * (B.card : ℝ)) :
    (ℓ < SubSumDim s.X c' → (s.W.P.toFinset.card : ℝ) ≤
        C₆₈ * (A.card : ℝ) ^ (-(1 - ε) * ((SubSumDim s.X c' : ℝ) - ℓ))
          * (B.card : ℝ)) ∧
    (SubSumDim s.X c' = ℓ → (s.W.P.toFinset.card : ℝ) ≤
        C₆₈ * ((s.X.card : ℝ) / (A.card : ℝ)) ^ K * (B.card : ℝ)) ∧
    (SubSumDim s.X c' < ℓ → (s.W.P.toFinset.card : ℝ) ≤
        C₆₈ * (B.card : ℝ)) := by
  set m : ℝ := max 0 ((dinit : ℝ) - (ℓ : ℝ)) with hm
  set dt : ℕ := SubSumDim s.X c' with hdt
  set U : ℕ := s.nd + s.nu with hU
  have hβ0 : (0 : ℝ) < β := by linarith
  have hsMinpos : (0 : ℝ) < sMin := lt_trans zero_lt_one hsMin
  have hK0 : (0 : ℝ) < K := by
    have h1 : (0 : ℝ) < 2 * (2 * ℓ + β + 2) / ε := by positivity
    linarith [hKbig]
  have hApos : (0 : ℝ) < (A.card : ℝ) := by linarith [hA1]
  have hXpos : (0 : ℝ) < (s.X.card : ℝ) := by
    have h1 : (0 : ℝ) < (A.card : ℝ) ^ (1 - ε / 2) :=
      Real.rpow_pos_of_pos hApos _
    linarith [s.size]
  have hγ1 : γ ≤ 1 :=
    le_trans hγδ (Real.rpow_le_one hδ.le hδ1.le hK0.le)
  have hC₆₈U : C₆₈ ^ U ≤ 1 := pow_le_one₀ hC₆₈.le hC₆₈1
  have hγns : γ ^ s.ns ≤ 1 := pow_le_one₀ hγ.le hγ1
  have hsMin0 : (0 : ℝ) < sMin := by linarith
  have hspos : (0 : ℝ) < sMin ^ (-(s.sd : ℝ)) :=
    Real.rpow_pos_of_pos hsMin0 _
  have hm0 : (0 : ℝ) ≤ m := le_max_left _ _
  have hexp0 : -((s.sd : ℝ) + m) ≤ 0 := by
    have hs0 : (0 : ℝ) ≤ (s.sd : ℝ) := Nat.cast_nonneg _
    linarith
  -- Master bound: chain the progression bound with the initial bound.
  have hP0pos : (0 : ℝ) < P0 := by
    by_contra hp
    push_neg at hp
    have hfac : (0 : ℝ) ≤ C₆₈ ^ U * γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) := by
      positivity
    have : C₆₈ ^ U * γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) * P0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfac hp
    linarith [s.hPb, s.W.one_le_card_P]
  have hmaster : (s.W.P.toFinset.card : ℝ) ≤
      C₆₈ * (γ ^ s.ns * sMin ^ (-((s.sd : ℝ) + m))) * (B.card : ℝ) := by
    have hfac : C₆₈ ^ U * γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) ≤
        γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) := by
      have hpos : (0 : ℝ) ≤ γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) := by positivity
      calc C₆₈ ^ U * γ ^ s.ns * sMin ^ (-(s.sd : ℝ))
          = C₆₈ ^ U * (γ ^ s.ns * sMin ^ (-(s.sd : ℝ))) := by ring
        _ ≤ 1 * (γ ^ s.ns * sMin ^ (-(s.sd : ℝ))) :=
            mul_le_mul_of_nonneg_right hC₆₈U hpos
        _ = γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) := one_mul _
    have h1 : (s.W.P.toFinset.card : ℝ) ≤
        γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) * P0 :=
      le_trans s.hPb (mul_le_mul_of_nonneg_right hfac hP0pos.le)
    have hpos2 : (0 : ℝ) ≤ γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) := by positivity
    have h2 : γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) * P0 ≤
        γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) *
          (C₆₈ * sMin ^ (-m) * (B.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hinit hpos2
    have h3 : γ ^ s.ns * sMin ^ (-(s.sd : ℝ)) *
          (C₆₈ * sMin ^ (-m) * (B.card : ℝ))
        = C₆₈ * (γ ^ s.ns * sMin ^ (-((s.sd : ℝ) + m))) * (B.card : ℝ) := by
      rw [show -((s.sd : ℝ) + m) = -(s.sd : ℝ) + -m by ring,
        Real.rpow_add hsMin0]
      ring
    rw [h3] at h2
    exact le_trans h1 h2
  -- The γ-free version (using `γ^ns ≤ 1`).
  have hmaster' : (s.W.P.toFinset.card : ℝ) ≤
      C₆₈ * sMin ^ (-((s.sd : ℝ) + m)) * (B.card : ℝ) := by
    have h1 : γ ^ s.ns * sMin ^ (-((s.sd : ℝ) + m)) ≤
        sMin ^ (-((s.sd : ℝ) + m)) := by
      calc γ ^ s.ns * sMin ^ (-((s.sd : ℝ) + m))
          ≤ 1 * sMin ^ (-((s.sd : ℝ) + m)) :=
            mul_le_mul_of_nonneg_right hγns (Real.rpow_nonneg hsMin0.le _)
        _ = sMin ^ (-((s.sd : ℝ) + m)) := one_mul _
    calc (s.W.P.toFinset.card : ℝ)
        ≤ C₆₈ * (γ ^ s.ns * sMin ^ (-((s.sd : ℝ) + m))) * (B.card : ℝ) :=
          hmaster
      _ ≤ C₆₈ * sMin ^ (-((s.sd : ℝ) + m)) * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 hC₆₈.le) (Nat.cast_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · -- `dt > ℓ`: each net dimension increase costs a factor `sMin^{-1}`,
    -- and `sMin ≥ |A|^{1-ε}` converts this into `|A|^{-(1-ε)(dt-ℓ)}`.
    intro hlt
    have hdimr : (dt : ℝ) = (dinit : ℝ) + (s.sd : ℝ) - (s.sdd : ℝ) := by
      have h := congrArg (fun z : ℤ ↦ (z : ℝ)) s.hdim
      push_cast at h
      exact h
    have hdle : (dt : ℝ) - ℓ ≤ (s.sd : ℝ) + m := by
      have hmge : (dinit : ℝ) - ℓ ≤ m := le_max_right _ _
      have hsdd0 : (0 : ℝ) ≤ (s.sdd : ℝ) := Nat.cast_nonneg _
      linarith [hdimr]
    have h1ε : (0 : ℝ) < 1 - ε := by linarith
    have hstep1 : sMin ^ (-((s.sd : ℝ) + m)) ≤
        ((A.card : ℝ) ^ (1 - ε)) ^ (-((s.sd : ℝ) + m)) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hApos _) hsMinA hexp0
    rw [← Real.rpow_mul hApos.le] at hstep1
    have hex : (1 - ε) * -((s.sd : ℝ) + m) ≤
        -(1 - ε) * ((dt : ℝ) - ℓ) := by
      have hmul := mul_le_mul_of_nonneg_left hdle h1ε.le
      linarith [hmul]
    have hstep3 : (A.card : ℝ) ^ ((1 - ε) * -((s.sd : ℝ) + m)) ≤
        (A.card : ℝ) ^ (-(1 - ε) * ((dt : ℝ) - ℓ)) :=
      Real.rpow_le_rpow_of_exponent_le hA1 hex
    calc (s.W.P.toFinset.card : ℝ)
        ≤ C₆₈ * sMin ^ (-((s.sd : ℝ) + m)) * (B.card : ℝ) := hmaster'
      _ ≤ C₆₈ * (A.card : ℝ) ^ (-(1 - ε) * ((dt : ℝ) - ℓ)) * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (le_trans hstep1 hstep3) hC₆₈.le) (Nat.cast_nonneg _)
  · -- `dt = ℓ`: `γ^ns ≤ (|X̃|/|A|)^K·δ^{-UK}` and `δ^{-UK} ≤ sMin^{sd+m}`
    -- since `nd + nu ≤ sdd + sd = 2·sd + (dinit - ℓ) ≤ 2·sd + m`.
    intro heq
    have hδUp : (0 : ℝ) < δ ^ U := pow_pos hδ _
    have hsz : δ ^ U * δ ^ s.ns * (A.card : ℝ) ≤ (s.X.card : ℝ) := by
      have h := s.hsz
      rw [pow_add] at h
      exact h
    have hδns : δ ^ s.ns ≤
        ((s.X.card : ℝ) / (A.card : ℝ)) * (δ ^ U)⁻¹ := by
      have h2 : δ ^ s.ns ≤ (s.X.card : ℝ) / (δ ^ U * (A.card : ℝ)) := by
        rw [le_div_iff₀ (mul_pos hδUp hApos)]
        calc δ ^ s.ns * (δ ^ U * (A.card : ℝ))
            = δ ^ U * δ ^ s.ns * (A.card : ℝ) := by ring
          _ ≤ (s.X.card : ℝ) := hsz
      calc δ ^ s.ns ≤ (s.X.card : ℝ) / (δ ^ U * (A.card : ℝ)) := h2
        _ = ((s.X.card : ℝ) / (A.card : ℝ)) * (δ ^ U)⁻¹ := by
            rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
            ring
    -- `γ^ns ≤ δ^{K·ns} = (δ^ns)^K ≤ (|X̃|/|A|)^K·δ^{-UK}`.
    have hγδns : γ ^ s.ns ≤
        ((s.X.card : ℝ) / (A.card : ℝ)) ^ K * δ ^ (-(U : ℝ) * K) := by
      have h1 : γ ^ s.ns ≤ (δ ^ K) ^ s.ns :=
        pow_le_pow_left₀ hγ.le hγδ _
      have h2 : (δ ^ K) ^ (s.ns : ℕ) = δ ^ (K * (s.ns : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      have h3 : δ ^ (K * (s.ns : ℝ)) = (δ ^ s.ns) ^ K := by
        rw [mul_comm K, Real.rpow_mul hδ.le, Real.rpow_natCast]
      have h4 : (δ ^ s.ns) ^ K ≤
          (((s.X.card : ℝ) / (A.card : ℝ)) * (δ ^ U)⁻¹) ^ K :=
        Real.rpow_le_rpow (pow_nonneg hδ.le _) hδns hK0.le
      have h5 : (((s.X.card : ℝ) / (A.card : ℝ)) * (δ ^ U)⁻¹) ^ K =
          ((s.X.card : ℝ) / (A.card : ℝ)) ^ K * ((δ ^ U)⁻¹) ^ K :=
        Real.mul_rpow (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (inv_nonneg.mpr (pow_nonneg hδ.le _))
      have h6 : ((δ ^ U)⁻¹) ^ K = δ ^ (-(U : ℝ) * K) := by
        rw [← Real.rpow_natCast δ U, ← Real.rpow_neg hδ.le,
          ← Real.rpow_mul hδ.le]
      rw [h2, h3] at h1
      rw [h5, h6] at h4
      exact le_trans h1 h4
    have hsddr : (s.sdd : ℝ) = (dinit : ℝ) + (s.sd : ℝ) - (ℓ : ℝ) := by
      have h := s.hdim
      rw [heq] at h
      have h2 : (s.sdd : ℤ) = (dinit : ℤ) + (s.sd : ℤ) - (ℓ : ℤ) := by omega
      have h3 := congrArg (fun z : ℤ ↦ (z : ℝ)) h2
      push_cast at h3
      exact h3
    have hUle : (U : ℝ) ≤ 2 * (s.sd : ℝ) + m := by
      have hnu : (s.nu : ℝ) ≤ (s.sd : ℝ) := by exact_mod_cast s.hnu
      have hnd : (s.nd : ℝ) ≤ (s.sdd : ℝ) := by exact_mod_cast s.hnd
      have hmge : (dinit : ℝ) - (ℓ : ℝ) ≤ m := le_max_right _ _
      have hUr : (U : ℝ) = (s.nd : ℝ) + (s.nu : ℝ) := by simp [hU]
      linarith [hsddr, hmge, hnu, hnd, hUr]
    have h1δ : (1 : ℝ) ≤ 1 / δ := (one_le_div hδ).mpr hδ1.le
    have hUK : (U : ℝ) * K ≤ 2 * K * ((s.sd : ℝ) + m) := by
      have h := mul_le_mul_of_nonneg_right hUle hK0.le
      have hmge0 : (0 : ℝ) ≤ m := le_max_left _ _
      linarith [h, mul_nonneg hK0.le hmge0]
    have hδinv : δ ^ (-(U : ℝ) * K) = (1 / δ) ^ ((U : ℝ) * K) := by
      rw [show (-(U : ℝ) * K) = (-1) * ((U : ℝ) * K) by ring,
        Real.rpow_mul hδ.le, Real.rpow_neg_one, one_div]
    have hδUbound : δ ^ (-(U : ℝ) * K) ≤ sMin ^ ((s.sd : ℝ) + m) := by
      rw [hδinv]
      calc (1 / δ) ^ ((U : ℝ) * K)
          ≤ (1 / δ) ^ (2 * K * ((s.sd : ℝ) + m)) :=
            Real.rpow_le_rpow_of_exponent_le h1δ hUK
        _ = ((1 / δ) ^ (2 * K)) ^ ((s.sd : ℝ) + m) := by
            rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / δ)]
        _ ≤ sMin ^ ((s.sd : ℝ) + m) :=
            Real.rpow_le_rpow
              (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 / δ) _)
              hδsMin (by linarith [hexp0])
    have hcomb : δ ^ (-(U : ℝ) * K) * sMin ^ (-((s.sd : ℝ) + m)) ≤ 1 := by
      have hsneg : (0 : ℝ) ≤ sMin ^ (-((s.sd : ℝ) + m)) :=
        Real.rpow_nonneg hsMin0.le _
      have h1 : δ ^ (-(U : ℝ) * K) * sMin ^ (-((s.sd : ℝ) + m)) ≤
          sMin ^ ((s.sd : ℝ) + m) * sMin ^ (-((s.sd : ℝ) + m)) :=
        mul_le_mul_of_nonneg_right hδUbound hsneg
      have h2 : sMin ^ ((s.sd : ℝ) + m) * sMin ^ (-((s.sd : ℝ) + m)) = 1 := by
        rw [← Real.rpow_add hsMin0,
          show (s.sd : ℝ) + m + -((s.sd : ℝ) + m) = 0 by ring,
          Real.rpow_zero]
      rwa [h2] at h1
    have hg' : γ ^ s.ns * sMin ^ (-((s.sd : ℝ) + m)) ≤
        ((s.X.card : ℝ) / (A.card : ℝ)) ^ K := by
      have hsneg : (0 : ℝ) ≤ sMin ^ (-((s.sd : ℝ) + m)) :=
        Real.rpow_nonneg hsMin0.le _
      have h1 := mul_le_mul_of_nonneg_right hγδns hsneg
      have hbase : (0 : ℝ) ≤ ((s.X.card : ℝ) / (A.card : ℝ)) ^ K :=
        Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
      have h2 := mul_le_mul_of_nonneg_left hcomb hbase
      calc γ ^ s.ns * sMin ^ (-((s.sd : ℝ) + m))
          ≤ (((s.X.card : ℝ) / (A.card : ℝ)) ^ K * δ ^ (-(U : ℝ) * K)) *
              sMin ^ (-((s.sd : ℝ) + m)) := h1
        _ = ((s.X.card : ℝ) / (A.card : ℝ)) ^ K *
              (δ ^ (-(U : ℝ) * K) * sMin ^ (-((s.sd : ℝ) + m))) := by ring
        _ ≤ ((s.X.card : ℝ) / (A.card : ℝ)) ^ K * 1 := h2
        _ = ((s.X.card : ℝ) / (A.card : ℝ)) ^ K := mul_one _
    calc (s.W.P.toFinset.card : ℝ)
        ≤ C₆₈ * (γ ^ s.ns * sMin ^ (-((s.sd : ℝ) + m))) * (B.card : ℝ) :=
          hmaster
      _ ≤ C₆₈ * ((s.X.card : ℝ) / (A.card : ℝ)) ^ K * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hg' hC₆₈.le) (Nat.cast_nonneg _)
  · -- `dt < ℓ`: `sMin^{-(sd+m)} ≤ 1` already suffices.
    intro _
    have hle1 : sMin ^ (-((s.sd : ℝ) + m)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hsMin.le hexp0
    calc (s.W.P.toFinset.card : ℝ)
        ≤ C₆₈ * sMin ^ (-((s.sd : ℝ) + m)) * (B.card : ℝ) := hmaster'
      _ ≤ C₆₈ * 1 * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hle1 hC₆₈.le) (Nat.cast_nonneg _)
      _ = C₆₈ * (B.card : ℝ) := by rw [mul_one]

/-- Transport along a dimension-index equality does not change the
cardinality of `P` (stated at cardinalities so the equality is
homogeneous: `(h ▸ W).P : GAP n d₂` while `W.P : GAP n d₁`). -/
theorem SubSumWitness.P_cast {n : ℕ} {X : Finset (Fin n → ℤ)} {c : ℝ}
    {d₁ d₂ : ℕ} (h : d₁ = d₂) (W : SubSumWitness X c d₁) :
    ((h ▸ W).P.toFinset.card : ℝ) = (W.P.toFinset.card : ℝ) := by
  cases h
  rfl

/-- Transport along a dimension-index equality does not change `Ah`. -/
theorem SubSumWitness.Ah_cast {n : ℕ} {X : Finset (Fin n → ℤ)} {c : ℝ}
    {d₁ d₂ : ℕ} (h : d₁ = d₂) (W : SubSumWitness X c d₁) :
    (h ▸ W).Ah = W.Ah := by
  cases h
  rfl

/-- `log p ≤ log q + log M` from `p ≤ M·q`. -/
theorem log_le_of_mul_bound {p q M : ℝ} (hp : 0 < p) (hM : 0 < M)
    (h : p ≤ M * q) : Real.log p ≤ Real.log q + Real.log M := by
  have hq : 0 < q := by
    by_contra hq0
    push_neg at hq0
    have : M * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM.le hq0
    linarith
  have h1 : Real.log p ≤ Real.log (M * q) := Real.log_le_log hp h
  rwa [Real.log_mul (ne_of_gt hM) (ne_of_gt hq), add_comm] at h1

/-- `Φ' ≤ Φ − η` from a `log|P|` bound and a dimension bound. -/
theorem L10Stage.pot_le_sub {A : Finset (Fin ℓ → ℤ)} {δ ε γ : ℝ} {c' : ℝ}
    {D : ℕ} {sMin C₆₈ P0 : ℝ} {dinit : ℕ} {g h : ℝ}
    {s s' : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit}
    (hlog : Real.log (s'.W.P.toFinset.card : ℝ) -
        Real.log (s.W.P.toFinset.card : ℝ) ≤ g)
    (hd : (Real.log sMin / 2) *
        ((SubSumDim s'.X c' : ℝ) - (SubSumDim s.X c' : ℝ)) ≤ h)
    (hgh : g + h ≤ -L10η γ sMin C₆₈) :
    s'.pot ≤ s.pot - L10η γ sMin C₆₈ := by
  unfold L10Stage.pot
  linarith

/-- **The Lemma-10 descent loop.**  Given the Lemmas-6/8 move bound
`hmove`, bounded-dimension `c'`-witnesses `hwit'` for all `(d,β')`-sets
above the running threshold, the moved-set box bound `hlb` (Lemma 8's
`(d,β')`-set property) and the size-stop exclusion `hnostop` (eq. (10)),
the down/up/shrink iteration starting from any stage terminates at a
`(δ,γ)`-irreducible stage.

Proof: `WellFounded.fix` on the `ℕ`-measure `μ = ⌈Φ/η⌉` with
`Φ = log|P_j| + (log sMin / 2)·d_j` — every move drops `Φ` by `≥ η`,
and a stage with `Φ ≤ 0` (hence `d = 0`, `|ϕ_P(Â)| ≤ 1 < δ|X|`) is
vacuously irreducible. -/
theorem l10_descent {A : Finset (Fin ℓ → ℤ)} {δ ε γ : ℝ} {c' β' sMin C₆₈ : ℝ}
    {D : ℕ} {P0 : ℝ} {dinit : ℕ} {E : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hC₆₈ : 0 < C₆₈) (hC₆₈1 : C₆₈ ≤ 1) (hsMin : 1 < sMin)
    (hCs : C₆₈ ^ 2 < sMin) (hβ' : 0 < β')
    (hε1 : ε < 1) (hAgt1 : (1 : ℝ) < (A.card : ℝ)) (hE : 0 ≤ E)
    (hsMinA : (A.card : ℝ) ^ (1 - ε) ≤ sMin) (hP0b : P0 ≤ (A.card : ℝ) ^ E)
    (hdimcap : dinit + ⌈E / (1 - ε)⌉₊ ≤ D)
    (hAvac : (1 : ℝ) < δ * (A.card : ℝ) ^ (1 - ε / 2))
    (hmove : MoveBound68 c' δ sMin C₆₈)
    (hwit' : ∀ ⦃d : ℕ⦄, d ≤ D → ∀ {X : Finset (Fin d → ℤ)} {B' : GAP.Box d},
        B'.IsInterval → X ⊆ B'.toFinset → (B'.card : ℝ) ≤ (X.card : ℝ) ^ β' →
        δ * (A.card : ℝ) ^ (1 - ε / 2) ≤ (X.card : ℝ) →
        ∃ d', Nonempty (SubSumWitness X c' d'))
    (hlb : ∀ ⦃n d : ℕ⦄ {X : Finset (Fin n → ℤ)} {A₁ : Finset (Fin d → ℤ)}
        {x : Fin d → ℤ} (W : SubSumWitness X c' d),
        A₁ ⊆ W.imageAh → x ∈ W.imageP →
        δ * (X.card : ℝ) ≤ (A₁.card : ℝ) →
        ∃ B' : GAP.Box d, B'.IsInterval ∧ A₁.image (· - x) ⊆ B'.toFinset ∧
          (B'.card : ℝ) ≤ ((A₁.image (· - x)).card : ℝ) ^ β')
    (hnostop : ∀ ⦃d : ℕ⦄ {X' : Finset (Fin d → ℤ)} (nd nu ns sd : ℕ)
        (W' : SubSumWitness X' c' (SubSumDim X' c')),
        (δ : ℝ) ^ (nd + nu + ns) * (A.card : ℝ) ≤ (X'.card : ℝ) →
        (W'.P.toFinset.card : ℝ) ≤
          C₆₈ ^ (nd + nu : ℕ) * γ ^ (ns : ℕ) * sMin ^ (-(sd : ℝ)) * P0 →
        (X'.card : ℝ) < (A.card : ℝ) ^ (1 - ε / 2) →
        (nd : ℝ) ≤ (dinit : ℝ) + sd → nu ≤ sd → False)
    (s : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit) :
    ∃ s' : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit,
      Irreducible s'.W c' δ γ := by
  classical
  have hη : 0 < L10η γ sMin C₆₈ := L10η_pos hC₆₈ hsMin hCs hγ hγ1
  have hls : 0 < Real.log sMin := Real.log_pos hsMin
  have hηd : L10η γ sMin C₆₈ ≤ Real.log sMin / 2 - Real.log C₆₈ :=
    min_le_left _ _
  have hηγ : L10η γ sMin C₆₈ ≤ -Real.log γ := min_le_right _ _
  refine WellFounded.fix
    (C := fun _ : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit ↦
      ∃ s' : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit,
        Irreducible s'.W c' δ γ)
    (measure L10Stage.μ).wf ?_ s
  intro s ih
  -- `ih : ∀ s', s'.μ < s.μ → ∃ s'', Irreducible s''.W c' δ γ`
  by_cases hirr : Irreducible s.W c' δ γ
  · exact ⟨s, hirr⟩
  by_cases hsmall : (s.W.imageAh.card : ℝ) < δ * (s.X.card : ℝ)
  · exact ⟨s, irreducible_of_imageAh_small s.W hsmall⟩
  have hd1 : 1 ≤ SubSumDim s.X c' := by
    by_contra hlt
    push_neg at hlt
    have hd0 : SubSumDim s.X c' = 0 := Nat.lt_one_iff.mp hlt
    have hAh1 : (s.W.Ah.card : ℝ) ≤ 1 := by
      have h := (hd0 ▸ s.W).card_Ah_le_one
      rw [SubSumWitness.Ah_cast hd0 s.W] at h
      exact_mod_cast h
    have himg : s.W.imageAh.card = s.W.Ah.card := s.W.card_imageAh
    have hAh1' : (s.W.imageAh.card : ℝ) ≤ 1 := by
      rw [himg]; exact hAh1
    have hbig : (1 : ℝ) < δ * (s.X.card : ℝ) :=
      lt_of_lt_of_le hAvac (mul_le_mul_of_nonneg_left s.size hδ.le)
    linarith
  obtain ⟨A₁, x, hA₁, hx, hA₁card, hder', hcase⟩ :=
    DerivedFrom.step_cases_of_derived s.der s.W rfl hd1 hirr
  set X' := A₁.image (· - x) with hX'def
  have hX'card : (X'.card : ℝ) = (A₁.card : ℝ) := by
    rw [hX'def, Finset.card_image_of_injective _ sub_left_injective]
  have hX'thr : δ * (A.card : ℝ) ^ (1 - ε / 2) ≤ (X'.card : ℝ) := by
    rw [hX'card]
    exact le_trans (mul_le_mul_of_nonneg_left s.size hδ.le) hA₁card
  obtain ⟨B', hB'int, hX'sub, hB'card⟩ := hlb s.W hA₁ hx hA₁card
  obtain ⟨d₂, hwit2⟩ := hwit' s.dim hB'int hX'sub hB'card hX'thr
  have hwitne : ∃ d', Nonempty (SubSumWitness X' c' d') := ⟨d₂, hwit2⟩
  obtain ⟨W', hW'b⟩ := hmove s.W rfl hA₁ hx hA₁card hwitne
  -- `X'` is a `set`-bound let, so `SubSumDim X' c'` is definitionally
  -- `SubSumDim (A₁.image (· - x)) c'`; restate `hW'b` in `X'`-form so that
  -- downstream `simpa [hmax]` rewrites match syntactically.
  replace hW'b : (W'.P.toFinset.card : ℝ) ≤
      C₆₈ * sMin ^
          (-(max 0 ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)))) *
        (s.W.P.toFinset.card : ℝ) := hW'b
  have hP1 : (1 : ℝ) ≤ (s.W.P.toFinset.card : ℝ) := s.W.one_le_card_P
  have hP'1 : (1 : ℝ) ≤ (W'.P.toFinset.card : ℝ) := W'.one_le_card_P
  -- **Dimension budget**: the next stage's `SubSumDim` is bounded by the
  -- `|P|`-invariant rather than by `hwit'` (which now gives no `d' ≤ D`
  -- bound).  From `1 ≤ |P'| ≤ C₆₈^U·γ^ns·sMin^{−sd}·P0 ≤ sMin^{−sd}·|A|^E`
  -- we get `sMin^{sd} ≤ |A|^E`, hence `sd·(1−ε)·log|A| ≤ sd·log sMin ≤
  -- E·log|A|`, i.e. `sd ≤ E/(1−ε)`; then `d_{i+1} = dinit + sd − sdd ≤
  -- dinit + ⌈E/(1−ε)⌉₊ ≤ D` (`hdimcap`).
  have hlogApos : (0 : ℝ) < Real.log (A.card : ℝ) := Real.log_pos hAgt1
  have hlogsMin : (1 - ε) * Real.log (A.card : ℝ) ≤ Real.log sMin := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hsMinA
    rwa [Real.log_rpow (by linarith : (0 : ℝ) < (A.card : ℝ))] at h
  have hdim_of : ∀ ⦃d'' : ℕ⦄ {X'' : Finset (Fin d'' → ℤ)}
      (W'' : SubSumWitness X'' c' (SubSumDim X'' c')) (U' ns' sd' sdd' : ℕ),
      (W''.P.toFinset.card : ℝ) ≤
        C₆₈ ^ U' * γ ^ ns' * sMin ^ (-(sd' : ℝ)) * P0 →
      (SubSumDim X'' c' : ℤ) = (dinit : ℤ) + (sd' : ℤ) - (sdd' : ℤ) →
      SubSumDim X'' c' ≤ D := by
    intro d'' X'' W'' U' ns' sd' sdd' hPb'' hdim''
    have hsMinpos : (0 : ℝ) < sMin := by linarith
    have hspos : (0 : ℝ) < sMin ^ (-(sd' : ℝ)) :=
      Real.rpow_pos_of_pos hsMinpos _
    have hP0pos : (0 : ℝ) < P0 := by
      by_contra hp
      push_neg at hp
      have hfac : (0 : ℝ) ≤ C₆₈ ^ U' * γ ^ ns' * sMin ^ (-(sd' : ℝ)) := by
        positivity
      have h0 : C₆₈ ^ U' * γ ^ ns' * sMin ^ (-(sd' : ℝ)) * P0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hfac hp
      linarith [W''.one_le_card_P, hPb'']
    have hCU : C₆₈ ^ U' ≤ 1 := pow_le_one₀ hC₆₈.le hC₆₈1
    have hγns : γ ^ ns' ≤ 1 := pow_le_one₀ hγ.le hγ1.le
    have hfac2 : (0 : ℝ) ≤ sMin ^ (-(sd' : ℝ)) * P0 :=
      mul_nonneg hspos.le hP0pos.le
    have h1 : (1 : ℝ) ≤ sMin ^ (-(sd' : ℝ)) * P0 := by
      have hregroup : C₆₈ ^ U' * γ ^ ns' * sMin ^ (-(sd' : ℝ)) * P0 =
          C₆₈ ^ U' * γ ^ ns' * (sMin ^ (-(sd' : ℝ)) * P0) := by ring
      have h2 : (1 : ℝ) ≤
          C₆₈ ^ U' * γ ^ ns' * (sMin ^ (-(sd' : ℝ)) * P0) :=
        hregroup ▸ le_trans W''.one_le_card_P hPb''
      have h3 : C₆₈ ^ U' * γ ^ ns' * (sMin ^ (-(sd' : ℝ)) * P0) ≤
          sMin ^ (-(sd' : ℝ)) * P0 := by
        calc C₆₈ ^ U' * γ ^ ns' * (sMin ^ (-(sd' : ℝ)) * P0)
            ≤ 1 * γ ^ ns' * (sMin ^ (-(sd' : ℝ)) * P0) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hCU (pow_nonneg hγ.le _)) hfac2
          _ = γ ^ ns' * (sMin ^ (-(sd' : ℝ)) * P0) := by rw [one_mul]
          _ ≤ 1 * (sMin ^ (-(sd' : ℝ)) * P0) :=
              mul_le_mul_of_nonneg_right hγns hfac2
          _ = sMin ^ (-(sd' : ℝ)) * P0 := one_mul _
      linarith [h2, h3]
    have hsd_pow : sMin ^ (sd' : ℝ) ≤ (A.card : ℝ) ^ E := by
      have h2 : sMin ^ (-(sd' : ℝ)) * P0 ≤
          sMin ^ (-(sd' : ℝ)) * (A.card : ℝ) ^ E :=
        mul_le_mul_of_nonneg_left hP0b hspos.le
      have h3 : (1 : ℝ) ≤ sMin ^ (-(sd' : ℝ)) * (A.card : ℝ) ^ E :=
        le_trans h1 h2
      have hcancel : sMin ^ (sd' : ℝ) * sMin ^ (-(sd' : ℝ)) = 1 := by
        rw [← Real.rpow_add (by linarith : (0 : ℝ) < sMin),
          add_neg_cancel, Real.rpow_zero]
      have h4 : sMin ^ (sd' : ℝ) * (sMin ^ (-(sd' : ℝ)) * (A.card : ℝ) ^ E) =
          (A.card : ℝ) ^ E := by
        rw [← mul_assoc, hcancel, one_mul]
      have h5 := mul_le_mul_of_nonneg_left h3
        (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < sMin) (sd' : ℝ)).le
      rwa [mul_one, h4] at h5
    have hsd : (sd' : ℝ) * Real.log sMin ≤ E * Real.log (A.card : ℝ) := by
      have h := Real.log_le_log
        (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < sMin) _) hsd_pow
      rwa [Real.log_rpow (by linarith : (0 : ℝ) < sMin),
        Real.log_rpow (by linarith : (0 : ℝ) < (A.card : ℝ))] at h
    have hsd' : (sd' : ℝ) ≤ E / (1 - ε) := by
      have h1ε : (0 : ℝ) < 1 - ε := by linarith
      have h2 : (sd' : ℝ) * (1 - ε) * Real.log (A.card : ℝ) ≤
          E * Real.log (A.card : ℝ) := by
        calc (sd' : ℝ) * (1 - ε) * Real.log (A.card : ℝ)
            = (sd' : ℝ) * ((1 - ε) * Real.log (A.card : ℝ)) := by ring
          _ ≤ (sd' : ℝ) * Real.log sMin :=
              mul_le_mul_of_nonneg_left hlogsMin (Nat.cast_nonneg _)
          _ ≤ E * Real.log (A.card : ℝ) := hsd
      have h3 : (sd' : ℝ) * (1 - ε) ≤ E :=
        le_of_mul_le_mul_right h2 hlogApos
      rwa [le_div_iff₀ h1ε]
    have hsdceil : sd' ≤ ⌈E / (1 - ε)⌉₊ := by
      have h : (sd' : ℝ) ≤ (⌈E / (1 - ε)⌉₊ : ℝ) :=
        le_trans hsd' (Nat.le_ceil _)
      exact_mod_cast h
    omega
  have hpos : 0 < s.pot := by
    unfold L10Stage.pot
    have h1 : (0:ℝ) ≤ Real.log (s.W.P.toFinset.card : ℝ) :=
      Real.log_nonneg hP1
    have h2 : (0:ℝ) ≤ Real.log sMin / 2 * (SubSumDim s.X c' : ℝ) :=
      mul_nonneg (by linarith) (by positivity)
    linarith [show (0:ℝ) < Real.log sMin / 2 *
      (SubSumDim s.X c' : ℝ) from
        mul_pos (by linarith) (by exact_mod_cast hd1)]
  rcases hcase with hdown | hup | ⟨heq, W'', hW''⟩
  · -- **down-move**: `SubSumDim X' c' < SubSumDim s.X c'`
    have hmax : max 0 ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)) = 0 :=
      max_eq_left (sub_nonpos.mpr (by exact_mod_cast hdown.le))
    have hb : (W'.P.toFinset.card : ℝ) ≤ C₆₈ * (s.W.P.toFinset.card : ℝ) := by
      simpa [hmax] using hW'b
    have hPb' : (W'.P.toFinset.card : ℝ) ≤
        C₆₈ ^ (s.nd + 1 + s.nu : ℕ) * γ ^ (s.ns : ℕ) *
          sMin ^ (-(s.sd : ℝ)) * P0 := by
      have h2 := mul_le_mul_of_nonneg_left s.hPb hC₆₈.le
      have h4 : C₆₈ ^ (s.nd + 1 + s.nu : ℕ) * γ ^ (s.ns : ℕ) *
          sMin ^ (-(s.sd : ℝ)) * P0 =
          C₆₈ * (C₆₈ ^ (s.nd + s.nu : ℕ) * γ ^ (s.ns : ℕ) *
            sMin ^ (-(s.sd : ℝ)) * P0) := by
        rw [show s.nd + 1 + s.nu = s.nd + s.nu + 1 by omega, pow_succ]
        ring
      rw [h4]
      exact le_trans hb h2
    have hsz'' : (δ : ℝ) ^ (s.nd + 1 + s.nu + s.ns) * (A.card : ℝ) ≤
        (X'.card : ℝ) := by
      have e : s.nd + 1 + s.nu + s.ns = s.nd + s.nu + s.ns + 1 := by omega
      rw [e, pow_succ, hX'card]
      calc (δ:ℝ)^(s.nd+s.nu+s.ns) * δ * (A.card:ℝ)
          = δ * ((δ:ℝ)^(s.nd+s.nu+s.ns) * (A.card:ℝ)) := by ring
        _ ≤ δ * (s.X.card:ℝ) := mul_le_mul_of_nonneg_left s.hsz hδ.le
        _ ≤ (A₁.card:ℝ) := hA₁card
    have hnd' : ((s.nd + 1 : ℕ) : ℝ) ≤ (dinit : ℝ) + (s.sd : ℝ) := by
      have h1 : (s.nd : ℝ) ≤ (s.sdd : ℝ) := by exact_mod_cast s.hnd
      have h2 : (s.sdd : ℝ) ≤ (dinit : ℝ) + (s.sd : ℝ) - 1 := by
        have h3 : (s.sdd : ℤ) =
            (dinit : ℤ) + (s.sd : ℤ) - (SubSumDim s.X c' : ℤ) := by
          have h := s.hdim; omega
        have h4 : (s.sdd : ℝ) =
            (dinit : ℝ) + (s.sd : ℝ) - (SubSumDim s.X c' : ℝ) := by
          exact_mod_cast h3
        have h5 : (1 : ℝ) ≤ (SubSumDim s.X c' : ℝ) := by exact_mod_cast hd1
        linarith
      push_cast
      linarith
    by_cases hsm : (X'.card : ℝ) < (A.card : ℝ) ^ (1 - ε / 2)
    · exact (hnostop (s.nd + 1) s.nu s.ns s.sd W' hsz'' hPb' hsm hnd' s.hnu).elim
    · have hdim'' : (SubSumDim X' c' : ℤ) = (dinit : ℤ) + (s.sd : ℤ) -
          ((s.sdd + (SubSumDim s.X c' - SubSumDim X' c') : ℕ) : ℤ) := by
        have h := s.hdim
        have hcast : ((SubSumDim s.X c' - SubSumDim X' c' : ℕ) : ℤ) =
            (SubSumDim s.X c' : ℤ) - (SubSumDim X' c' : ℤ) :=
          Nat.cast_sub hdown.le
        push_cast at hcast ⊢
        omega
      have hnd2 : s.nd + 1 ≤ s.sdd + (SubSumDim s.X c' - SubSumDim X' c') := by
        have h1 : 1 ≤ SubSumDim s.X c' - SubSumDim X' c' :=
          Nat.sub_pos_of_lt hdown
        exact Nat.add_le_add s.hnd h1
      have hdim2 : SubSumDim X' c' ≤ D :=
        hdim_of W' (s.nd + 1 + s.nu) s.ns s.sd
          (s.sdd + (SubSumDim s.X c' - SubSumDim X' c')) hPb' hdim''
      set s' : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit :=
        ⟨SubSumDim s.X c', X', hder', W', hdim2, not_lt.mp hsm, s.nd + 1, s.nu, s.ns,
          s.sd, s.sdd + (SubSumDim s.X c' - SubSumDim X' c'), hsz'', hPb',
          hdim'', s.hnu, hnd2⟩
      have hdelt : ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)) ≤ -1 := by
        have h : SubSumDim X' c' + 1 ≤ SubSumDim s.X c' := hdown
        have h' : (SubSumDim X' c' : ℝ) + 1 ≤ (SubSumDim s.X c' : ℝ) := by
          exact_mod_cast h
        linarith
      have hdrop : s'.pot ≤ s.pot - L10η γ sMin C₆₈ := by
        apply L10Stage.pot_le_sub (g := Real.log C₆₈)
          (h := -(Real.log sMin / 2))
        · have h := log_le_of_mul_bound (zero_lt_one.trans_le hP'1)
            (mul_pos hC₆₈ (Real.rpow_pos_of_pos (by linarith) _)) hW'b
          rw [Real.log_mul (ne_of_gt hC₆₈)
            (ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)),
            Real.log_rpow (by linarith), hmax] at h
          simp only [neg_zero, mul_zero, add_zero] at h
          show Real.log (s'.W.P.toFinset.card : ℝ) -
              Real.log (s.W.P.toFinset.card : ℝ) ≤ Real.log C₆₈
          change Real.log (W'.P.toFinset.card : ℝ) -
              Real.log (s.W.P.toFinset.card : ℝ) ≤ Real.log C₆₈
          linarith [h]
        · have h2 := mul_le_mul_of_nonneg_left hdelt
            (by linarith : (0 : ℝ) ≤ Real.log sMin / 2)
          rwa [mul_neg_one] at h2
        · linarith [hηd]
      exact ih s' (L10Stage.μ_lt hη hdrop hpos)
  · -- **up-move**: `SubSumDim s.X c' < SubSumDim X' c'`
    have hΔ : 0 < (SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ) := by
      have h : SubSumDim s.X c' + 1 ≤ SubSumDim X' c' := hup
      have h' : (SubSumDim s.X c' : ℝ) + 1 ≤ (SubSumDim X' c' : ℝ) := by
        exact_mod_cast h
      linarith
    have hmax : max 0 ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)) =
        (SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ) :=
      max_eq_right hΔ.le
    have hb : (W'.P.toFinset.card : ℝ) ≤
        C₆₈ * sMin ^ (-((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ))) *
          (s.W.P.toFinset.card : ℝ) := by
      simpa [hmax] using hW'b
    have hsub' : ((SubSumDim X' c' - SubSumDim s.X c' : ℕ) : ℝ) =
        (SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ) :=
      Nat.cast_sub hup.le
    have hsd' : (-((s.sd + (SubSumDim X' c' - SubSumDim s.X c') : ℕ) : ℝ)) =
        (-(s.sd : ℝ)) + (-((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ))) := by
      rw [Nat.cast_add, hsub']
      ring
    have hPb' : (W'.P.toFinset.card : ℝ) ≤
        C₆₈ ^ (s.nd + (s.nu + 1) : ℕ) * γ ^ (s.ns : ℕ) *
          sMin ^ (-((s.sd + (SubSumDim X' c' - SubSumDim s.X c') : ℕ) : ℝ)) *
            P0 := by
      have hpow : sMin ^ (-((s.sd + (SubSumDim X' c' - SubSumDim s.X c') : ℕ) : ℝ))
          = sMin ^ (-(s.sd : ℝ)) *
              sMin ^ (-((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ))) := by
        rw [hsd', Real.rpow_add (by linarith)]
      have h3 : C₆₈ ^ (s.nd + (s.nu + 1) : ℕ) * γ ^ (s.ns : ℕ) *
          (sMin ^ (-(s.sd : ℝ)) *
            sMin ^ (-((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)))) * P0 =
          C₆₈ * sMin ^ (-((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ))) *
            (C₆₈ ^ (s.nd + s.nu : ℕ) * γ ^ (s.ns : ℕ) * sMin ^ (-(s.sd : ℝ)) *
              P0) := by
        rw [show s.nd + (s.nu + 1) = s.nd + s.nu + 1 by omega, pow_succ]
        ring
      rw [hpow, h3]
      exact le_trans hb (mul_le_mul_of_nonneg_left s.hPb
        (mul_nonneg hC₆₈.le (Real.rpow_nonneg (by linarith) _)))
    have hsz'' : (δ : ℝ) ^ (s.nd + (s.nu + 1) + s.ns) * (A.card : ℝ) ≤
        (X'.card : ℝ) := by
      have e : s.nd + (s.nu + 1) + s.ns = s.nd + s.nu + s.ns + 1 := by omega
      rw [e, pow_succ, hX'card]
      calc (δ:ℝ)^(s.nd+s.nu+s.ns) * δ * (A.card:ℝ)
          = δ * ((δ:ℝ)^(s.nd+s.nu+s.ns) * (A.card:ℝ)) := by ring
        _ ≤ δ * (s.X.card:ℝ) := mul_le_mul_of_nonneg_left s.hsz hδ.le
        _ ≤ (A₁.card:ℝ) := hA₁card
    have hnu' : s.nu + 1 ≤ s.sd + (SubSumDim X' c' - SubSumDim s.X c') := by
      have h1 : 1 ≤ SubSumDim X' c' - SubSumDim s.X c' :=
        Nat.sub_pos_of_lt hup
      exact Nat.add_le_add s.hnu h1
    by_cases hsm : (X'.card : ℝ) < (A.card : ℝ) ^ (1 - ε / 2)
    · have hnd' : ((s.nd : ℕ) : ℝ) ≤ (dinit : ℝ) +
          (s.sd + (SubSumDim X' c' - SubSumDim s.X c') : ℕ) := by
        have h1 : (s.nd : ℝ) ≤ (s.sdd : ℝ) := by exact_mod_cast s.hnd
        have h3 : (s.sdd : ℤ) =
            (dinit : ℤ) + (s.sd : ℤ) - (SubSumDim s.X c' : ℤ) := by
          have h := s.hdim; omega
        have h4 : (s.sdd : ℝ) =
            (dinit : ℝ) + (s.sd : ℝ) - (SubSumDim s.X c' : ℝ) := by
          exact_mod_cast h3
        have h5 : (0 : ℝ) ≤ (SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ) :=
          hΔ.le
        push_cast
        linarith
      exact (hnostop s.nd (s.nu + 1) s.ns
        (s.sd + (SubSumDim X' c' - SubSumDim s.X c')) W' hsz'' hPb' hsm
        hnd' hnu').elim
    · have hdim'' : (SubSumDim X' c' : ℤ) =
          (dinit : ℤ) + ((s.sd + (SubSumDim X' c' - SubSumDim s.X c') : ℕ) : ℤ) -
            (s.sdd : ℤ) := by
        have h := s.hdim
        have hcast : ((SubSumDim X' c' - SubSumDim s.X c' : ℕ) : ℤ) =
            (SubSumDim X' c' : ℤ) - (SubSumDim s.X c' : ℤ) :=
          Nat.cast_sub hup.le
        push_cast at hcast ⊢
        omega
      have hdim2 : SubSumDim X' c' ≤ D :=
        hdim_of W' (s.nd + (s.nu + 1)) s.ns
          (s.sd + (SubSumDim X' c' - SubSumDim s.X c')) s.sdd hPb' hdim''
      set s' : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit :=
        ⟨SubSumDim s.X c', X', hder', W', hdim2, not_lt.mp hsm, s.nd, s.nu + 1, s.ns,
          s.sd + (SubSumDim X' c' - SubSumDim s.X c'), s.sdd, hsz'', hPb',
          hdim'', hnu', s.hnd⟩
      have hdrop : s'.pot ≤ s.pot - L10η γ sMin C₆₈ := by
        apply L10Stage.pot_le_sub
          (g := Real.log C₆₈ -
            ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)) * Real.log sMin)
          (h := (Real.log sMin / 2) *
            ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)))
        · have h := log_le_of_mul_bound (zero_lt_one.trans_le hP'1)
            (mul_pos hC₆₈ (Real.rpow_pos_of_pos (by linarith) _)) hW'b
          rw [Real.log_mul (ne_of_gt hC₆₈)
            (ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)),
            Real.log_rpow (by linarith), hmax] at h
          show Real.log (s'.W.P.toFinset.card : ℝ) -
              Real.log (s.W.P.toFinset.card : ℝ) ≤ _
          change Real.log (W'.P.toFinset.card : ℝ) -
              Real.log (s.W.P.toFinset.card : ℝ) ≤ _
          linarith [h]
        · exact le_rfl
        · have ht : Real.log sMin / 2 < Real.log sMin := by linarith [hls]
          have hgap : Real.log C₆₈ -
              ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)) * Real.log sMin +
              (Real.log sMin / 2) *
                ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)) ≤
              -(L10η γ sMin C₆₈) := by
            have hΔ1 : (1 : ℝ) ≤
                (SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ) := by
              have h' : (SubSumDim s.X c' : ℝ) + 1 ≤
                  (SubSumDim X' c' : ℝ) := by exact_mod_cast hup
              linarith
            have h1 : ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)) *
                (Real.log sMin - Real.log sMin / 2) ≥
                Real.log sMin - Real.log sMin / 2 := by
              apply le_mul_of_one_le_left (by linarith [ht]) hΔ1
            linarith [hηd, h1]
          exact hgap
      exact ih s' (L10Stage.μ_lt hη hdrop hpos)
  · -- **shrink-move**: `SubSumDim X' c' = SubSumDim s.X c'`, `|P'| < γ|P|`
    set W''s : SubSumWitness X' c' (SubSumDim X' c') := heq.symm ▸ W''
      with hW''s
    have hPcast : (W''s.P.toFinset.card : ℝ) = (W''.P.toFinset.card : ℝ) := by
      rw [hW''s]; exact SubSumWitness.P_cast heq.symm W''
    have hW''b : (W''s.P.toFinset.card : ℝ) <
        γ * (s.W.P.toFinset.card : ℝ) := by
      rw [hPcast]; exact hW''
    have hPb' : (W''s.P.toFinset.card : ℝ) ≤
        C₆₈ ^ (s.nd + s.nu : ℕ) * γ ^ (s.ns + 1 : ℕ) *
          sMin ^ (-(s.sd : ℝ)) * P0 := by
      have h2 := mul_le_mul_of_nonneg_left s.hPb hγ.le
      have h3 : γ * (s.W.P.toFinset.card : ℝ) ≤
          γ * (C₆₈ ^ (s.nd + s.nu : ℕ) * γ ^ (s.ns : ℕ) *
            sMin ^ (-(s.sd : ℝ)) * P0) := h2
      have h4 : (W''s.P.toFinset.card : ℝ) ≤
          γ * (s.W.P.toFinset.card : ℝ) := hW''b.le
      have h5 := le_trans h4 h3
      have h6 : C₆₈ ^ (s.nd + s.nu : ℕ) * γ ^ (s.ns + 1 : ℕ) *
          sMin ^ (-(s.sd : ℝ)) * P0 =
          γ * (C₆₈ ^ (s.nd + s.nu : ℕ) * γ ^ (s.ns : ℕ) *
            sMin ^ (-(s.sd : ℝ)) * P0) := by
        rw [pow_succ]; ring
      rwa [h6]
    have hsz'' : (δ : ℝ) ^ (s.nd + s.nu + (s.ns + 1)) * (A.card : ℝ) ≤
        (X'.card : ℝ) := by
      have e : s.nd + s.nu + (s.ns + 1) = s.nd + s.nu + s.ns + 1 := by omega
      rw [e, pow_succ, hX'card]
      calc (δ:ℝ)^(s.nd+s.nu+s.ns) * δ * (A.card:ℝ)
          = δ * ((δ:ℝ)^(s.nd+s.nu+s.ns) * (A.card:ℝ)) := by ring
        _ ≤ δ * (s.X.card:ℝ) := mul_le_mul_of_nonneg_left s.hsz hδ.le
        _ ≤ (A₁.card:ℝ) := hA₁card
    by_cases hsm : (X'.card : ℝ) < (A.card : ℝ) ^ (1 - ε / 2)
    · have hnd' : ((s.nd : ℕ) : ℝ) ≤ (dinit : ℝ) + (s.sd : ℝ) := by
        have h1 : (s.nd : ℝ) ≤ (s.sdd : ℝ) := by exact_mod_cast s.hnd
        have h3 : (s.sdd : ℤ) =
            (dinit : ℤ) + (s.sd : ℤ) - (SubSumDim s.X c' : ℤ) := by
          have h := s.hdim; omega
        have h4 : (s.sdd : ℝ) =
            (dinit : ℝ) + (s.sd : ℝ) - (SubSumDim s.X c' : ℝ) := by
          exact_mod_cast h3
        have h5 : (1 : ℝ) ≤ (SubSumDim s.X c' : ℝ) := by exact_mod_cast hd1
        linarith
      exact (hnostop s.nd s.nu (s.ns + 1) s.sd W''s hsz'' hPb' hsm hnd'
        s.hnu).elim
    · have hdim'' : (SubSumDim X' c' : ℤ) = (dinit : ℤ) + (s.sd : ℤ) -
          (s.sdd : ℤ) := by
        have h := s.hdim
        have hcast : (SubSumDim X' c' : ℤ) = (SubSumDim s.X c' : ℤ) := by
          exact_mod_cast heq
        omega
      have hdim2 : SubSumDim X' c' ≤ D :=
        hdim_of W''s (s.nd + s.nu) (s.ns + 1) s.sd s.sdd hPb' hdim''
      set s' : L10Stage A δ ε γ c' D sMin C₆₈ P0 dinit :=
        ⟨SubSumDim s.X c', X', hder', W''s, hdim2, not_lt.mp hsm, s.nd, s.nu, s.ns + 1,
          s.sd, s.sdd, hsz'', hPb', hdim'', s.hnu, s.hnd⟩
      have hdrop : s'.pot ≤ s.pot - L10η γ sMin C₆₈ := by
        apply L10Stage.pot_le_sub (g := Real.log γ) (h := 0)
        · have h := log_le_of_mul_bound
            (zero_lt_one.trans_le W''s.one_le_card_P) hγ hW''b.le
          show Real.log (s'.W.P.toFinset.card : ℝ) -
              Real.log (s.W.P.toFinset.card : ℝ) ≤ Real.log γ
          change Real.log (W''s.P.toFinset.card : ℝ) -
              Real.log (s.W.P.toFinset.card : ℝ) ≤ Real.log γ
          linarith [h]
        · show (Real.log sMin / 2) *
              ((SubSumDim X' c' : ℝ) - (SubSumDim s.X c' : ℝ)) ≤ 0
          have hcast : (SubSumDim X' c' : ℝ) = (SubSumDim s.X c' : ℝ) := by
            exact_mod_cast heq
          exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hls])
            (sub_nonpos.mpr hcast.le)
        · simp only [add_zero]
          linarith [hηγ]
      exact ih s' (L10Stage.μ_lt hη hdrop hpos)

/-- **Uniform Cor-5 constant across bounded ambient dimension**:
a single `c'` that is a Cor-5 constant for every `(d,β')`-class with
`d ≤ D`.  The round-6 note claimed this was obstructed by constant
rigidity — `SubSumWitness` is not monotone in `c`.  The resolution is
the `s`-parameter rescaling in `uniform_cor5_of_family`: with
`c' := min_{d ≤ D} cf d`, each class's `cfp_structure` is applied at
`s := ⌊(c'/cf_d)·s(X)⌋₊`, which makes both the `k ≤ c'·s(X)` and the
`|Â| ≥ |X| − c'⁻¹|X|/log|X|` inequalities hold simultaneously (they use
`c'` in opposite directions, but the rescaled `s ≈ (c'/cf_d)·s(X)`
absorbs the factor).  All largeness requirements are bundled into the
threshold `C₀ d`. -/
theorem uniform_cor5_exists {β' : ℝ} (hβ' : 1 < β') (D : ℕ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ d ≤ D, ∃ C₀, UniformCor5 c' β' d C₀ := by
  obtain ⟨cf, df, hcf, hcfp⟩ := cfp_structure_family hβ'
  obtain ⟨c', C₀, hc', hval⟩ := uniform_cor5_of_family hβ' hcf hcfp D
  exact ⟨c', hc', fun d hd ↦ ⟨C₀ d, fun X B' hBi hsubX hBX hC₀ ↦
    (hval hd hBi hsubX hBX hC₀).imp fun d' h ↦ h.2⟩⟩

/-- **Lemma-10 bookkeeping (`iterates_to_irreducible`).**  Given the
move bound `hmove` (Lemmas 6/8, `lem68_move_bound`), the bounded-dimension
`c'`-witness inputs `hwit0`/`hwit'` (uniform Cor-5,
`uniform_cor5_bounded_exists`), the `(d,β')`-set property `hlb` of a move
(Lemma 8, `moved_set_is_lb`), the large-`K` hypothesis `hKbig` (eq. (10)'s
`K ≥ C_{β,ε}`, which the `γ ≤ δ^K` interface does *not* supply), and the
initial largeness `hA1`/`hAvac`, the down/up/shrink iteration produces a
`(δ,γ)`-irreducible derived set together with the three GAP bounds.

The proof applies `l10_descent` to the initial stage built from the
canonical `c'`-witness of `A` (`P₀` = the `lem68_initial_bound` bound,
`dinit = SubSumDim A c'`), then `final_P_bounds` for the conclusion. -/
theorem iterates_to_irreducible
    {β ε δ γ K : ℝ} {c' sMin C₆₈ β' : ℝ} {D : ℕ} {G : ℕ → ℕ}
    (hβ : 1 < β) (hε : 0 < ε) (hε3 : ε < 1 / 3)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < γ) (hγδ : γ ≤ δ ^ K)
    (hKbig : (2 : ℝ) * (2 * ℓ + β + 2) / ε < K)
    (hc' : 0 < c') (hC₆₈ : 0 < C₆₈) (hsMin : 1 < sMin)
    (hCs : C₆₈ ^ 2 < sMin) (hβ' : 0 < β') (hℓD : ℓ ≤ D)
    (hGD : G ℓ + ⌈(2 * (ℓ : ℝ) + β + 2) / (1 - ε)⌉₊ ≤ D)
    {A : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ}
    (hBint : B.IsInterval) (hNA : NonAveraging A) (hsub : A ⊆ B.toFinset)
    (hBβ : (B.card : ℝ) ≤ (A.card : ℝ) ^ β)
    (hA1 : (1 : ℝ) ≤ (A.card : ℝ))
    (hC₆₈b : C₆₈ ≤ (A.card : ℝ))
    (hAvac : (1 : ℝ) < δ * (A.card : ℝ) ^ (1 - ε / 2))
    (hC₆₈1 : C₆₈ ≤ 1)
    (hsMinA : (A.card : ℝ) ^ (1 - ε) ≤ sMin)
    (hδA : (1 / δ) ^ (2 * K) ≤ (A.card : ℝ) ^ (1 - ε))
    (hLarg : K * Real.log (1 / δ) * (D : ℝ) ≤
        (K * ε / 2 - (2 * ℓ + β + 2)) * Real.log (A.card : ℝ))
    (hmove : MoveBound68 c' δ sMin C₆₈)
    (hwit0 : ∃ d' ≤ G ℓ, Nonempty (SubSumWitness A c' d'))
    (hwit' : ∀ ⦃d : ℕ⦄, d ≤ D → ∀ {X : Finset (Fin d → ℤ)} {B' : GAP.Box d},
        B'.IsInterval → X ⊆ B'.toFinset → (B'.card : ℝ) ≤ (X.card : ℝ) ^ β' →
        δ * (A.card : ℝ) ^ (1 - ε / 2) ≤ (X.card : ℝ) →
        ∃ d', Nonempty (SubSumWitness X c' d'))
    (hlb : ∀ ⦃n d : ℕ⦄ {X : Finset (Fin n → ℤ)} {A₁ : Finset (Fin d → ℤ)}
        {x : Fin d → ℤ} (W : SubSumWitness X c' d),
        A₁ ⊆ W.imageAh → x ∈ W.imageP →
        δ * (X.card : ℝ) ≤ (A₁.card : ℝ) →
        ∃ B' : GAP.Box d, B'.IsInterval ∧ A₁.image (· - x) ⊆ B'.toFinset ∧
          (B'.card : ℝ) ≤ ((A₁.image (· - x)).card : ℝ) ^ β') :
    ∃ (n : ℕ) (At : Finset (Fin n → ℤ)) (dt : ℕ)
      (Wt : SubSumWitness At c' dt),
      DerivedFrom A δ At ∧ NonAveraging At ∧
      (A.card : ℝ) ^ (1 - ε) ≤ (At.card : ℝ) ∧ dt ≤ D ∧
      Irreducible Wt c' δ γ ∧
      (ℓ < dt → (Wt.P.toFinset.card : ℝ) ≤
        C₆₈ * (A.card : ℝ) ^ (-(1 - ε) * ((dt : ℝ) - ℓ)) * (B.card : ℝ)) ∧
      (dt = ℓ → (Wt.P.toFinset.card : ℝ) ≤
        C₆₈ * ((At.card : ℝ) / (A.card : ℝ)) ^ K * (B.card : ℝ)) ∧
      (dt < ℓ → (Wt.P.toFinset.card : ℝ) ≤ C₆₈ * (B.card : ℝ)) := by
  classical
  have hγ1 : γ < 1 := by
    have hK : 0 < K := by
      have hβnn : (0 : ℝ) < 2 * (ℓ : ℝ) + β + 2 := by linarith [hβ]
      have hpos : (0 : ℝ) < 2 * (2 * ℓ + β + 2) / ε := by positivity
      linarith
    exact lt_of_le_of_lt hγδ (Real.rpow_lt_one hδ.le hδ1 hK)
  obtain ⟨d₀', hd₀'ℓ, ⟨W₀'⟩⟩ := hwit0
  have hwitneA : ∃ d', Nonempty (SubSumWitness A c' d') := ⟨d₀', ⟨W₀'⟩⟩
  set W0 := canonicalWitness A c' hwitneA
  have hdinit : SubSumDim A c' ≤ G ℓ := le_trans (subSumDim_le ⟨W₀'⟩) hd₀'ℓ
  set dinit := SubSumDim A c' with hdinitdef
  set P0 : ℝ :=
    C₆₈ * sMin ^ (-(max 0 ((dinit : ℝ) - (ℓ : ℝ)))) * (B.card : ℝ)
    with hP0def
  have hinit : (W0.P.toFinset.card : ℝ) ≤ P0 := by
    rw [hP0def]; exact lem68_initial_bound hBint hsub W0
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have hdinitD : dinit ≤ D :=
    le_trans hdinit (le_trans (Nat.le_add_right _ _) hGD)
  have hdinitv : (dinit : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdinitD
  have hsize0 : (A.card : ℝ) ^ (1 - ε / 2) ≤ (A.card : ℝ) := by
    calc (A.card : ℝ) ^ (1 - ε / 2)
        ≤ (A.card : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
      _ = (A.card : ℝ) := Real.rpow_one _
  have hP0b : P0 ≤ (A.card : ℝ) ^ (2 * ℓ + β + 2) := by
    rw [hP0def]
    have hr : sMin ^ (-(max 0 ((dinit : ℝ) - (ℓ : ℝ)))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hsMin.le
        (neg_nonpos.mpr (le_max_left _ _))
    calc C₆₈ * sMin ^ (-(max 0 ((dinit : ℝ) - (ℓ : ℝ)))) * (B.card : ℝ)
        ≤ C₆₈ * 1 * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hr hC₆₈.le) (Nat.cast_nonneg _)
      _ = C₆₈ * (B.card : ℝ) := by ring
      _ ≤ (A.card : ℝ) * (A.card : ℝ) ^ β :=
          mul_le_mul hC₆₈b hBβ (Nat.cast_nonneg _)
            (by linarith : (0 : ℝ) ≤ (A.card : ℝ))
      _ = (A.card : ℝ) ^ (1 + β) := by
          rw [Real.rpow_add (by linarith : (0 : ℝ) < (A.card : ℝ)),
            Real.rpow_one]
      _ ≤ (A.card : ℝ) ^ (2 * ℓ + β + 2) :=
          Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
  -- size-stop exclusion via `size_stop_absurd` (with `Q := D`)
  have hnostop : ∀ ⦃d : ℕ⦄ {X' : Finset (Fin d → ℤ)} (nd nu ns sd : ℕ)
      (W' : SubSumWitness X' c' (SubSumDim X' c')),
      (δ : ℝ) ^ (nd + nu + ns) * (A.card : ℝ) ≤ (X'.card : ℝ) →
      (W'.P.toFinset.card : ℝ) ≤
        C₆₈ ^ (nd + nu : ℕ) * γ ^ (ns : ℕ) * sMin ^ (-(sd : ℝ)) * P0 →
      (X'.card : ℝ) < (A.card : ℝ) ^ (1 - ε / 2) →
      (nd : ℝ) ≤ (dinit : ℝ) + sd → nu ≤ sd → False := by
    intro d X' nd nu ns sd W' hsize' hPb' hsmall' hnd' hnu'
    exact size_stop_absurd hδ hε hε3 hγ hγδ hKbig hβ hC₆₈ hC₆₈1 hsMin
      hsMinA hδA hLarg
      hsize' hsmall' hPb' hP0b W'.one_le_card_P hnd' hnu' hdinitv
  -- the initial stage
  have hsz0 : (δ : ℝ) ^ (0 + 0 + 0) * (A.card : ℝ) ≤ (A.card : ℝ) := by
    simp
  have hPb0 : (W0.P.toFinset.card : ℝ) ≤
      C₆₈ ^ ((0 : ℕ) + 0) * γ ^ (0 : ℕ) * sMin ^ (-((0 : ℕ) : ℝ)) * P0 := by
    simpa using hinit
  have hdim0 : (SubSumDim A c' : ℤ) =
      (dinit : ℤ) + ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) := by
    rw [hdinitdef]; push_cast; ring
  -- `|A| > 1` (from `hAvac` and `δ < 1`), needed for the dimension budget.
  have hAgt1' : (1 : ℝ) < (A.card : ℝ) := by
    have h1 : (1 : ℝ) < (A.card : ℝ) ^ (1 - ε / 2) := by
      have hδle : δ * (A.card : ℝ) ^ (1 - ε / 2) ≤
          1 * (A.card : ℝ) ^ (1 - ε / 2) :=
        mul_le_mul_of_nonneg_right hδ1.le
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      linarith [hAvac]
    by_contra hle
    push_neg at hle
    have hle' : (A.card : ℝ) ^ (1 - ε / 2) ≤ 1 :=
      Real.rpow_le_one (Nat.cast_nonneg _) hle (by linarith)
    linarith
  have hE : (0 : ℝ) ≤ 2 * (ℓ : ℝ) + β + 2 := by
    have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
    linarith
  have hdimcap : dinit + ⌈(2 * (ℓ : ℝ) + β + 2) / (1 - ε)⌉₊ ≤ D :=
    le_trans (Nat.add_le_add_right hdinit _) hGD
  refine (l10_descent hδ hε hγ hγ1 hC₆₈ hC₆₈1 hsMin hCs hβ'
    (by linarith) hAgt1' hE hsMinA hP0b hdimcap hAvac hmove hwit' hlb
    hnostop
    ⟨ℓ, A, DerivedFrom.refl, W0, hdinitD, hsize0, 0, 0, 0, 0, 0,
      hsz0, hPb0, hdim0, le_refl 0, le_refl 0⟩).elim ?_
  intro s' hirr
  have hδsMin : (1 / δ) ^ (2 * K) ≤ sMin := le_trans hδA hsMinA
  refine ⟨s'.n, s'.X, SubSumDim s'.X c', s'.W, s'.der,
    s'.der.nonAveraging hNA, ?_, s'.dim, hirr,
    final_P_bounds (β' := β') s' hβ hε hε3 hδ hδ1 hγ hγδ hKbig hC₆₈
      hC₆₈1 hsMin hA1 hsMinA hδsMin hBβ (le_of_eq hP0def)⟩
  exact le_trans
    (Real.rpow_le_rpow_of_exponent_le hA1 (by linarith : (1 - ε) ≤ 1 - ε / 2))
    s'.size

/-- **Lemma 10 (faithful form).**  The constants `c₀`, `c'` are *universal*:
they are produced before `∀ A` and cannot depend on `A` (the paper takes
`c₀` to be the Corollary-5 constant `c(ℓ,β)` — resp. the maximum of the
Corollary-5 constants `c(d',β')` over the finitely many reachable
dimensions `d' ≤ D`).  Consequently `Wt`'s field
`|At| − c₀⁻¹·|At|/log|At| ≤ |Ât|` is a genuine `|Ât| ≥ |At|(1−o(1))`
constraint, `dt ≥ 1`, and `Irreducible Wt c' δ γ` quantifies non-vacuously
over subsets of `ϕ_{P̃}(Ât)`.

The proof (paper §3.2): run the down/up/shrink moves
(`DerivedFrom.step_cases`) starting from `Ã₀ = ϕ_P(Â)`
(`exists_first_move`), stopping when `|A_{i+1}| ≤ |A|^{1−ε/2}` or
`d_{i+1} > d̄`; equation (8) gives
`|P_i| ≤ C^{|D|+|U|}·γ^{|S|}·∏_{j∈U}s(A_j)^{−(d_{j+1}−d_j)}·|P|`,
equation (9) bounds `Σ_{j∈U}(d_{j+1}−d_j) = O_β(1)` via `s(A_j) ≥
|A|^{1−ε}` and `|P| ≤ |A|^{O_β(1)}`, so the `d̄` threshold is never hit and
the size-stopping leads to `γ^{i−O(1)} ≤ |P|^{−10}` contradicting
`γ ≥ |A|^{−1/3}` — hence the process stops at `(δ,γ)`-irreducibility.
The remaining gap in the formalization: Lemmas 6 and 8
(`|P(A₁−x)| ≪_{d} s(A₁)^{−(d₁−d)}·|P|` for up-moves and
`|P(A₁−x)| ≪_d |P|` for down-moves), which need the covolume/discrete-John
machinery (Lemmas 7, 11–14), plus the `|U|+|D| = O_β(1)` bookkeeping —
only the elementary counting bounds `|P'| ≤ (2s'+1)^d·3^d·∏wᵢ` are
currently available (`SubSumWitness.card_P'_le_of_imageAh_sub_witness`). -/
theorem irreduciblization_faithful {β ε δ γ K : ℝ}
    (hβ : 1 < β) (hε : 0 < ε) (hε3 : ε < 1 / 3) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hγ : 0 < γ) (hγδ : γ ≤ δ ^ K)
    (hKbig : (2 : ℝ) * (2 * ℓ + β + 2) / ε < K) :
    ∃ (c₀ c' C : ℝ) (D N : ℕ), 0 < c₀ ∧ 0 < c' ∧ 0 < C ∧
      ∀ {A : Finset (Fin ℓ → ℤ)} {B : GAP.Box ℓ},
        B.IsInterval → NonAveraging A → A ⊆ B.toFinset →
        (B.card : ℝ) ≤ (A.card : ℝ) ^ β →
        (A.card : ℝ) ^ (-(1 : ℝ) / 3) ≤ γ → N ≤ A.card →
      ∃ (n : ℕ) (At : Finset (Fin n → ℤ)) (dt : ℕ)
        (Wt : SubSumWitness At c₀ dt),
        DerivedFrom A δ At ∧
        NonAveraging At ∧
        (A.card : ℝ) ^ (1 - ε) ≤ (At.card : ℝ) ∧
        dt ≤ D ∧
        Irreducible Wt c' δ γ ∧
        (ℓ < dt → (Wt.P.toFinset.card : ℝ) ≤
          C * (A.card : ℝ) ^ (-(1 - ε) * ((dt : ℝ) - ℓ)) * (B.card : ℝ)) ∧
        (dt = ℓ → (Wt.P.toFinset.card : ℝ) ≤
          C * ((At.card : ℝ) / (A.card : ℝ)) ^ K * (B.card : ℝ)) ∧
        (dt < ℓ → (Wt.P.toFinset.card : ℝ) ≤ C * (B.card : ℝ)) := by
  classical
  -- Constants: `c₀ := c'` (the uniform Cor-5 constant — this resolves the
  -- `c₀`-vs-`c'` witness mismatch by producing the final witness at `c'`
  -- itself), `C := C₆₈ := 1`, `sMin := 2`, `β' := 3β`.
  have hβ' : (0 : ℝ) < 3 * β := by linarith
  -- `F := ⌈(2ℓ+β+2)/(1-ε)⌉₊` is the iteration's dimension budget: the
  -- cap `D` covers `ℓ + G ℓ + F`, so every stage dimension is `≤ D`.
  obtain ⟨c', G, C₀, D, hc', hDG, hval⟩ :=
    uniform_cor5_bounded_exists (β' := 3 * β) (ℓ := ℓ) (by linarith)
      ⌈(2 * (ℓ : ℝ) + β + 2) / (1 - ε)⌉₊
  have hℓD : ℓ ≤ D := le_trans (by omega) hDG
  have hGD : G ℓ + ⌈(2 * (ℓ : ℝ) + β + 2) / (1 - ε)⌉₊ ≤ D :=
    le_trans (by omega) hDG
  -- `N`: the common largeness threshold covering `|A| ≥ 1`, the vacuity
  -- threshold `δ·|A|^{1−ε/2} > 1` and `C₀ d ≤ δ·|A|^{1−ε/2}` for all
  -- `d ≤ D`.
  set a : ℝ := 1 - ε / 2
  have ha : 0 < a := by dsimp [a]; linarith
  set Cmax := (Finset.range (D + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos D)⟩ fun d ↦ max (C₀ d) 0
  have hCmax0 : (0 : ℝ) ≤ Cmax := by
    show (0 : ℝ) ≤ (Finset.range (D + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos D)⟩ (fun d ↦ max (C₀ d) 0)
    exact le_trans (le_max_right _ _)
      (Finset.le_sup' (fun d ↦ max (C₀ d) 0)
        (Finset.mem_range.mpr (Nat.succ_pos D)))
  set T1 := (1 / δ) ^ (1 / a : ℝ)
  set T2 := (Cmax / δ) ^ (1 / a : ℝ)
  -- `T3`: makes `(1/δ)^{2K} ≤ |A|^{1-ε}` (the `δ^{-2K} ≤ sMin` input of
  -- `final_P_bounds`, with `sMin := |A|^{1-ε}`); `T4`: the largeness
  -- `K·t·Q ≤ (Kε/2 - (2ℓ+β+2))·log|A|` needed by `size_stop_absurd`.
  set T3 := (1 / δ) ^ (2 * K / (1 - ε))
  set T4 := Real.exp (K * Real.log (1 / δ) * (D : ℝ) /
    (K * ε / 2 - (2 * ℓ + β + 2)))
  set N := max 1 (⌈max T1 (max T2 (max T3 T4))⌉₊ + 1)
  refine ⟨c', c', 1, D, N, hc', hc', zero_lt_one, ?_⟩
  intro A B hBint hNA hsub hBβ hγA hN
  have hNR : (N : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hN
  have hA1 : (1 : ℝ) ≤ (A.card : ℝ) :=
    le_trans (by exact_mod_cast le_max_left 1 _ : (1 : ℝ) ≤ (N : ℝ)) hNR
  have hT1a : T1 ^ a = 1 / δ := by
    dsimp [T1]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / δ),
      div_mul_cancel₀ _ (ne_of_gt ha), Real.rpow_one]
  have hT2a : T2 ^ a = Cmax / δ := by
    dsimp [T2]
    rw [← Real.rpow_mul (div_nonneg hCmax0 hδ.le),
      div_mul_cancel₀ _ (ne_of_gt ha), Real.rpow_one]
  have hAgt : max T1 (max T2 (max T3 T4)) < (A.card : ℝ) := by
    have h1 : max T1 (max T2 (max T3 T4)) ≤
        (⌈max T1 (max T2 (max T3 T4))⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈max T1 (max T2 (max T3 T4))⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by
      have : ⌈max T1 (max T2 (max T3 T4))⌉₊ + 1 ≤ N := le_max_right _ _
      exact_mod_cast this
    have h3 : max T1 (max T2 (max T3 T4)) < (N : ℝ) := by linarith
    linarith
  have hAvac : (1 : ℝ) < δ * (A.card : ℝ) ^ a := by
    have h1 : T1 < (A.card : ℝ) := lt_of_le_of_lt (le_max_left _ _) hAgt
    have h2 : (0 : ℝ) ≤ T1 := by
      dsimp [T1]; positivity
    have h3 : T1 ^ a < (A.card : ℝ) ^ a :=
      Real.rpow_lt_rpow h2 h1 ha
    rw [hT1a] at h3
    have h4 : δ * (1 / δ) = 1 := mul_one_div_cancel (ne_of_gt hδ)
    calc (1 : ℝ) = δ * (1 / δ) := h4.symm
      _ < δ * (A.card : ℝ) ^ a := by
        apply mul_lt_mul_of_pos_left h3 hδ
  have hC₀bound : ∀ d ≤ D, (C₀ d : ℝ) ≤ δ * (A.card : ℝ) ^ a := by
    intro d hd
    have h1 : T2 < (A.card : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hAgt
    have h2 : (0 : ℝ) ≤ T2 := by
      dsimp [T2]
      exact Real.rpow_nonneg (div_nonneg hCmax0 hδ.le) _
    have h3 : T2 ^ a < (A.card : ℝ) ^ a :=
      Real.rpow_lt_rpow h2 h1 ha
    rw [hT2a] at h3
    have h4 : δ * (Cmax / δ) = Cmax := mul_div_cancel₀ _ (ne_of_gt hδ)
    have h5 : Cmax < δ * (A.card : ℝ) ^ a := by
      have h6 : δ * (Cmax / δ) < δ * (A.card : ℝ) ^ a :=
        mul_lt_mul_of_pos_left h3 hδ
      rwa [h4] at h6
    have h7 : (C₀ d : ℝ) ≤ Cmax := by
      have hmem : d ∈ Finset.range (D + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hd)
      have h8 : max (C₀ d) 0 ≤ Cmax := by
        show max (C₀ d) 0 ≤ (Finset.range (D + 1)).sup'
          ⟨d, hmem⟩ (fun d ↦ max (C₀ d) 0)
        exact Finset.le_sup' (fun d ↦ max (C₀ d) 0) hmem
      exact le_trans (le_max_left _ _) h8
    linarith
  -- the residual hypotheses, then `iterates_to_irreducible`
  have hwit0 : ∃ d' ≤ G ℓ, Nonempty (SubSumWitness A c' d') := by
    have hB3 : (B.card : ℝ) ≤ (A.card : ℝ) ^ (3 * β) :=
      le_trans hBβ (Real.rpow_le_rpow_of_exponent_le hA1 (by linarith))
    have hC₀ℓ : (C₀ ℓ : ℝ) ≤ (A.card : ℝ) := by
      have h1 := hC₀bound ℓ hℓD
      have h2 : δ * (A.card : ℝ) ^ a ≤ (A.card : ℝ) := by
        have h3 : (A.card : ℝ) ^ a ≤ (A.card : ℝ) := by
          dsimp [a]
          calc (A.card : ℝ) ^ (1 - ε / 2)
              ≤ (A.card : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
            _ = (A.card : ℝ) := Real.rpow_one _
        calc δ * (A.card : ℝ) ^ a ≤ 1 * (A.card : ℝ) ^ a :=
              mul_le_mul_of_nonneg_right hδ1.le
                (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          _ = (A.card : ℝ) ^ a := one_mul _
          _ ≤ (A.card : ℝ) := h3
      linarith
    exact hval hℓD hBint hsub hB3 hC₀ℓ
  have hwit' : ∀ ⦃d : ℕ⦄, d ≤ D →
      ∀ {X : Finset (Fin d → ℤ)} {B' : GAP.Box d},
      B'.IsInterval → X ⊆ B'.toFinset → (B'.card : ℝ) ≤ (X.card : ℝ) ^ (3 * β) →
      δ * (A.card : ℝ) ^ a ≤ (X.card : ℝ) →
      ∃ d', Nonempty (SubSumWitness X c' d') := by
    intro d hd X B' hBi hsubX hBX hthr
    have hC₀d : (C₀ d : ℝ) ≤ (X.card : ℝ) :=
      le_trans (hC₀bound d hd) hthr
    exact (hval hd hBi hsubX hBX hC₀d).imp fun d' h ↦ h.2
  -- `|A| > 1` (since `δ·|A|^a > 1` and `δ ≤ 1`), giving `sMin := |A|^{1-ε} > 1`.
  have hAgt1 : (1 : ℝ) < (A.card : ℝ) := by
    have h1 : (1 : ℝ) < (A.card : ℝ) ^ a := by
      have hδle : δ * (A.card : ℝ) ^ a ≤ 1 * (A.card : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hδ1.le
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      linarith [hAvac]
    by_contra hle
    push_neg at hle
    have hle' : (A.card : ℝ) ^ a ≤ 1 :=
      Real.rpow_le_one (Nat.cast_nonneg _) hle ha.le
    linarith
  have hsMin' : (1 : ℝ) < (A.card : ℝ) ^ (1 - ε) :=
    Real.one_lt_rpow hAgt1 (by linarith : (0 : ℝ) < 1 - ε)
  -- `(1/δ)^{2K} ≤ |A|^{1-ε}` from `N ≥ T3` (the `δ^{-2K} ≤ sMin` input).
  have hδA : (1 / δ) ^ (2 * K) ≤ (A.card : ℝ) ^ (1 - ε) := by
    have h1ε : (0 : ℝ) < 1 - ε := by linarith
    have hT3le : T3 ≤ (A.card : ℝ) :=
      le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) hAgt.le))
    have hT3eq : T3 ^ (1 - ε) = (1 / δ) ^ (2 * K) := by
      dsimp [T3]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / δ),
        div_mul_cancel₀ _ (ne_of_gt h1ε)]
    rw [← hT3eq]
    exact Real.rpow_le_rpow (by dsimp [T3]; positivity) hT3le h1ε.le
  -- `K·t·Q ≤ (Kε/2 − (2ℓ+β+2))·log|A|` from `N ≥ T4` (the `size_stop_absurd`
  -- largeness input); `Δ' > 0` follows from the strict `hKbig`.
  have hLarg : K * Real.log (1 / δ) * (D : ℝ) ≤
      (K * ε / 2 - (2 * ℓ + β + 2)) * Real.log (A.card : ℝ) := by
    have hΔ' : (0 : ℝ) < K * ε / 2 - (2 * ℓ + β + 2) := by
      have h := (div_lt_iff₀ hε).mp hKbig
      linarith [h]
    have hT4le : T4 ≤ (A.card : ℝ) :=
      le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) hAgt.le))
    have hexp' : Real.log T4 = K * Real.log (1 / δ) *
        (D : ℝ) / (K * ε / 2 - (2 * ℓ + β + 2)) := by
      dsimp [T4]
      rw [Real.log_exp]
    have hlog : K * Real.log (1 / δ) * (D : ℝ) /
        (K * ε / 2 - (2 * ℓ + β + 2)) ≤ Real.log (A.card : ℝ) := by
      rw [← hexp']
      exact Real.log_le_log (by dsimp [T4]; exact Real.exp_pos _) hT4le
    have h := (div_le_iff₀ hΔ').mp hlog
    linarith [h]
  -- The `K ≥ C_{β,ε}` input (eq. (10)) is now the explicit strict
  -- hypothesis `hKbig`, and `sMin := |A|^{1-ε}` (the paper's `s(A_j) ≥
  -- |A|^{1-ε}` bookkeeping), `C₆₈ := 1`.
  exact iterates_to_irreducible hβ hε hε3 hδ hδ1 hγ hγδ hKbig hc'
    zero_lt_one hsMin'
    (by simpa using hsMin') hβ' hℓD hGD
    hBint hNA hsub hBβ hA1 hA1 hAvac
    (le_refl 1) (le_refl _) hδA hLarg
    lem68_move_bound hwit0 hwit'
      (by intro n d X A₁ x W hA₁ hx hcard
          exact moved_set_is_lb W hA₁ hx hcard)

end Nonaveraging
