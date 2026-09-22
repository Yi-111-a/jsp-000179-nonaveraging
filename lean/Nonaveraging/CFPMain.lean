import Nonaveraging.GAP

/-!
# Toward `cfp_main` (CFP23, Theorem 1.5) — honest partial development

`cfp_main` in `Nonaveraging/GAP.lean` is the `ℓ = 1` instance of the
Conlon–Fox–Pham structure theorem (arXiv:2311.01416, Theorem 1.5, quoted as
Theorem 5 in arXiv:2410.14624v2 Appendix A).  It is the deep external input
of the whole project; its proof in the literature occupies most of a ~50-page
paper.  A complete formalisation is therefore not feasible in this file.
What this file does instead, **without any `sorry`/`admit`/`axiom`**, is:

1. **Discharge every conjunct of the conclusion that is elementary.**
   `cfp_main_easy_part` proves, for `c = d = 1`, that one may always take
   `Â = A` and `P = intInterval n` (the symmetric interval `[-n, n]`) to
   satisfy `Â ⊆ A`, the cardinality lower bound, `d' ≤ d`, `P.Symmetric`,
   `P.Homogeneous`, `P.Proper` and `(Â ∪ {0}) ⊆ P.toFinset`.  The *only*
   missing conjunct is the joint package
   `∃ A' ⊆ Â, |A'| ≤ s, ∃ k ≤ c·s, ∃ t, kP + t ⊆ Σ(A') ∧ kP proper`.

2. **Isolate the residual faithfully.**  `cfpInput` is exactly the inner
   `∀`-statement of `cfp_main`, i.e. CFP23 Theorem 1.5 verbatim (with the
   Corollary-5 symmetric/homogeneous strengthening).  `cfp_main_proof_of_cfpInput`
   shows the reduction is tautologically tight: the theorem *is* the residual.

   *Why the residual cannot be stated with a fixed `P`:* taking
   `P = intInterval n` forces `kP + t ⊆ Σ(A') ⊆ bℤ` whenever `A ⊆ bℤ`
   (e.g. `A = {b, 2b, …, mb}` with `b ≈ n/m ≈ m^{β-1}`), which requires
   `b ∣ k`, hence `k ≥ b ≈ m^{β-1} ≫ c·s` — contradiction.  So `P` must adapt
   to the modular/arithmetic structure of `A`, which is precisely the content
   of the CFP theorem.

3. **Provide the reusable machinery** that any eventual proof (or a proof of
   special cases) needs:
   * `GAP.intInterval`, its membership criterion, and proofs that it is
     `Symmetric`, `Homogeneous`, `Proper` and contains any `|·|`-bounded set;
   * `GAP.Proper.smul`/`nsmul`/`translate`: properness is preserved by
     nonzero dilation and translation (the `(k•P).Proper` clause);
   * `GAP.subsetSumsL` API: `0 ∈ Σ(A)`, monotonicity, the insert formula
     `Σ(A ∪ {b}) = Σ(A) ∪ (Σ(A) + b)`, the **completeness step**
     (`coordIcc_subset_subsetSumsL_insert`), its iteration
     (`coordIcc_subset_subsetSumsL_natInterval`: `{1,…,u}` has
     `[0, u(u+1)/2] ⊆ Σ`), and the span bound `subsetSumsL_mem_Icc`;
   * `GAP.toFinset_subset_centered_snoc`: every GAP embeds in a symmetric,
     homogeneous GAP of dimension `d+1` (containment only — properness is
     *not* preserved in general, which is why the symmetric strengthening
     stays inside the residual).

## Status

`theorem cfp_main_proof` with the required signature is **not** asserted here:
it is exactly `cfp_main_proof_of_cfpInput` applied to a proof of `cfpInput`,
and `cfpInput` is the unproved CFP23 main theorem.  See
`discovery/JSP-000179/scratch/round5_cfpmain_report.md`.
-/

open Finset

namespace Nonaveraging

namespace GAP

/-! ### The symmetric interval GAP `[-N, N]` in `ℤ` -/

/-- The one-dimensional symmetric interval GAP `{x : |x 0| ≤ N}`, as a
`GAP 1 1`: `centered` with a single step `(1)` of width `2N + 1`.  This is the
canonical trivial covering GAP for anchored/symmetric `A ⊆ [-N, N]`. -/
def intInterval (N : ℕ) : GAP 1 1 :=
  centered (fun _ ↦ fun _ ↦ (1 : ℤ)) (fun _ ↦ N)

theorem intInterval_eval (N : ℕ) (n : Fin 1 → ℕ) :
    (intInterval N).eval n = fun _ ↦ (n 0 : ℤ) - (N : ℤ) := by
  funext i
  rw [Fin.eq_zero i]
  show ((centered (fun _ ↦ fun _ ↦ (1 : ℤ)) (fun _ ↦ N)).eval n) 0 = _
  rw [centered_eval, Fin.sum_univ_one]
  simp [Pi.smul_apply, smul_eq_mul]

/-- Membership in the interval GAP is exactly the coordinate bound. -/
theorem mem_intInterval {N : ℕ} {x : Fin 1 → ℤ} :
    x ∈ (intInterval N).toFinset ↔ |x 0| ≤ (N : ℤ) := by
  rw [intInterval, mem_centered]
  constructor
  · rintro ⟨r, hr, hrx⟩
    have hx0 : x 0 = r 0 := by
      have h := congrFun hrx 0
      rwa [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, mul_one] at h
    rw [hx0]
    exact hr 0
  · intro hx
    refine ⟨fun _ ↦ x 0, fun i ↦ ?_, ?_⟩
    · rw [Fin.eq_zero i]
      exact hx
    · funext i
      rw [Fin.eq_zero i, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, mul_one]

theorem intInterval_symmetric (N : ℕ) : (intInterval N).Symmetric :=
  centered_symmetric _ _

theorem intInterval_homogeneous (N : ℕ) : (intInterval N).Homogeneous :=
  centered_homogeneous _ _

/-- The interval GAP is proper: the coordinate of `eval n` is `n 0 - N`. -/
theorem intInterval_proper (N : ℕ) : (intInterval N).Proper := by
  intro a _ b _ h
  have h0 := congrFun h 0
  rw [intInterval_eval, intInterval_eval] at h0
  have hab : a 0 = b 0 := by
    have h1 : (a 0 : ℤ) - (N : ℤ) = (b 0 : ℤ) - (N : ℤ) := h0
    omega
  funext i
  rw [Fin.eq_zero i]
  exact hab

theorem subset_intInterval {N : ℕ} {A : Finset (Fin 1 → ℤ)}
    (hA : ∀ a ∈ A, |a 0| ≤ (N : ℤ)) : A ⊆ (intInterval N).toFinset :=
  fun a ha ↦ mem_intInterval.mpr (hA a ha)

theorem zero_mem_intInterval (N : ℕ) :
    (0 : Fin 1 → ℤ) ∈ (intInterval N).toFinset :=
  mem_intInterval.mpr (by simp)

theorem union_subset_intInterval {N : ℕ} {A : Finset (Fin 1 → ℤ)}
    (hA : ∀ a ∈ A, |a 0| ≤ (N : ℤ)) :
    (A ∪ {0}) ⊆ (intInterval N).toFinset :=
  Finset.union_subset (subset_intInterval hA)
    (Finset.singleton_subset_iff.mpr (zero_mem_intInterval N))

/-- The cardinality of the interval GAP is `2N + 1` (it is proper). -/
theorem card_intInterval (N : ℕ) : (intInterval N).toFinset.card = 2 * N + 1 := by
  rw [card_toFinset_of_proper _ (intInterval_proper N), Fin.prod_univ_one]
  rfl

/-! ### Properness under dilation and translation -/

/-- Nonzero dilation preserves properness: `k • eval` is injective when
`k ≠ 0`, since `ℤ^ℓ` is `ℤ`-torsion-free.  This is the `(k•P).Proper`
conjunct of `cfp_main`. -/
theorem Proper.smul {ℓ d : ℕ} {P : GAP ℓ d} (hP : P.Proper) {k : ℤ}
    (hk : k ≠ 0) : (k • P).Proper := by
  intro a ha b hb h
  rw [smul_coeffs] at ha hb
  apply hP ha hb
  have h2 : k • P.eval a = k • P.eval b := by
    have h' : (k • P).eval a = (k • P).eval b := h
    rwa [smul_eval, smul_eval] at h'
  funext j
  have hj := congrFun h2 j
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hj
  exact mul_left_cancel₀ hk hj

/-- Natural-number version of `Proper.smul` (the `k • P` of `cfp_main`). -/
theorem Proper.nsmul {ℓ d : ℕ} {P : GAP ℓ d} (hP : P.Proper) {k : ℕ}
    (hk : 0 < k) : (k • P).Proper := by
  rw [nsmul_eq_zsmul]
  exact Proper.smul hP (by exact_mod_cast hk.ne')

/-- Translation preserves properness. -/
theorem Proper.translate {ℓ d : ℕ} {P : GAP ℓ d} (hP : P.Proper)
    (t : Fin ℓ → ℤ) : (P.translate t).Proper := by
  intro a ha b hb h
  rw [translate_coeffs] at ha hb
  apply hP ha hb
  rw [translate_eval, translate_eval] at h
  exact add_left_cancel h

/-! ### `subsetSumsL` basics -/

theorem zero_mem_subsetSumsL {ℓ : ℕ} (A : Finset (Fin ℓ → ℤ)) :
    (0 : Fin ℓ → ℤ) ∈ subsetSumsL A :=
  mem_subsetSumsL.mpr ⟨∅, Finset.empty_subset _, by simp⟩

theorem subsetSumsL_mono {ℓ : ℕ} {A B : Finset (Fin ℓ → ℤ)} (h : A ⊆ B) :
    subsetSumsL A ⊆ subsetSumsL B := by
  intro x hx
  obtain ⟨S, hS, hsum⟩ := mem_subsetSumsL.mp hx
  exact mem_subsetSumsL.mpr ⟨S, hS.trans h, hsum⟩

theorem singleton_mem_subsetSumsL {ℓ : ℕ} {A : Finset (Fin ℓ → ℤ)} {a : Fin ℓ → ℤ}
    (ha : a ∈ A) : a ∈ subsetSumsL A :=
  mem_subsetSumsL.mpr ⟨{a}, Finset.singleton_subset_iff.mpr ha, by simp⟩

/-- The subset sums of an insert split: `Σ(A ∪ {b}) = Σ(A) ∪ (Σ(A) + b)`. -/
theorem subsetSumsL_insert {ℓ : ℕ} {A : Finset (Fin ℓ → ℤ)} {b : Fin ℓ → ℤ}
    (hb : b ∉ A) :
    subsetSumsL (insert b A) =
      subsetSumsL A ∪ (subsetSumsL A).image (· + b) := by
  ext x
  rw [mem_subsetSumsL, Finset.mem_union, mem_subsetSumsL]
  simp only [Finset.mem_image, mem_subsetSumsL]
  constructor
  · rintro ⟨S, hS, hsum⟩
    by_cases hbS : b ∈ S
    · right
      refine ⟨∑ y ∈ S.erase b, y, ⟨S.erase b, ?_, rfl⟩, ?_⟩
      · exact (Finset.erase_subset _ _).trans
          (Finset.subset_insert_iff.mp hS)
      · have e : (∑ x ∈ S, x) = b + ∑ y ∈ S.erase b, y := by
          conv_lhs => rw [← Finset.insert_erase hbS]
          exact Finset.sum_insert (Finset.notMem_erase _ _)
        rw [← hsum, e]
        exact add_comm _ _
    · left
      refine ⟨S, ?_, hsum⟩
      have := Finset.subset_insert_iff.mp hS
      rwa [Finset.erase_eq_of_notMem hbS] at this
  · rintro (⟨S, hS, hsum⟩ | ⟨y, ⟨S, hS, hsum⟩, rfl⟩)
    · exact ⟨S, hS.trans (Finset.subset_insert _ _), hsum⟩
    · refine ⟨insert b S, Finset.insert_subset_insert _ hS, ?_⟩
      rw [Finset.sum_insert (fun h ↦ hb (hS h)), hsum]
      exact add_comm _ _

/-! ### The interval (completeness) mechanism inside `Σ(A)`

If `Σ(A)` already covers `[0, L]` (as coordinate values), then adjoining an
element `b ∈ [0, L+1]` extends the covered interval to `[0, L + b]`.  This is
the induction step of the classical *completeness* argument (Freiman,
Erdős–Ginzburg folklore): subset sums fill an initial interval as long as no
element exceeds one more than the current sum. -/

/-- The points of `Fin 1 → ℤ` whose coordinate lies in `[0, L]`. -/
def coordIcc (L : ℤ) : Finset (Fin 1 → ℤ) :=
  (Finset.Icc 0 L).image fun i ↦ fun _ : Fin 1 ↦ i

theorem mem_coordIcc {L : ℤ} {x : Fin 1 → ℤ} :
    x ∈ coordIcc L ↔ 0 ≤ x 0 ∧ x 0 ≤ L := by
  rw [coordIcc, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_Icc.mp hi
  · rintro ⟨h1, h2⟩
    exact ⟨x 0, Finset.mem_Icc.mpr ⟨h1, h2⟩,
      funext fun i ↦ by rw [Fin.eq_zero i]⟩

/-- **Completeness step**: adjoining `b` with `0 ≤ b 0 ≤ L + 1` to `A`
extends the `Σ`-covered interval from `[0, L]` to `[0, L + b 0]`. -/
theorem coordIcc_subset_subsetSumsL_insert {L : ℤ} {A : Finset (Fin 1 → ℤ)}
    {b : Fin 1 → ℤ} (hb : b ∉ A) (hb0 : 0 ≤ b 0) (hbL : b 0 ≤ L + 1)
    (hA : coordIcc L ⊆ subsetSumsL A) :
    coordIcc (L + b 0) ⊆ subsetSumsL (insert b A) := by
  rw [subsetSumsL_insert hb]
  intro x hx
  rw [mem_coordIcc] at hx
  by_cases h : x 0 ≤ L
  · exact Finset.subset_union_left (hA (mem_coordIcc.mpr ⟨hx.1, h⟩))
  · apply Finset.subset_union_right
    refine Finset.mem_image.mpr ⟨x - b, ?_, by simp⟩
    apply hA
    rw [mem_coordIcc]
    have hsub : (x - b) 0 = x 0 - b 0 := Pi.sub_apply _ _ _
    rw [hsub]
    constructor <;> omega

/-- The points `{1, 2, …, u}` of `Fin 1 → ℤ`. -/
def natInterval (u : ℕ) : Finset (Fin 1 → ℤ) :=
  (Finset.range u).image fun i ↦ fun _ : Fin 1 ↦ (i : ℤ) + 1

/-- Iterating the completeness step: the subset sums of `{1, …, u}` contain
the full interval `[0, 1 + 2 + … + u]`. -/
theorem coordIcc_subset_subsetSumsL_natInterval (u : ℕ) :
    coordIcc (∑ i ∈ Finset.range u, ((i : ℤ) + 1)) ⊆
      subsetSumsL (natInterval u) := by
  induction u with
  | zero =>
    intro x hx
    rw [mem_coordIcc, Finset.sum_range_zero] at hx
    have hx0 : x = 0 := by
      funext i
      rw [Fin.eq_zero i]
      omega
    rw [hx0]
    exact zero_mem_subsetSumsL _
  | succ u ih =>
    have hsplit : natInterval (u + 1) =
        insert (fun _ : Fin 1 ↦ ((u : ℤ) + 1)) (natInterval u) := by
      rw [natInterval, Finset.range_succ, Finset.image_insert]
    have hnotmem : (fun _ : Fin 1 ↦ ((u : ℤ) + 1)) ∉ natInterval u := by
      intro h
      rw [natInterval, Finset.mem_image] at h
      obtain ⟨i, hi, hxi⟩ := h
      have hc := congrFun hxi 0
      rw [Finset.mem_range] at hi
      simp only at hc
      omega
    rw [hsplit, Finset.sum_range_succ]
    refine coordIcc_subset_subsetSumsL_insert hnotmem (by simp) ?_ ih
    have hle : (u : ℤ) ≤ ∑ i ∈ Finset.range u, ((i : ℤ) + 1) := by
      calc (u : ℤ) = ∑ _i ∈ Finset.range u, (1 : ℤ) := by simp
        _ ≤ ∑ i ∈ Finset.range u, ((i : ℤ) + 1) :=
            Finset.sum_le_sum fun i _ ↦ by simp
    show ((fun _ : Fin 1 ↦ ((u : ℤ) + 1)) 0) ≤ _
    simp only
    linarith

/-- The Gauss sum `2·(1 + ⋯ + u) = u·(u+1)`. -/
theorem sum_range_add_one (u : ℕ) :
    (∑ i ∈ Finset.range u, ((i : ℤ) + 1)) * 2 = (u : ℤ) * ((u : ℤ) + 1) := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

/-- Packaged form: `Σ({1,…,u}) ⊇ [0, u(u+1)/2]`. -/
theorem coordIcc_subset_subsetSumsL_natInterval' (u : ℕ) :
    coordIcc ((u : ℤ) * (u + 1) / 2) ⊆ subsetSumsL (natInterval u) := by
  have h := coordIcc_subset_subsetSumsL_natInterval u
  have h2 := sum_range_add_one u
  have hσ : (∑ i ∈ Finset.range u, ((i : ℤ) + 1)) = (u : ℤ) * (u + 1) / 2 := by
    omega
  rw [hσ] at h
  exact h

/-- Every element of `natInterval u` lies in `[1, u]`. -/
theorem natInterval_mem {u : ℕ} {x : Fin 1 → ℤ} (hx : x ∈ natInterval u) :
    1 ≤ x 0 ∧ x 0 ≤ (u : ℤ) := by
  rw [natInterval, Finset.mem_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Finset.mem_range] at hi
  constructor <;> simp only [] <;> omega

/-- **Span bound**: subset sums of an `[0, M]`-valued set stay in
`[0, |A|·M]` — the trivial range control used in the Appendix-A `H`-sizing. -/
theorem subsetSumsL_mem_Icc {A : Finset (Fin 1 → ℤ)} {M : ℤ}
    (hM : ∀ a ∈ A, 0 ≤ a 0 ∧ a 0 ≤ M) {σ : Fin 1 → ℤ}
    (hσ : σ ∈ subsetSumsL A) : 0 ≤ σ 0 ∧ σ 0 ≤ (A.card : ℤ) * M := by
  obtain ⟨S, hS, rfl⟩ := mem_subsetSumsL.mp hσ
  constructor
  · rw [Finset.sum_apply]
    exact Finset.sum_nonneg fun a ha ↦ (hM a (hS ha)).1
  · rw [Finset.sum_apply]
    have hM0 : (0 : ℤ) ≤ M := by
      rcases A.eq_empty_or_nonempty with hAe | hAe
      · rw [hAe] at hS
        exact absurd (Finset.empty_subset _ hS ▸ hS) (by simp)
      · obtain ⟨a, ha⟩ := hAe
        exact (hM a ha).1.trans (hM a ha).2
    calc ∑ a ∈ S, a 0 ≤ ∑ _a ∈ S, M :=
          Finset.sum_le_sum fun a ha ↦ (hM a (hS ha)).2
      _ = (S.card : ℤ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A.card : ℤ) * M :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast Finset.card_le_card hS) hM0

/-! ### Symmetrization containment

Every `d`-dimensional GAP embeds in a symmetric, homogeneous `d+1`-dimensional
GAP: adjoin the base as an extra step of width `3 ∋ {-1,0,1}` (coefficient
`1`) and symmetrize the widths to `wᵢ - 1`.  **Caveat:** properness is not
preserved — the new step can create relations — which is why the
symmetric/homogeneous requirement remains part of the residual input. -/

theorem toFinset_subset_centered_snoc {ℓ d : ℕ} (P : GAP ℓ d) :
    P.toFinset ⊆
      (centered (Fin.snoc P.step P.base)
        (Fin.snoc (fun i ↦ P.width i - 1) 1)).toFinset := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  rw [mem_centered]
  refine ⟨Fin.snoc (fun i ↦ (n i : ℤ)) 1, fun i ↦ ?_, ?_⟩
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      have hlt := coeff_mem_width hn j
      have hw : (1 : ℤ) ≤ (P.width j : ℤ) := by exact_mod_cast hlt
      have hcast : ((P.width j - 1 : ℕ) : ℤ) = (P.width j : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ P.width j)]
        simp
      rw [abs_le, hcast]
      constructor <;> omega
    · rw [Fin.snoc_last, Fin.snoc_last]
      simp
  · show P.eval n = ∑ i : Fin (d + 1),
        (Fin.snoc (fun i ↦ (n i : ℤ)) 1) i • (Fin.snoc P.step P.base) i
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    show P.base + ∑ i, (n i : ℤ) • P.step i =
      ∑ i, (n i : ℤ) • P.step i + 1 • P.base
    rw [one_smul]
    exact add_comm _ _

end GAP

/-! ### The elementary part of `cfp_main`

For `c = d = 1`, `Â = A` and `P = intInterval n`, every conjunct of the
`cfp_main` conclusion *except* the `Σ(A') ⊇ kP + t` package holds. -/

theorem cfp_main_easy_part {β η : ℝ} (hβ : 1 < β) (hη : 0 < η) (hη1 : η < 1) :
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
          (Â ∪ {0}) ⊆ P.toFinset := by
  refine ⟨1, 1, one_pos, one_pos, fun A n s hne hAn _ _ _ ↦ ?_⟩
  have hlog : 0 ≤ Real.log (A.card : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Finset.card_pos.mpr hne
  refine ⟨A, 1, GAP.intInterval n, Finset.Subset.rfl, ?_, le_rfl,
    GAP.intInterval_symmetric n, GAP.intInterval_homogeneous n,
    GAP.intInterval_proper n, ?_⟩
  · have hnn : (0 : ℝ) ≤ (1 : ℝ)⁻¹ * s * Real.log A.card :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hlog
    linarith
  · apply GAP.union_subset_intInterval
    intro a ha
    obtain ⟨h1, h2⟩ := hAn a ha
    rw [abs_le]
    constructor <;> omega

/-! ### The isolated residual

`cfpInput c d` is the inner `∀`-statement of `cfp_main`: CFP23 Theorem 1.5
verbatim, including the Corollary-5 strengthening that `P` may be taken
symmetric and homogeneous (and `kP` proper).  By `cfp_main_easy_part`, the
*only* mathematically nontrivial content inside it is the joint package

  `∃ Â ⊆ A` (large), `∃ P ∋ Â ∪ {0}` (proper GAP, dim `≤ d`),
  `∃ A' ⊆ Â`, `|A'| ≤ s`, `∃ k ≤ c·s`, `∃ t`: `kP + t ⊆ Σ(A')`, `kP` proper —

which cannot be decomposed further: `P` must simultaneously cover almost all
of `A` and have a bounded dilation inside the `≤ s`-generated subset sums. -/

/-- **The residual input**: the per-`c`,`d` inner statement of `cfp_main`,
i.e. CFP23 Theorem 1.5 (arXiv:2311.01416) as quoted in arXiv:2410.14624v2
Theorem 5, with the symmetric/homogeneous strengthening of its Corollary. -/
def cfpInput {β η : ℝ} (c d : ℝ) : Prop :=
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
            (k • P).Proper

/-- **Conditional `cfp_main`**: the exact `cfp_main` statement follows from
the residual input — the reduction is tautologically tight, meaning the
residual *is* the missing mathematical content, not a strengthening of it.

`theorem cfp_main_proof` (the required signature) is precisely this theorem
applied to a proof of `∃ c d, 0 < c ∧ 0 < d ∧ cfpInput c d` — i.e., to
CFP23 Theorem 1.5. -/
theorem cfp_main_proof_of_cfpInput {β η : ℝ} (hβ : 1 < β) (hη : 0 < η)
    (hη1 : η < 1)
    (h : ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ @cfpInput β η c d) :
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
                (k • P).Proper :=
  h

end Nonaveraging
