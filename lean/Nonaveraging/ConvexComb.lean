import Mathlib

/-!
# Balanced convex combinations (Pham–Zakharov, arXiv:2410.14624v2, eq. (12))

If `A₀ ⊆ ℝ^d` is a finite set, `μ > 0`, and every closed halfspace through `a`
contains strictly more than `μ * |A₀|` points of `A₀`, then `a` can be written
as a convex combination of the points of `A₀` in which every point receives
weight at most `(μ * |A₀|)⁻¹`.

The proof follows the paper: the set of achievable convex combinations is the
image of a compact convex coefficient polytope under a linear map, hence compact
and convex.  If `0` were not achievable, the geometric Hahn–Banach theorem
(strict separation) would produce a halfspace through `a` with at most
`μ * |A₀|` points, contradicting the hypothesis.
-/

open scoped BigOperators

section

variable {d : ℕ}

/-- Strict separation of `0` from a nonempty compact convex set
`K ⊆ Fin d → ℝ` not containing it: some `u : Fin d → ℝ` satisfies
`∑ i, u i * y i < 0` for all `y ∈ K`.  Obtained from the geometric
Hahn–Banach theorem plus the decomposition of a continuous linear functional
on `Fin d → ℝ` along the coordinate vectors. -/
private theorem exists_forall_sum_lt_zero {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (_hne : K.Nonempty) (hconv : Convex ℝ K)
    (h0 : (0 : Fin d → ℝ) ∉ K) :
    ∃ u : Fin d → ℝ, ∀ y ∈ K, ∑ i, u i * y i < 0 := by
  classical
  obtain ⟨f, u', v, hfK, huv, hv0⟩ :=
    geometric_hahn_banach_compact_closed hconv hK (convex_singleton 0)
      isClosed_singleton (Set.disjoint_singleton_right.mpr h0)
  have hv0' : v < 0 := by
    have h := hv0 0 (Set.mem_singleton_iff.mpr rfl)
    rwa [map_zero] at h
  refine ⟨fun i ↦ f (Pi.single i (1 : ℝ)), fun y hy ↦ ?_⟩
  have hfy : f y = ∑ i : Fin d, (y i) * f (Pi.single i (1 : ℝ)) := by
    have hy : y = ∑ i : Fin d, y i • Pi.single i (1 : ℝ) :=
      (Finset.univ_sum_single y).symm.trans
        (Finset.sum_congr rfl fun i _ ↦ by
          rw [← Pi.single_smul, smul_eq_mul, mul_one])
    conv_lhs => rw [hy]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
  have hfy0 : f y < 0 := lt_trans (hfK y hy) (lt_trans huv hv0')
  have heq : (∑ i : Fin d, f (Pi.single i (1 : ℝ)) * y i) = f y := by
    rw [hfy]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  show (∑ i : Fin d, f (Pi.single i (1 : ℝ)) * y i) < 0
  rwa [heq]

/-- The coefficient polytope argument.  The set
`K = {∑_{x ∈ A₀} c x • (x - a) | 0 ≤ c x ≤ (μ·|A₀|)⁻¹, ∑ c = 1}` is a compact
convex subset of `Fin d → ℝ` (linear image of a product of intervals
intersected with a hyperplane).  If `0 ∉ K`, the separating direction `u` has
`∑ i, u i * y i < 0` on `K`, but the hypothesis gives `> μ·|A₀|` points `x`
with `∑ i, u i * (x - a) i ≥ 0`, and putting equal weight on them yields a
point of `K` with nonnegative pairing — a contradiction. -/
private theorem exists_balanced_combination_aux {A₀ : Finset (Fin d → ℝ)}
    {a : Fin d → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (H : ∀ (u : Fin d → ℝ) (t : ℝ), t ≤ ∑ i, u i * a i →
      μ * (A₀.card : ℝ) <
        ((A₀.filter fun x ↦ t ≤ ∑ i, u i * x i).card : ℝ)) :
    ∃ c : ↥A₀ → ℝ,
      (∀ x : ↥A₀, 0 ≤ c x) ∧ (∀ x : ↥A₀, c x ≤ (μ * A₀.card)⁻¹) ∧
      (∑ x : ↥A₀, c x = 1) ∧ (∑ x : ↥A₀, c x • ((x : Fin d → ℝ) - a) = 0) := by
  classical
  -- From `H` at `u = 0`, `t = 0`: `A₀` is nonempty and `μ * card ≤ card`.
  have hcardpos : (0 : ℝ) < A₀.card := by
    have h := H 0 0 (by simp)
    rw [Finset.filter_true_of_mem
      (fun x _ ↦ by simp : ∀ x ∈ A₀, (0 : ℝ) ≤ ∑ i, (0 : Fin d → ℝ) i * x i)] at h
    rcases Nat.eq_zero_or_pos A₀.card with h0 | h0
    · rw [h0] at h
      simp at h
    · exact_mod_cast h0
  have hμcard : μ * (A₀.card : ℝ) ≤ A₀.card := by
    have h := H 0 0 (by simp)
    rw [Finset.filter_true_of_mem
      (fun x _ ↦ by simp : ∀ x ∈ A₀, (0 : ℝ) ≤ ∑ i, (0 : Fin d → ℝ) i * x i)] at h
    exact h.le
  have hμcpos : (0 : ℝ) < μ * A₀.card := mul_pos hμ hcardpos
  have hwpos : (0 : ℝ) < (μ * A₀.card)⁻¹ := inv_pos.mpr hμcpos
  have hcardw : (A₀.card : ℝ)⁻¹ ≤ (μ * A₀.card)⁻¹ :=
    (inv_le_inv₀ hcardpos hμcpos).mpr hμcard
  -- The coefficient polytope `S ∩ T`.
  let w : ℝ := (μ * (A₀.card : ℝ))⁻¹
  let S : Set (↥A₀ → ℝ) := Set.univ.pi fun _ ↦ Set.Icc 0 w
  let T : Set (↥A₀ → ℝ) := {c | ∑ x : ↥A₀, c x = 1}
  have hScomp : IsCompact S := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hTclosed : IsClosed T :=
    isClosed_singleton.preimage
      (continuous_finsetSum _ fun i _ ↦ continuous_apply i)
  have hCcomp : IsCompact (S ∩ T) := hScomp.inter_right hTclosed
  have hSconv : Convex ℝ S := convex_pi fun i _ ↦ convex_Icc 0 w
  have hTconv : Convex ℝ T := by
    intro c₁ hc₁ c₂ hc₂ α β hα hβ hαβ
    have hc₁' : (∑ x : ↥A₀, c₁ x) = 1 := hc₁
    have hc₂' : (∑ x : ↥A₀, c₂ x) = 1 := hc₂
    show (∑ x : ↥A₀, (α • c₁ + β • c₂) x) = 1
    have e : (∑ x : ↥A₀, (α • c₁ + β • c₂) x)
        = α * (∑ x : ↥A₀, c₁ x) + β * (∑ x : ↥A₀, c₂ x) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [e, hc₁', hc₂', mul_one, mul_one]
    exact hαβ
  have hCconv : Convex ℝ (S ∩ T) := hSconv.inter hTconv
  -- The linear map `F c = ∑ c x • (x - a)` and `K = F '' (S ∩ T)`.
  let F : (↥A₀ → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    ∑ x : ↥A₀, (LinearMap.proj x).smulRight ((x : Fin d → ℝ) - a)
  have hFapply : ∀ c : ↥A₀ → ℝ,
      F c = ∑ x : ↥A₀, c x • ((x : Fin d → ℝ) - a) := by
    intro c
    show (∑ x : ↥A₀, (LinearMap.proj x).smulRight ((x : Fin d → ℝ) - a)) c = _
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  let K : Set (Fin d → ℝ) := F '' (S ∩ T)
  have hKcomp : IsCompact K := hCcomp.image F.continuous_of_finiteDimensional
  have hKconv : Convex ℝ K := hCconv.linear_image F
  -- `S ∩ T` is nonempty: the constant weight `1 / |A₀|` is feasible.
  have hc₀mem : (fun _ : ↥A₀ ↦ (A₀.card : ℝ)⁻¹) ∈ S ∩ T := by
    refine ⟨?_, ?_⟩
    · apply Set.mem_univ_pi.mpr
      exact fun i ↦ ⟨inv_nonneg.mpr hcardpos.le, hcardw⟩
    · show (∑ x : ↥A₀, (A₀.card : ℝ)⁻¹) = 1
      have hne : (A₀.card : ℝ) ≠ 0 := ne_of_gt hcardpos
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
        mul_inv_cancel₀ hne]
  have hKne : K.Nonempty := ⟨_, Set.mem_image_of_mem F hc₀mem⟩
  -- Main claim: `0 ∈ K`.
  have h0K : (0 : Fin d → ℝ) ∈ K := by
    by_contra h0
    obtain ⟨u, hu⟩ := exists_forall_sum_lt_zero hKcomp hKne hKconv h0
    let B : Finset (Fin d → ℝ) :=
      A₀.filter fun x ↦ (∑ i, u i * a i) ≤ ∑ i, u i * x i
    have hBm : μ * (A₀.card : ℝ) < (B.card : ℝ) := H u _ le_rfl
    have hmpos : (0 : ℝ) < B.card := lt_trans hμcpos hBm
    have hmne : (B.card : ℝ) ≠ 0 := ne_of_gt hmpos
    let c : ↥A₀ → ℝ :=
      fun x ↦ if (x : Fin d → ℝ) ∈ B then (B.card : ℝ)⁻¹ else 0
    -- The equal-weight coefficient is feasible.
    have hcC : c ∈ S ∩ T := by
      refine ⟨?_, ?_⟩
      · apply Set.mem_univ_pi.mpr
        intro i
        by_cases hi : (i : Fin d → ℝ) ∈ B
        · have hci : c i = (B.card : ℝ)⁻¹ := ite_eq_left hi
          refine ⟨?_, ?_⟩
          · rw [hci]
            exact inv_nonneg.mpr hmpos.le
          · rw [hci]
            exact (inv_le_inv₀ hmpos hμcpos).mpr hBm.le
        · have hci : c i = 0 := ite_eq_right hi
          refine ⟨?_, ?_⟩
          · rw [hci]
          · rw [hci]
            exact hwpos.le
      · show (∑ x : ↥A₀, c x) = 1
        have hAB : A₀.filter (· ∈ B) = B := by
          ext x
          rw [Finset.mem_filter]
          exact ⟨And.right, fun hx ↦ ⟨Finset.filter_subset _ _ hx, hx⟩⟩
        have e : (∑ x : ↥A₀, c x)
            = ∑ x ∈ A₀, (if x ∈ B then (B.card : ℝ)⁻¹ else 0) :=
          (Finset.sum_congr rfl fun x _ ↦ rfl).trans
            (Finset.sum_coe_sort A₀
              (fun x ↦ if x ∈ B then (B.card : ℝ)⁻¹ else 0))
        rw [e, ← Finset.sum_filter, hAB, Finset.sum_const, nsmul_eq_mul]
        exact mul_inv_cancel₀ hmne
    -- But then `F c ∈ K` has `∑ i, u i * (F c) i ≥ 0`, contradicting separation.
    have hFmem : F c ∈ K := Set.mem_image_of_mem F hcC
    have hult : (∑ i, u i * (F c) i) < 0 := hu _ hFmem
    have hdF : (∑ i, u i * (F c) i)
        = ∑ x : ↥A₀, c x * (∑ i, u i * ((x : Fin d → ℝ) i - a i)) := by
      rw [hFapply]
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hdF] at hult
    have hnn : 0 ≤ ∑ x : ↥A₀, c x * (∑ i, u i * ((x : Fin d → ℝ) i - a i)) := by
      apply Finset.sum_nonneg
      intro x _
      by_cases hxB : (x : Fin d → ℝ) ∈ B
      · have hcx : c x = (B.card : ℝ)⁻¹ := ite_eq_left hxB
        have h2 : 0 ≤ ∑ i, u i * ((x : Fin d → ℝ) i - a i) := by
          have hle : (∑ i, u i * a i) ≤ ∑ i, u i * (x : Fin d → ℝ) i :=
            (Finset.mem_filter.mp hxB).2
          have hsub : (∑ i, u i * ((x : Fin d → ℝ) i - a i))
              = (∑ i, u i * (x : Fin d → ℝ) i) - (∑ i, u i * a i) := by
            simp only [mul_sub, Finset.sum_sub_distrib]
          rw [hsub]
          linarith
        rw [hcx]
        exact mul_nonneg (inv_nonneg.mpr hmpos.le) h2
      · have hcx : c x = 0 := ite_eq_right hxB
        rw [hcx, zero_mul]
    linarith
  -- Unpack `0 ∈ K` into the required coefficient function.
  obtain ⟨c, hcC, hFc0⟩ := h0K
  refine ⟨c, fun x ↦ ?_, fun x ↦ ?_, ?_, ?_⟩
  · exact (Set.mem_Icc.mp (Set.mem_univ_pi.mp hcC.1 x)).1
  · exact (Set.mem_Icc.mp (Set.mem_univ_pi.mp hcC.1 x)).2
  · exact hcC.2
  · rw [hFapply] at hFc0
    exact hFc0

end

/-- **Pham–Zakharov, eq. (12).** Let `A₀ : Finset (Fin d → ℝ)`, `a : Fin d → ℝ`,
`0 < μ`.  Suppose that for every `u : Fin d → ℝ` and `t : ℝ` with
`t ≤ ∑ i, u i * a i`, the halfspace `{x | t ≤ ∑ i, u i * x i}` contains strictly
more than `μ * |A₀|` points of `A₀`.  Then `a` is a convex combination of the
points of `A₀` with every weight in `[0, (μ * |A₀|)⁻¹]`. -/
theorem exists_balanced_convex_combination {d : ℕ} (A₀ : Finset (Fin d → ℝ))
    (a : Fin d → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (H : ∀ (u : Fin d → ℝ) (t : ℝ), t ≤ ∑ i, u i * a i →
      μ * (A₀.card : ℝ) <
        ((A₀.filter fun x ↦ t ≤ ∑ i, u i * x i).card : ℝ)) :
    ∃ c : (Fin d → ℝ) → ℝ,
      (∀ x ∈ A₀, 0 ≤ c x) ∧ (∀ x ∈ A₀, c x ≤ (μ * A₀.card)⁻¹) ∧
      (∑ x ∈ A₀, c x = 1) ∧ (∑ x ∈ A₀, c x • (x - a) = 0) := by
  classical
  obtain ⟨c₀, h0, hcap, hsum, hzero⟩ := exists_balanced_combination_aux hμ H
  refine ⟨fun x ↦ if h : x ∈ A₀ then c₀ ⟨x, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have e : (fun x ↦ if h : x ∈ A₀ then c₀ ⟨x, h⟩ else 0) x = c₀ ⟨x, hx⟩ :=
      dite_eq_left hx
    rw [e]
    exact h0 ⟨x, hx⟩
  · intro x hx
    have e : (fun x ↦ if h : x ∈ A₀ then c₀ ⟨x, h⟩ else 0) x = c₀ ⟨x, hx⟩ :=
      dite_eq_left hx
    rw [e]
    exact hcap ⟨x, hx⟩
  · have e : (∑ x ∈ A₀, (if h : x ∈ A₀ then c₀ ⟨x, h⟩ else 0))
        = ∑ x : ↥A₀, c₀ x :=
      (Finset.sum_coe_sort A₀
        (fun x ↦ if h : x ∈ A₀ then c₀ ⟨x, h⟩ else 0)).symm.trans
        (Finset.sum_congr rfl fun x _ ↦ by rw [dite_eq_left x.2])
    rw [e, hsum]
  · have e : (∑ x ∈ A₀, (if h : x ∈ A₀ then c₀ ⟨x, h⟩ else 0) • (x - a))
        = ∑ x : ↥A₀, c₀ x • ((x : Fin d → ℝ) - a) :=
      (Finset.sum_coe_sort A₀
        (fun x ↦ (if h : x ∈ A₀ then c₀ ⟨x, h⟩ else 0) • (x - a))).symm.trans
        (Finset.sum_congr rfl fun x _ ↦ by rw [dite_eq_left x.2])
    rw [e, hzero]
