import Nonaveraging.Structure
import Nonaveraging.Asymptotics

/-!
# The upper bound: `h(n) ≤ n^{1/4+o(1)}`

Paper references (arXiv:2410.14624v2, §4):

* **Theorem 2** (`nonaveraging_box_bound`) — a non-averaging subset of a box
  `B ⊆ ℤ^d` satisfies `|A| ≤ |B|^{α_d + o(1)}` where `α_d = (d−1)/(d+1)` for
  `d ≥ 2` and `α₁ = 1/4`.  Proved by the density-increment iteration:
  `irreduciblization` (Lemma 10) + `embedded_in_mu_convex_position`
  (Theorem 4) + `density_increment` (Lemma 1).
* `log_h_div_log_upper` — the `d = 1` case transported to `[n] ⊆ ℤ`.
-/

open Finset MeasureTheory Filter

namespace Nonaveraging

/-- The exponent `α_d` of Theorem 2: `(d−1)/(d+1)` for `d ≥ 2`, `1/4` for
`d = 1`. -/
noncomputable def alphaExp (d : ℕ) : ℝ :=
  if d = 1 then 1 / 4 else ((d : ℝ) - 1) / (d + 1)

/-- **Theorem 2.** For `d ≥ 1` and `ζ > 0`, no non-averaging
`A ⊆ B ⊆ ℤ^d` satisfies `|A| > |B|^{α_d + ζ}` once `|A|` is large enough. -/
theorem nonaveraging_box_bound (d : ℕ) (hd : 1 ≤ d) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ M : ℕ, ∀ (A : Finset (Fin d → ℤ)) (B : GAP.Box d),
      NonAveraging A → A ⊆ B.toFinset → M ≤ A.card →
      (A.card : ℝ) ≤ (B.card : ℝ) ^ (alphaExp d + ζ) := by
  sorry

/-- The `d = 1` consequence: `h n ≤ n^{1/4 + o(1)}` in logarithmic form. -/
theorem log_h_div_log_upper : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop, Real.log (h n) / Real.log n ≤ (1 / 4 : ℝ) + ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := nonaveraging_box_bound 1 le_rfl (half_pos hε)
  have hMev : ∀ᶠ n : ℕ in atTop, M ≤ h n := by
    filter_upwards [tendsto_sqrt_sqrt_atTop.eventually_ge_atTop (M + 1)]
      with n hn
    exact le_trans (Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn))
      (h_ge_sqrt_sqrt_sub_one n)
  filter_upwards [hMev, eventually_ge_atTop 2] with n hMn hn2
  classical
  obtain ⟨A, hAsub, hANA, hAcard⟩ := exists_nonAveraging_card_eq n
  let e : ℤ →+ (Fin 1 → ℤ) :=
    { toFun := fun x _ ↦ x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have he_inj : Function.Injective e := fun _ _ h ↦ congrFun h 0
  set A' := A.image e with hA'def
  have hANA' : NonAveraging A' := hANA.image e he_inj
  have hcard' : A'.card = h n := by
    rw [hA'def, Finset.card_image_of_injective _ he_inj, hAcard]
  let B : GAP.Box 1 := fun _ ↦ Finset.Icc 1 (n : ℤ)
  have hAsub' : A' ⊆ B.toFinset := by
    intro x hx
    rw [hA'def, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [GAP.Box.toFinset, Fintype.mem_piFinset]
    intro i
    exact hAsub hy
  have hBcard : B.card = n := by
    have h1 : B.card = (Finset.Icc 1 (n : ℤ)).card := Fin.prod_univ_one _
    rw [h1, Int.card_Icc]
    simp
  have hbox := hM A' B hANA' hAsub' (by rw [hcard']; exact hMn)
  rw [hcard', hBcard] at hbox
  have hα : alphaExp 1 = 1 / 4 := by unfold alphaExp; norm_num
  rw [hα] at hbox
  have hpos : (0 : ℝ) < (h n : ℝ) := by
    have hs : ({(1 : ℤ)} : Finset ℤ) ⊆ Finset.Icc 1 (n : ℤ) := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_Icc.mpr ⟨le_refl 1,
        by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hn2⟩
    have hc := card_le_h hs (nonAveraging_singleton (1 : ℤ))
    rw [Finset.card_singleton] at hc
    exact_mod_cast hc
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
  have hln : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast hn2 : (1 : ℝ) < n)
  have hlog : Real.log (h n) ≤ (1 / 4 + ε / 2) * Real.log n := by
    have h1 := (Real.log_le_log_iff hpos
      (Real.rpow_pos_of_pos hn0 _)).mpr hbox
    rwa [Real.log_rpow hn0] at h1
  calc Real.log (h n) / Real.log n ≤ 1 / 4 + ε / 2 :=
        (div_le_iff₀ hln).mpr hlog
    _ ≤ 1 / 4 + ε := by linarith

end Nonaveraging
