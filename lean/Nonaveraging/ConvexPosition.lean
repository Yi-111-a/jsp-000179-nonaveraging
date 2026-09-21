import Nonaveraging.ConvexBody
import Nonaveraging.GAP

/-!
# Sets in δ-convex position and the density-increment lemma

Paper references (arXiv:2410.14624v2, §2):

* `InDeltaConvexPosition` — `A ⊂ ℝ^d` is in δ-convex position if every point
  of `A` lies in a half-space containing at most `δ|A|` points of `A`.
* **Lemma 1** (`density_increment`) — given `A ⊂ Ω` in δ-convex position,
  some smaller convex `Ω' ⊂ Ω` has a substantially denser intersection:
  `Vol(Ω') ≤ η·Vol(Ω)` and `|A ∩ Ω'| ≥ η^{(d−1)/(d+1)+ε}|A|` for some
  `η ∈ [δ, δ^τ]`.
* **Lemma 2** (`convex_linear_approx`) — a bounded convex function on a box in
  `ℝ^{d−1}` is well-approximated by a linear function on one of many
  prescribed sub-cubes.
-/

open Finset MeasureTheory

attribute [local instance] Classical.propDecidable

namespace Nonaveraging

variable {d : ℕ}

/-- The standard dot product on `Fin d → ℝ`. -/
def dot (u x : Fin d → ℝ) : ℝ := ∑ i, u i * x i

/-- `A ⊂ ℝ^d` is in *δ-convex position* if for every `a ∈ A` some half-space
containing `a` contains at most `δ|A|` points of `A`. -/
def InDeltaConvexPosition (A : Finset (Fin d → ℝ)) (δ : ℝ) : Prop :=
  ∀ a ∈ A, ∃ u : Fin d → ℝ, ∃ t : ℝ,
    t ≤ dot u a ∧
    ((A.filter fun x ↦ t ≤ dot u x).card : ℝ) ≤ δ * A.card

/-- The open box `(−c, 1+c)^k` in `ℝ^k`. -/
def openBox {k : ℕ} (c : ℝ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun _ ↦ Set.Ioo (-c) (1 + c)

/-- The sub-cube `v/m + [0,1/m]^k` for `v : Fin k → ℕ`. -/
def cubeOf {k : ℕ} (m : ℕ) (v : Fin k → ℕ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun i ↦ Set.Icc ((v i : ℝ) / m) (((v i : ℝ) + 1) / m)

private lemma mem_openBox {k : ℕ} {c : ℝ} {x : Fin k → ℝ} :
    x ∈ openBox c ↔ ∀ i, x i ∈ Set.Ioo (-c) (1 + c) := by
  rw [openBox, Set.mem_univ_pi]

private lemma mem_cubeOf {k : ℕ} {m : ℕ} {v : Fin k → ℕ} {x : Fin k → ℝ} :
    x ∈ cubeOf m v ↔ ∀ i, x i ∈ Set.Icc ((v i : ℝ) / m) (((v i : ℝ) + 1) / m) := by
  rw [cubeOf, Set.mem_univ_pi]

private lemma update_mem_openBox {k : ℕ} {c : ℝ} {P : Fin k → ℝ} (hP : P ∈ openBox c)
    (i : Fin k) {t : ℝ} (ht : t ∈ Set.Ioo (-c) (1 + c)) :
    Function.update P i t ∈ openBox c := by
  rw [mem_openBox] at hP ⊢
  intro j
  by_cases hji : j = i
  · simpa [hji] using ht
  · rw [Function.update_of_ne hji]
    exact hP j

private lemma cubeOf_subset_openBox {k : ℕ} {m : ℕ} {c : ℝ} (hc : 0 < c)
    {v : Fin k → ℕ} (hv : ∀ i, v i < m) : cubeOf m v ⊆ openBox c := by
  intro x hx
  rw [mem_cubeOf] at hx
  rw [mem_openBox]
  intro i
  have hm0 : (0 : ℝ) < m := by
    have h : (0 : ℕ) < m := Nat.lt_of_le_of_lt (Nat.zero_le _) (hv i)
    exact_mod_cast h
  have h1 : 0 ≤ (v i : ℝ) / m := by positivity
  have h2 : ((v i : ℝ) + 1) / m ≤ 1 := by
    rw [div_le_one hm0]
    have : v i + 1 ≤ m := hv i
    exact_mod_cast this
  exact ⟨lt_of_lt_of_le (by linarith) (hx i).1, lt_of_le_of_lt (hx i).2 (by linarith)⟩

/-- Restriction of a convex function on a box to a coordinate line. -/
private lemma convexOn_update_line {k : ℕ} {c : ℝ} {H : (Fin k → ℝ) → ℝ}
    (hconv : ConvexOn ℝ (openBox c) H) {P : Fin k → ℝ} (hP : P ∈ openBox c)
    (i : Fin k) :
    ConvexOn ℝ (Set.Ioo (-c) (1 + c)) (fun t ↦ H (Function.update P i t)) := by
  refine ⟨convex_Ioo _ _, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hupd : Function.update P i (a • x + b • y)
      = a • Function.update P i x + b • Function.update P i y := by
    funext j
    by_cases hji : j = i
    · subst hji; simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    · simp only [Function.update_of_ne hji, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
  show H (Function.update P i (a • x + b • y))
      ≤ a • H (Function.update P i x) + b • H (Function.update P i y)
  rw [hupd]
  exact hconv.2 (update_mem_openBox hP i hx) (update_mem_openBox hP i hy) ha hb hab

/-- Monotonicity of the `h`-step secant slope of a convex function. -/
private lemma unit_slope_mono {φ : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s φ)
    {h : ℝ} (hh : 0 < h) {x y : ℝ} (hx : x ∈ s) (hyh : y + h ∈ s) (hxy : x ≤ y) :
    (φ (x + h) - φ x) / h ≤ (φ (y + h) - φ y) / h := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · exact le_rfl
  · have h1 : (φ (x + h) - φ x) / ((x + h) - x) ≤ (φ (y + h) - φ x) / ((y + h) - x) :=
      hf.secant_mono_aux2 hx hyh (by linarith) (by linarith)
    have h2 : (φ (y + h) - φ x) / ((y + h) - x) ≤ (φ (y + h) - φ y) / ((y + h) - y) :=
      hf.secant_mono_aux3 hx hyh hxy (by linarith)
    have e1 : (x + h) - x = h := by ring
    have e2 : (y + h) - y = h := by ring
    rw [e1] at h1; rw [e2] at h2
    exact le_trans h1 h2

/-- The base point `v/m` of a cube, as a real vector. -/
private noncomputable def basePt {k : ℕ} (m : ℕ) (v : Fin k → ℕ) : Fin k → ℝ :=
  fun j ↦ (v j : ℝ) / m

/-- The unit secant slope of `H` along the `i`-th coordinate line through `P`,
i.e. `m · (H(P + (t+1/m)eᵢ) − H(P + t eᵢ))`. -/
private noncomputable def uslope {k : ℕ} (H : (Fin k → ℝ) → ℝ) (m : ℕ) (P : Fin k → ℝ)
    (i : Fin k) (t : ℝ) : ℝ :=
  (H (Function.update P i (t + 1 / m)) - H (Function.update P i t)) / (1 / m)

/-- The open box `(−c, 1+c)^k` is open. -/
private lemma isOpen_openBox {k : ℕ} (c : ℝ) : IsOpen (openBox (k := k) c) :=
  isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo

/-- The base point `v/m` lies in the open box. -/
private lemma basePt_mem_openBox {k m : ℕ} {c : ℝ} (hc : 0 < c) {v : Fin k → ℕ}
    (hv : ∀ i, v i < m) : basePt m v ∈ openBox c := by
  rw [mem_openBox]
  intro i
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) (hv i)
  have h1 : (0 : ℝ) ≤ (v i : ℝ) / m := by positivity
  have h2 : (v i : ℝ) / m < 1 := by
    rw [div_lt_one hm0]
    exact_mod_cast hv i
  show (v i : ℝ) / m ∈ Set.Ioo (-c) (1 + c)
  constructor <;> linarith

/-- **Subgradient existence** for a bounded convex function on a box:
at every point `P` of the box there is a vector `u` with
`H x ≥ H P + u · (x − P)` on the whole box. -/
private lemma exists_subgradient {k : ℕ} {c : ℝ} (_hc : 0 < c)
    {H : (Fin k → ℝ) → ℝ} (hconv : ConvexOn ℝ (openBox c) H)
    (hbdd : ∀ x ∈ openBox c, H x ∈ Set.Icc 0 1)
    {P : Fin k → ℝ} (hP : P ∈ openBox c) :
    ∃ u : Fin k → ℝ, ∀ x ∈ openBox c, H P + dot u (x - P) ≤ H x := by
  classical
  set epi : Set ((Fin k → ℝ) × ℝ) := {p | p.1 ∈ openBox c ∧ H p.1 ≤ p.2}
  have hepi : Convex ℝ epi := hconv.convex_epigraph
  have hopen : IsOpen (openBox (k := k) c) := isOpen_openBox c
  have hint : (interior epi).Nonempty := by
    have hW : openBox c ×ˢ Set.Ioi (1 : ℝ) ⊆ epi := fun p hp ↦
      ⟨hp.1, (hbdd p.1 hp.1).2.trans (le_of_lt hp.2)⟩
    have hWopen : IsOpen (openBox c ×ˢ Set.Ioi (1 : ℝ)) := hopen.prod isOpen_Ioi
    refine ⟨(P, 2), interior_mono hW ?_⟩
    rw [hWopen.interior_eq]
    exact ⟨hP, by norm_num⟩
  have hnot : (P, H P) ∉ interior epi := by
    intro hmem
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hmem
    have hdist : dist (P, H P - ε / 2) (P, H P) < ε := by
      rw [Prod.dist_eq]
      simp only [dist_self, dist_eq_norm]
      rw [Real.norm_eq_abs]
      have habs : |H P - ε / 2 - H P| = ε / 2 := by
        have : H P - ε / 2 - H P = -(ε / 2) := by ring
        rw [this, abs_neg, abs_of_pos (half_pos hε)]
      rw [habs]
      exact max_lt (by linarith) (by linarith)
    have hmem' : (P, H P - ε / 2) ∈ epi :=
      interior_subset (hball (Metric.mem_ball.mpr hdist))
    have := hmem'.2
    linarith
  obtain ⟨f, hfne, hfle⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hepi hnot hint
  -- decompose `f` as `f (x, t) = g x + α * t`
  set g : (Fin k → ℝ) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Fin k → ℝ) ℝ)
    with hg
  set α := f ((0 : Fin k → ℝ), 1) with hαdef
  have hgapply : ∀ x : Fin k → ℝ, g x = f (x, 0) := fun x ↦ by
    rw [hg]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have hdecomp : ∀ (x : Fin k → ℝ) (t : ℝ), f (x, t) = g x + α * t := by
    intro x t
    rw [hgapply]
    have h1 : (x, t) = (x, (0 : ℝ)) + t • ((0 : Fin k → ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [h1]
    rw [map_add, map_smul, smul_eq_mul, mul_comm]
  have key : ∀ x ∈ openBox c, ∀ t : ℝ, H x ≤ t → g x + α * t ≤ g P + α * H P := by
    intro x hx t ht
    have := hfle (x, t) (show (x, t) ∈ epi from ⟨hx, ht⟩)
    rwa [hdecomp, hdecomp] at this
  have hα0 : α ≤ 0 := by
    by_contra hα'
    push Not at hα'
    have := key P hP (H P + 1) (by linarith)
    nlinarith
  have hα : α < 0 := by
    rcases eq_or_lt_of_le hα0 with h | h
    · exfalso
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen P hP
      have hg0 : ∀ w : Fin k → ℝ, g w = 0 := by
        intro w
        by_cases hw : w = 0
        · simp [hw]
        · set t := ε / (2 * ‖w‖ + 1) with htdef
          have ht : 0 < t := by positivity
          have htnorm : ‖t • w‖ < ε := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
            have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
            have h1 : t * ‖w‖ = ε * (‖w‖ / (2 * ‖w‖ + 1)) := by
              rw [htdef]; field_simp
            rw [h1]
            have h2 : ‖w‖ / (2 * ‖w‖ + 1) < 1 := by
              rw [div_lt_one (by positivity)]; linarith
            calc ε * (‖w‖ / (2 * ‖w‖ + 1)) < ε * 1 := by gcongr
              _ = ε := mul_one _
          have hmem1 : P + t • w ∈ openBox c := hball (by
            rw [Metric.mem_ball, dist_eq_norm]
            simpa using htnorm)
          have hmem2 : P - t • w ∈ openBox c := hball (by
            rw [Metric.mem_ball, dist_eq_norm]
            simpa using htnorm)
          have h1 := key _ hmem1 (H _) le_rfl
          have h2 := key _ hmem2 (H _) le_rfl
          simp only [h, zero_mul, add_zero] at h1 h2
          -- g (P + t•w) ≤ g P and g (P − t•w) ≤ g P
          rw [map_add, map_smul, smul_eq_mul] at h1
          have hsub : g (P - t • w) = g P - t * g w := by
            rw [map_sub, map_smul, smul_eq_mul]
          have hg1 : g w ≤ 0 := by
            rcases (mul_nonpos_iff.mp (show t * g w ≤ 0 by linarith)) with ⟨-, h'⟩ | ⟨h', -⟩
            · exact h'
            · linarith
          have hg2 : 0 ≤ g w := by
            rcases (mul_nonneg_iff.mp (show 0 ≤ t * g w by linarith [h2, hsub]))
              with ⟨-, h'⟩ | ⟨h', -⟩
            · exact h'
            · linarith
          linarith
      apply hfne
      refine ContinuousLinearMap.ext fun p ↦ ?_
      obtain ⟨x, t⟩ := p
      simp [hdecomp x t, hg0 x, h]
    · exact h
  -- `u i = g eᵢ / (−α)` is a subgradient
  refine ⟨fun i ↦ g (Pi.single i 1) / (-α), fun x hx ↦ ?_⟩
  have hx' := key x hx (H x) le_rfl
  have hgx : g (x - P) = ∑ i : Fin k, (x i - P i) * g (Pi.single i 1) := by
    conv_lhs => rw [show x - P = ∑ i : Fin k, Pi.single i (x i - P i) from
      (Finset.univ_sum_single _).symm]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hs : Pi.single i (x i - P i) = (x i - P i) • Pi.single i (1 : ℝ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hs, map_smul, smul_eq_mul]
  have hdot : dot (fun i ↦ g (Pi.single i 1) / (-α)) (x - P) = g (x - P) / (-α) := by
    unfold dot
    simp only [Pi.sub_apply]
    rw [hgx, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot]
  -- α·(Hx − HP) ≤ −g(x−P), hence g(x−P)/(−α) ≤ Hx − HP
  have hgsub : g x - g P = g (x - P) := (map_sub g x P).symm
  have hle : g (x - P) / (-α) ≤ H x - H P := by
    rw [div_le_iff₀ (neg_pos.mpr hα)]
    linarith [hx', hgsub]
  linarith [hle]

/-- **Claim 3 of Lemma 2** (derivative-free version): if the supporting
linearisation `L_v` at the base point of `Q_v` fails by more than `δ` at `y`,
then along some coordinate `i` the `1/m`-unit secant slope jumps by at least
`δ·m/(k+1)` over an interval of length `≤ k/m`. -/
private lemma claim3 {k : ℕ} (m : ℕ) (hm : 0 < m) {c δ : ℝ}
    (hc : 2 * ((k : ℝ) + 1) / m < c) {H : (Fin k → ℝ) → ℝ}
    (hconv : ConvexOn ℝ (openBox c) H)
    {v : Fin k → ℕ} (hv : ∀ i, v i < m)
    {u : Fin k → ℝ}
    (hu : ∀ x ∈ openBox c, H (basePt m v) + dot u (x - basePt m v) ≤ H x)
    (hδ : 0 < δ)
    {y : Fin k → ℝ} (hy : y ∈ cubeOf m v)
    (hfail : H (basePt m v) + dot u (y - basePt m v) + δ < H y) :
    ∃ i : Fin k, ∃ s : ℝ, 0 < s ∧ s ≤ (k : ℝ) / m ∧
      uslope H m (basePt m v) i (basePt m v i + s) ≥
        uslope H m (basePt m v) i (basePt m v i - 1 / m) + δ * m / (k + 1) := by
  classical
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hc' : 0 < c := by
    have hpos : (0 : ℝ) < 2 * (k + 1 : ℝ) / m := by positivity
    linarith
  have hmc : 2 * ((k : ℝ) + 1) < c * m := by
    have h := mul_lt_mul_of_pos_right hc hm'
    rwa [div_mul_cancel₀ _ hm'.ne'] at h
  set P := basePt m v
  have hP : P ∈ openBox c := basePt_mem_openBox hc' hv
  have hPlower : ∀ i : Fin k, -c < P i := fun i ↦ (mem_openBox.mp hP i).1
  have hPupper : ∀ i : Fin k, P i ≤ ((m : ℝ) - 1) / m := fun i ↦ by
    show (v i : ℝ) / m ≤ ((m : ℝ) - 1) / m
    apply div_le_div_of_nonneg_right _ hm'.le
    have hle : v i ≤ m - 1 := by have hlt := hv i; omega
    have hcast : (v i : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hle
    rwa [Nat.cast_sub (Nat.one_le_of_lt hm), Nat.cast_one] at hcast
  -- `a i = y i − P i ∈ [0, 1/m]` and `s = ∑ a i`
  set a : Fin k → ℝ := fun i ↦ y i - P i
  have ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1 / m := fun i ↦ by
    have h := (mem_cubeOf.mp hy) i
    have hPi : P i = (v i : ℝ) / m := rfl
    constructor
    · have : a i = y i - (v i : ℝ) / m := rfl
      linarith [h.1]
    · have h2 : y i - (v i : ℝ) / m ≤ 1 / m := by
        have : ((v i : ℝ) + 1) / m = (v i : ℝ) / m + 1 / m := by ring
        linarith [h.2]
      exact h2
  set s := ∑ i, a i
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ ↦ (ha i).1
  have hsle : s ≤ (k : ℝ) / m := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ (ha i).2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div] at h
    exact h
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le hs0 with h0 | h0
    · exfalso
      have hzero : ∀ i, a i = 0 := fun i ↦
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ (ha i).1).mp h0.symm i (Finset.mem_univ _)
      have hyP : y = P := funext fun i ↦ by
        have := hzero i
        change y i - P i = 0 at this
        linarith
      rw [hyP] at hfail
      have : dot u (P - P) = 0 := by
        unfold dot; simp [Pi.sub_apply]
      linarith [hfail, hδ, this]
    · exact h0
  -- `z i = P + s eᵢ` and `y` is the convex combination `∑ (aᵢ/s) zᵢ`
  set w : Fin k → ℝ := fun i ↦ a i / s
  set z : Fin k → (Fin k → ℝ) := fun i ↦ Function.update P i (P i + s)
  have hwsum : ∑ i, w i = 1 := by
    show ∑ i : Fin k, a i / s = 1
    rw [← Finset.sum_div]
    show s / s = 1
    exact div_self hspos.ne'
  have hw0 : ∀ i, 0 ≤ w i := fun i ↦ div_nonneg (ha i).1 hs0
  have hz_mem : ∀ i : Fin k, z i ∈ openBox c := fun i ↦
    update_mem_openBox hP i ⟨by linarith [hPlower i, hs0], by
      have : P i + s ≤ ((m : ℝ) - 1) / m + (k : ℝ) / m :=
        add_le_add (hPupper i) hsle
      have hk : (k : ℝ) - 1 < c * m := by linarith
      have hlt : ((m : ℝ) - 1) / m + (k : ℝ) / m < 1 + c := by
        rw [← add_div, div_lt_iff₀ hm']
        linarith
      linarith⟩
  have hyeq : y = ∑ i, w i • z i := by
    funext j
    have hzj : ∀ i : Fin k, z i j = P j + (if i = j then s else 0) := fun i ↦ by
      by_cases hij : i = j
      · subst hij; simp [z]
      · have hji : j ≠ i := fun h ↦ hij h.symm
        simp [z, Function.update_of_ne hji, hij]
    have hsum : ∑ i : Fin k, w i * z i j = P j + a j := by
      calc _ = ∑ i, (w i * P j + w i * (if i = j then s else 0)) :=
            Finset.sum_congr rfl fun i _ ↦ by rw [hzj i]; ring
        _ = (∑ i, w i) * P j + ∑ i, w i * (if i = j then s else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
        _ = P j + a j := by
            rw [hwsum, one_mul]
            have hite : ∑ i, w i * (if i = j then s else 0) = w j * s := by
              rw [Finset.sum_congr rfl (fun i _ ↦ by rw [mul_ite, mul_zero])]
              rw [Finset.sum_ite_eq']; simp
            rw [hite]
            have hws : w j * s = a j := by
              change a j / s * s = a j
              exact div_mul_cancel₀ _ hspos.ne'
            linarith [hws]
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    change y j = P j + (y j - P j)
    ring
  -- linearisation evaluated at `z i`
  have hdotz : ∀ i, dot u (z i - P) = s * u i := fun i ↦ by
    have hzsub : z i - P = Pi.single i s := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [z, Pi.single_eq_same]
      · simp only [Pi.sub_apply, z]
        rw [Function.update_of_ne hji, Pi.single_eq_of_ne hji]
        ring
    unfold dot
    rw [hzsub, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]; ring
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · simp
  have hdoty : dot u (y - P) = ∑ i, a i * u i := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    show u i * (y i - P i) = (y i - P i) * u i
    ring
  have hLsum : ∑ i, w i • (H P + s * u i) = H P + dot u (y - P) := by
    rw [hdoty]
    have hterm : ∀ i : Fin k, w i • (H P + s * u i) = w i * H P + a i * u i := fun i ↦ by
      have hws : w i * s = a i := by
        change a i / s * s = a i
        exact div_mul_cancel₀ _ hspos.ne'
      rw [smul_eq_mul, mul_add, ← mul_assoc, hws]
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_add_distrib,
      ← Finset.sum_mul, hwsum, one_mul]
  -- compare Jensen with the failure
  have hJen := hconv.map_sum_le (fun i _ ↦ hw0 i) hwsum (fun i _ ↦ hz_mem i)
  rw [← hyeq] at hJen
  have hsumgt : δ < ∑ i, w i • (H (z i) - (H P + s * u i)) := by
    have hsplit : ∑ i, w i • (H (z i) - (H P + s * u i)) =
        (∑ i, w i • H (z i)) - ∑ i, w i • (H P + s * u i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_sub]
    rw [hsplit, hLsum]
    linarith [hfail]
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
    (f := fun i ↦ δ * w i)
    (g := fun i ↦ w i • (H (z i) - (H P + s * u i))) (by
      rwa [← Finset.mul_sum, hwsum, mul_one])
  have hw_pos : 0 < w i₀ := by
    rcases lt_trichotomy (w i₀) 0 with h | h | h
    · linarith [hw0 i₀]
    · rw [h] at hi₀; simp at hi₀
    · exact h
  have hGi : δ < H (z i₀) - (H P + s * u i₀) := by
    have h' : δ * w i₀ < w i₀ * (H (z i₀) - (H P + s * u i₀)) := by
      rwa [smul_eq_mul] at hi₀
    rw [mul_comm δ] at h'
    exact lt_of_mul_lt_mul_left h' hw_pos.le
  -- one-dimensional convexity along coordinate `i₀`
  set φ := fun t ↦ H (Function.update P i₀ t)
  have hφ : ConvexOn ℝ (Set.Ioo (-c) (1 + c)) φ := convexOn_update_line hconv hP i₀
  have hPIoo : P i₀ ∈ Set.Ioo (-c) (1 + c) := mem_openBox.mp hP i₀
  -- the witness
  refine ⟨i₀, s, hspos, hsle, ?_⟩
  -- `slope[Pᵢ₀, Pᵢ₀+s] > uᵢ₀ + δ/s`
  have hslope : u i₀ + δ / s < (H (z i₀) - φ (P i₀)) / s := by
    have hφP : φ (P i₀) = H P := by
      show H (Function.update P i₀ (P i₀)) = H P
      rw [Function.update_eq_self]
    rw [lt_div_iff₀ hspos]
    have hthis : (u i₀ + δ / s) * s = s * u i₀ + δ := by
      rw [add_mul, div_mul_cancel₀ _ hspos.ne']; ring
    rw [hthis, hφP]
    linarith [hGi]
  -- `uslope(Pᵢ₀ + s) ≥ slope[Pᵢ₀, Pᵢ₀ + s]` by secant monotonicity
  have hzup : P i₀ + s + 1 / m ∈ Set.Ioo (-c) (1 + c) := by
    have hk : (k : ℝ) < c * m := by linarith
    have hub : P i₀ + s + 1 / m ≤ ((m : ℝ) - 1) / m + (k : ℝ) / m + 1 / m := by
      linarith [hPupper i₀, hsle]
    have hlt : ((m : ℝ) - 1) / m + (k : ℝ) / m + 1 / m < 1 + c := by
      rw [← add_div, ← add_div, div_lt_iff₀ hm']
      linarith [hk]
    exact ⟨by linarith [hPIoo.1, hspos, one_div_pos.mpr hm'],
      lt_of_le_of_lt hub hlt⟩
  have hsec := hφ.slope_mono_adjacent (y := P i₀ + s) hPIoo hzup (by linarith)
    (by linarith [one_div_pos.mpr hm'])
  have hden1 : P i₀ + s - P i₀ = s := by ring
  have hden2 : P i₀ + s + 1 / m - (P i₀ + s) = 1 / m := by ring
  rw [hden1, hden2] at hsec
  change (H (z i₀) - φ (P i₀)) / s ≤ uslope H m P i₀ (P i₀ + s) at hsec
  -- `B = uslope(Pᵢ₀ − 1/m) ≤ uᵢ₀` from the subgradient
  have hlow : uslope H m P i₀ (P i₀ - 1 / m) ≤ u i₀ := by
    have hPnn : 0 ≤ P i₀ := by
      change 0 ≤ (v i₀ : ℝ) / m
      positivity
    have hz'mem : Function.update P i₀ (P i₀ - 1 / m) ∈ openBox c :=
      update_mem_openBox hP i₀ ⟨by
        have hone : (1 : ℝ) / m < c := by rw [div_lt_iff₀ hm']; linarith
        linarith, by linarith [hPIoo.2, one_div_pos.mpr hm']⟩
    have hle := hu _ hz'mem
    have hdot' : dot u (Function.update P i₀ (P i₀ - 1 / m) - P) =
        u i₀ * (-((1 : ℝ) / m)) := by
      unfold dot
      rw [Finset.sum_eq_single i₀]
      · simp only [Pi.sub_apply, Function.update_self]
        ring
      · intro j _ hj
        simp only [Pi.sub_apply]
        rw [Function.update_of_ne hj, sub_self, mul_zero]
      · simp
    unfold uslope
    have hsimp : P i₀ - 1 / m + 1 / m = P i₀ := by ring
    rw [hsimp, Function.update_eq_self]
    rw [div_le_iff₀ (one_div_pos.mpr hm')]
    have hneg : u i₀ * (1 / m) = -(u i₀ * -(1 / m)) := by ring
    linarith [hle, hdot', hneg]
  have hdelta : δ * m / (k + 1) ≤ δ / s := by
    have hkpos : (0 : ℝ) < k := by
      have : 0 < k := Nat.pos_of_ne_zero fun h ↦ by subst h; exact i₀.elim0
      exact_mod_cast this
    have h1 : δ / ((k : ℝ) / m) ≤ δ / s :=
      div_le_div_of_nonneg_left hδ.le hspos hsle
    have h2 : δ / ((k : ℝ) / m) = δ * m / k := by
      have hkn : (k : ℝ) ≠ 0 := hkpos.ne'
      have hmn : (m : ℝ) ≠ 0 := hm'.ne'
      field_simp
    have h3 : δ * m / (k + 1) ≤ δ * m / k :=
      div_le_div_of_nonneg_left (mul_nonneg hδ.le hm'.le) hkpos (by linarith)
    linarith
  exact le_trans (add_le_add_left hlow (δ * m / (k + 1)))
    (by linarith [hslope, hsec, hdelta])

/-- Pigeonhole: for `f : s → t` with `t` nonempty, some fiber has cardinality
at least `|s| / |t|`. -/
private lemma exists_fiber_card_ge {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : Finset β} {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Nonempty) :
    ∃ b ∈ t, s.card ≤ t.card * (s.filter (fun a ↦ f a = b)).card := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · obtain ⟨b, hb⟩ := ht
    exact ⟨b, hb, by simp⟩
  by_contra h
  push Not at h
  have hle : ∀ b ∈ t, (s.filter (fun a ↦ f a = b)).card ≤ (s.card - 1) / t.card := by
    intro b hb
    have hltb := h b hb
    rw [Nat.le_div_iff_mul_le (Finset.card_pos.mpr ht), mul_comm]
    omega
  have hsum := Finset.card_eq_sum_card_fiberwise (s := s) (t := t) (f := f)
    (fun a ha ↦ hf a ha)
  have hsumle : ∑ b ∈ t, (s.filter (fun a ↦ f a = b)).card ≤
      t.card * ((s.card - 1) / t.card) :=
    calc ∑ b ∈ t, (s.filter (fun a ↦ f a = b)).card
        ≤ ∑ _b ∈ t, (s.card - 1) / t.card := Finset.sum_le_sum hle
      _ = t.card * ((s.card - 1) / t.card) := by
          simp [Finset.sum_const]
  rw [← hsum] at hsumle
  have h2 : s.card ≤ s.card - 1 := le_trans hsumle (Nat.mul_div_le _ _)
  have h3 : s.card - 1 < s.card := by
    have := Finset.card_pos.mpr hs
    omega
  exact (lt_irrefl _) (lt_of_le_of_lt h2 h3)

/-- A secant slope of a `[0,1]`-valued convex function on `(−c,1+c)`, taken over
an interval `[t, t+h]` bounded away from the endpoints, has absolute value
at most `4/c`. -/
private lemma abs_secant_le {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Ioo (-c) (1 + c)) φ)
    (hbdd : ∀ x ∈ Set.Ioo (-c) (1 + c), φ x ∈ Set.Icc 0 1)
    {t h : ℝ} (hh : 0 < h) (ht : -c / 2 ≤ t) (hb : t + h ≤ 1 + c / 2) :
    |(φ (t + h) - φ t) / h| ≤ 4 / c := by
  have htI : t ∈ Set.Ioo (-c) (1 + c) := ⟨by linarith, by linarith⟩
  have hthI : t + h ∈ Set.Ioo (-c) (1 + c) := ⟨by linarith, by linarith⟩
  have e1 : t + h - t = h := by ring
  rw [abs_le]
  constructor
  · -- lower bound via the left endpoint `a' = (t − c)/2`
    set a' := (t - c) / 2 with ha'def
    have ha'I : a' ∈ Set.Ioo (-c) (1 + c) :=
      ⟨by show -c < (t - c) / 2; linarith, by show (t - c) / 2 < 1 + c; linarith⟩
    have h2 := hf.slope_mono_adjacent (y := t) ha'I hthI
      (by show (t - c) / 2 < t; linarith) (by linarith)
    rw [e1] at h2
    have hnum : -1 ≤ φ t - φ a' := by
      have h1 := hbdd _ htI; have h2' := hbdd _ ha'I
      linarith [h1.1, h2'.2]
    have hden : (0 : ℝ) < t - a' := by show (0 : ℝ) < t - (t - c) / 2; linarith
    have hden4 : c / 4 ≤ t - a' := by show c / 4 ≤ t - (t - c) / 2; linarith
    have step1 : -1 / (t - a') ≤ (φ t - φ a') / (t - a') :=
      div_le_div_of_nonneg_right hnum hden.le
    have step2 : -(4 / c) ≤ -1 / (t - a') := by
      have h11 : (1 : ℝ) / (t - a') ≤ 1 / (c / 4) :=
        div_le_div_of_nonneg_left zero_le_one (by linarith) hden4
      have h41 : (4 : ℝ) / c = 1 / (c / 4) := by rw [one_div_div]
      rw [neg_div]
      exact neg_le_neg (h11.trans (le_of_eq h41.symm))
    exact le_trans step2 (le_trans step1 h2)
  · -- upper bound via the right endpoint `b' = (t + h + 1 + c)/2`
    set b' := (t + h + (1 + c)) / 2 with hb'def
    have hb'I : b' ∈ Set.Ioo (-c) (1 + c) :=
      ⟨by show -c < (t + h + (1 + c)) / 2; linarith,
        by show (t + h + (1 + c)) / 2 < 1 + c; linarith⟩
    have h1 := hf.slope_mono_adjacent (y := t + h) htI hb'I (by linarith)
      (by show t + h < (t + h + (1 + c)) / 2; linarith)
    rw [e1] at h1
    have hnum : φ b' - φ (t + h) ≤ 1 := by
      have h1' := hbdd _ hb'I; have h2' := hbdd _ hthI
      linarith [h1'.2, h2'.1]
    have hden : (0 : ℝ) < b' - (t + h) := by
      show (0 : ℝ) < (t + h + (1 + c)) / 2 - (t + h); linarith
    have hden4 : c / 4 ≤ b' - (t + h) := by
      show c / 4 ≤ (t + h + (1 + c)) / 2 - (t + h); linarith
    have step1 : (φ b' - φ (t + h)) / (b' - (t + h)) ≤ 1 / (b' - (t + h)) :=
      div_le_div_of_nonneg_right hnum hden.le
    have step2 : 1 / (b' - (t + h)) ≤ 4 / c := by
      have h41 : (4 : ℝ) / c = 1 / (c / 4) := by rw [one_div_div]
      rw [h41]
      exact div_le_div_of_nonneg_left zero_le_one (by linarith) hden4
    linarith [h1, step1, step2]

/-- If `g` is injective on `S₀`, the "slope" `Φ` is nondecreasing from `hi x`
to `lo y` whenever `g x < g y`, and each `x` contributes a jump, then the total
of the jumps telescopes. -/
private lemma sum_jumps_le {β : Type*} [DecidableEq β] {Φ : ℝ → ℝ} {g : β → ℕ}
    {lo hi : β → ℝ} {S₀ : Finset β}
    (hinj : ∀ x ∈ S₀, ∀ y ∈ S₀, g x = g y → x = y)
    (hmono : ∀ x ∈ S₀, ∀ y ∈ S₀, g x < g y → Φ (hi x) ≤ Φ (lo y)) :
    ∀ S ⊆ S₀, S.Nonempty → ∃ a ∈ S, ∃ b ∈ S,
      ∑ x ∈ S, (Φ (hi x) - Φ (lo x)) ≤ Φ (hi b) - Φ (lo a) := by
  intro S
  induction S using Finset.induction_on_max_value g with
  | empty => intro _ hne; exact absurd hne Finset.not_nonempty_empty
  | insert a S' ha hmax ih =>
    intro hS _
    rcases S'.eq_empty_or_nonempty with hE | hNE
    · subst hE
      refine ⟨a, by simp, a, by simp, ?_⟩
      simp
    · have hS' : S' ⊆ S₀ := fun x hx ↦ hS (Finset.mem_insert_of_mem hx)
      obtain ⟨a', ha', b', hb', hsum'⟩ := ih hS' hNE
      have haS₀ : a ∈ S₀ := hS (Finset.mem_insert_self _ _)
      have hlt : g b' < g a := by
        have hle := hmax b' hb'
        rcases eq_or_lt_of_le hle with h | h
        · exfalso
          have hab : a = b' := hinj a haS₀ b' (hS' hb') h.symm
          rw [← hab] at hb'
          exact ha hb'
        · exact h
      have hle1 : Φ (hi b') ≤ Φ (lo a) := hmono b' (hS' hb') a haS₀ hlt
      refine ⟨a', Finset.mem_insert_of_mem ha', a, Finset.mem_insert_self _ _, ?_⟩
      rw [Finset.sum_insert ha]
      linarith [hsum', hle1]

set_option maxHeartbeats 1600000 in
/-- **Lemma 2**: a convex `H : (−c, 1+c)^{d−1} → [0,1]` has, for any
`I ⊆ [m]^{d−1}`, a cube `Q_v` with `v ∈ I` on which `H` is approximated to
within `4d⁴m^{d−3}/(c|I|)` by an affine linear function. -/
theorem convex_linear_approx (m d : ℕ) (hm : 0 < m) (hd : 0 < d) {c : ℝ}
    (hc : 2 * (d : ℝ) / m < c) (H : (Fin (d - 1) → ℝ) → ℝ)
    (hconv : ConvexOn ℝ (openBox c) H)
    (hbdd : ∀ x ∈ openBox c, H x ∈ Set.Icc 0 1)
    (I : Finset (Fin (d - 1) → ℕ)) (hI : ∀ v ∈ I, ∀ i, v i < m)
    (hIne : I.Nonempty) :
    ∃ v ∈ I, ∃ b : ℝ, ∃ l : Fin (d - 1) → ℝ,
      ∀ x ∈ cubeOf m v,
        |H x - (b + dot l x)| ≤
          4 * (d : ℝ) ^ 4 * (m : ℝ) ^ ((d : ℤ) - 3) / (c * I.card) := by
  classical
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hcpos : 0 < c := lt_trans (div_pos (mul_pos (by norm_num) hdR) hm') hc
  have hcardI : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.mpr hIne
  set δ := 4 * (d : ℝ) ^ 4 * (m : ℝ) ^ ((d : ℤ) - 3) / (c * I.card) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact div_pos (mul_pos (mul_pos (by norm_num) (pow_pos hdR _)) (zpow_pos hm' _))
      (mul_pos hcpos hcardI)
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 :=
    ⟨d - 1, (Nat.sub_add_cancel (Nat.one_le_of_lt hd)).symm⟩
  push_cast at hc
  -- now `hc : 2 * (↑k + 1) / ↑m < c`
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · -- `k = 0`: the domain `Fin 0 → ℝ` is a singleton, so `H` is constant
    obtain ⟨v, hvI⟩ := hIne
    refine ⟨v, hvI, H 0, 0, fun x _ ↦ ?_⟩
    have hx : x = 0 := funext fun i ↦ absurd hk0 (by have := i.isLt; omega)
    rw [hx]
    have hd0 : dot (0 : Fin k → ℝ) (0 : Fin k → ℝ) = 0 := by simp [dot]
    rw [hd0]
    simp only [add_zero, sub_self, abs_zero]
    exact hδ.le
  · -- `k ≥ 1`
    by_contra hall
    push Not at hall
    have hmc : 2 * ((k : ℝ) + 1) < c * m := by
      have h := mul_lt_mul_of_pos_right hc hm'
      rwa [div_mul_cancel₀ _ hm'.ne'] at h
    -- every `v ∈ I` yields a slope-jump witness `(iF v, sF v)`
    have hwit : ∀ w : {x // x ∈ I}, ∃ i : Fin k, ∃ s : ℝ, 0 < s ∧ s ≤ (k : ℝ) / m ∧
        uslope H m (basePt m w.1) i (basePt m w.1 i + s) ≥
          uslope H m (basePt m w.1) i (basePt m w.1 i - 1 / m) + δ * m / ((k : ℝ) + 1) := by
      intro w
      obtain ⟨v, hvI⟩ := w
      have hPv := basePt_mem_openBox hcpos (hI v hvI)
      obtain ⟨u, hu⟩ := exists_subgradient hcpos hconv hbdd hPv
      obtain ⟨x, hxc, hxf⟩ := hall v hvI (H (basePt m v) - dot u (basePt m v)) u
      have hdoteq : dot u (x - basePt m v) = dot u x - dot u (basePt m v) := by
        unfold dot
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.sub_apply]
        ring
      have hLx : H (basePt m v) - dot u (basePt m v) + dot u x =
          H (basePt m v) + dot u (x - basePt m v) := by linarith [hdoteq]
      rw [hLx] at hxf
      have hsubx := hu x (cubeOf_subset_openBox hcpos (hI v hvI) hxc)
      have hge : δ < H x - (H (basePt m v) + dot u (x - basePt m v)) := by
        have hnn : 0 ≤ H x - (H (basePt m v) + dot u (x - basePt m v)) := by linarith
        rwa [abs_of_nonneg hnn] at hxf
      have hfail : H (basePt m v) + dot u (x - basePt m v) + δ < H x := by linarith
      exact claim3 m hm hc hconv (hI v hvI) hu hδ hxc hfail
    choose iF sF hwits using hwit
    -- pigeonhole on the distinguished coordinate
    obtain ⟨i₀, -, hcard1⟩ := exists_fiber_card_ge (s := I.attach) (t := Finset.univ)
      (f := fun w ↦ iF w) (fun w _ ↦ Finset.mem_univ _)
      ⟨⟨0, hk1⟩, Finset.mem_univ _⟩
    set S := I.attach.filter (fun w ↦ iF w = i₀) with hSdef
    have hcard1' : I.card ≤ k * S.card := by
      have h := hcard1
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_attach] at h
      change I.card ≤ k * S.card at h
      exact h
    -- pigeonhole on the "line": values in all coordinates except `i₀`
    set L := Fintype.piFinset
      (fun j : Fin k ↦ if j = i₀ then ({0} : Finset ℕ) else Finset.range m) with hLdef
    have hLmaps : ∀ w ∈ S, Function.update w.1 i₀ 0 ∈ L := fun w hw ↦ by
      rw [Fintype.mem_piFinset]
      intro j
      by_cases hji : j = i₀
      · subst hji; rw [Function.update_self]; simp
      · rw [if_neg hji, Function.update_of_ne hji, Finset.mem_range]
        exact hI w.1 w.2 j
    have hLcard : L.card = m ^ (k - 1) := by
      rw [Fintype.card_piFinset]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      rw [if_pos rfl, Finset.card_singleton, one_mul]
      have hprod : ∏ x ∈ Finset.univ.erase i₀,
            (if x = i₀ then ({0} : Finset ℕ) else Finset.range m).card
          = ∏ _x ∈ Finset.univ.erase i₀, m :=
        Finset.prod_congr rfl fun j hj ↦ by
          rw [if_neg (Finset.ne_of_mem_erase hj), Finset.card_range]
      rw [hprod, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
        Fintype.card_fin]
    have hLne : L.Nonempty := ⟨fun _ ↦ 0, by
      rw [Fintype.mem_piFinset]
      intro j
      by_cases hji : j = i₀
      · subst hji; simp
      · rw [if_neg hji, Finset.mem_range]; exact hm⟩
    obtain ⟨a, haL, hcard2⟩ := exists_fiber_card_ge (s := S) (t := L)
      (f := fun w ↦ Function.update w.1 i₀ 0) hLmaps hLne
    set S₁ := S.filter (fun w ↦ Function.update w.1 i₀ 0 = a) with hS₁def
    have ha_i₀ : a i₀ = 0 := by
      have h := (Fintype.mem_piFinset.mp haL) i₀
      rw [if_pos rfl] at h
      exact Finset.mem_singleton.mp h
    have ha_lt : ∀ j, j ≠ i₀ → a j < m := fun j hj ↦ by
      have h := (Fintype.mem_piFinset.mp haL) j
      rw [if_neg hj] at h
      exact Finset.mem_range.mp h
    -- pigeonhole on the residue class mod `k + 1`
    obtain ⟨r₀, -, hcard3⟩ := exists_fiber_card_ge (s := S₁) (t := Finset.range (k + 1))
      (f := fun w ↦ w.1 i₀ % (k + 1))
      (fun w _ ↦ Finset.mem_range.mpr (Nat.mod_lt _ (Nat.succ_pos k)))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
    set S₂ := S₁.filter (fun w ↦ w.1 i₀ % (k + 1) = r₀) with hS₂def
    have hS₂sub : S₂ ⊆ S₁ := fun x hx ↦ (Finset.mem_filter.mp hx).1
    have hS₁sub : S₁ ⊆ S := fun x hx ↦ (Finset.mem_filter.mp hx).1
    have hIbound : I.card ≤ k * m ^ (k - 1) * (k + 1) * S₂.card := by
      calc I.card ≤ k * S.card := hcard1'
        _ ≤ k * (L.card * S₁.card) := mul_le_mul_right hcard2 k
        _ = k * (m ^ (k - 1)) * S₁.card := by rw [hLcard]; ring
        _ ≤ k * m ^ (k - 1) * ((k + 1) * S₂.card) := by
          rw [Finset.card_range] at hcard3
          exact mul_le_mul_right hcard3 _
        _ = k * m ^ (k - 1) * (k + 1) * S₂.card := by ring
    have hS₂ne : S₂.Nonempty := by
      have hpos : 0 < S₂.card := by
        by_contra h0
        push Not at h0
        rw [Nat.eq_zero_of_le_zero h0] at hIbound
        simp only [mul_zero, Nat.le_zero] at hIbound
        have hposI := Finset.card_pos.mpr hIne
        omega
      exact Finset.card_pos.mp hpos
    -- common line through `a` in direction `i₀`
    set P₀ := basePt m a with hP₀def
    have hPa : P₀ ∈ openBox c := basePt_mem_openBox hcpos fun j ↦ by
      by_cases hji : j = i₀
      · subst hji; rw [ha_i₀]; exact hm
      · exact ha_lt j hji
    set φ₀ := fun t ↦ H (Function.update P₀ i₀ t) with hφ₀def
    have hφ₀ : ConvexOn ℝ (Set.Ioo (-c) (1 + c)) φ₀ := convexOn_update_line hconv hPa i₀
    have hφ₀bdd : ∀ x ∈ Set.Ioo (-c) (1 + c), φ₀ x ∈ Set.Icc 0 1 :=
      fun t ht ↦ hbdd _ (update_mem_openBox hPa i₀ ht)
    set Φ := fun t ↦ uslope H m P₀ i₀ t with hΦdef
    have hbase : ∀ w ∈ S₂, ∀ t : ℝ, Function.update (basePt m w.1) i₀ t =
        Function.update P₀ i₀ t := by
      intro w hw t
      have hwa : Function.update w.1 i₀ 0 = a := (Finset.mem_filter.mp (hS₂sub hw)).2
      funext j
      by_cases hji : j = i₀
      · subst hji; simp [Function.update_self]
      · rw [Function.update_of_ne hji, Function.update_of_ne hji]
        show (w.1 j : ℝ) / m = (a j : ℝ) / m
        rw [← congrFun hwa j, Function.update_of_ne hji]
    have huseq : ∀ w ∈ S₂, ∀ t : ℝ, uslope H m (basePt m w.1) i₀ t =
        uslope H m P₀ i₀ t := by
      intro w hw t
      unfold uslope
      rw [hbase w hw t, hbase w hw (t + 1 / m)]
    set lo : {x // x ∈ I} → ℝ := fun w ↦ ((w.1 i₀ : ℝ) - 1) / m with hlodef
    set hi : {x // x ∈ I} → ℝ := fun w ↦ (w.1 i₀ : ℝ) / m + sF w with hhidef
    have hmod : ∀ w ∈ S₂, w.1 i₀ % (k + 1) = r₀ := fun w hw ↦ (Finset.mem_filter.mp hw).2
    have hline : ∀ w ∈ S₂, Function.update w.1 i₀ 0 = a :=
      fun w hw ↦ (Finset.mem_filter.mp (hS₂sub hw)).2
    have hiFi : ∀ w ∈ S₂, iF w = i₀ :=
      fun w hw ↦ (Finset.mem_filter.mp (hS₁sub (hS₂sub hw))).2
    have hinj : ∀ x ∈ S₂, ∀ y ∈ S₂, x.1 i₀ = y.1 i₀ → x = y := by
      intro x hx y hy hxy
      apply Subtype.ext
      funext j
      by_cases hji : j = i₀
      · subst hji; exact hxy
      · have hxa := congrFun (hline x hx) j
        have hya := congrFun (hline y hy) j
        rw [Function.update_of_ne hji] at hxa hya
        rw [hxa, hya]
    have hsep : ∀ x ∈ S₂, ∀ y ∈ S₂, x.1 i₀ < y.1 i₀ → x.1 i₀ + (k + 1) ≤ y.1 i₀ := by
      intro x hx y hy hlt
      have h1 : x.1 i₀ % (k + 1) = y.1 i₀ % (k + 1) := by rw [hmod x hx, hmod y hy]
      have hxd := Nat.div_add_mod (x.1 i₀) (k + 1)
      have hyd := Nat.div_add_mod (y.1 i₀) (k + 1)
      have hq : x.1 i₀ / (k + 1) < y.1 i₀ / (k + 1) := by
        by_contra h
        push Not at h
        have h2 : (k + 1) * (y.1 i₀ / (k + 1)) ≤ (k + 1) * (x.1 i₀ / (k + 1)) :=
          mul_le_mul_right h (k + 1)
        omega
      have hle : (k + 1) * (x.1 i₀ / (k + 1)) + (k + 1) ≤ (k + 1) * (y.1 i₀ / (k + 1)) := by
        have h3 : x.1 i₀ / (k + 1) + 1 ≤ y.1 i₀ / (k + 1) := hq
        have h2 := mul_le_mul_right h3 (k + 1)
        have h4 : (k + 1) * (x.1 i₀ / (k + 1) + 1) =
            (k + 1) * (x.1 i₀ / (k + 1)) + (k + 1) := by ring
        rwa [h4] at h2
      omega
    have hmono : ∀ x ∈ S₂, ∀ y ∈ S₂, x.1 i₀ < y.1 i₀ → Φ (hi x) ≤ Φ (lo y) := by
      intro x hx y hy hlt
      have hsep' := hsep x hx y hy hlt
      have hsx : 0 < sF x := (hwits x).1
      have hsFx : sF x ≤ (k : ℝ) / m := (hwits x).2.1
      have hxm : (x.1 i₀ : ℝ) ≤ (m : ℝ) - 1 := by
        have hle : x.1 i₀ ≤ m - 1 := by have h := hI x.1 x.2 i₀; omega
        have hcast : (x.1 i₀ : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hle
        rwa [Nat.cast_sub (Nat.one_le_of_lt hm), Nat.cast_one] at hcast
      have hym : (y.1 i₀ : ℝ) ≤ (m : ℝ) - 1 := by
        have hle : y.1 i₀ ≤ m - 1 := by have h := hI y.1 y.2 i₀; omega
        have hcast : (y.1 i₀ : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hle
        rwa [Nat.cast_sub (Nat.one_le_of_lt hm), Nat.cast_one] at hcast
      have hix_mem : hi x ∈ Set.Ioo (-c) (1 + c) := by
        have hxnn : (0 : ℝ) ≤ (x.1 i₀ : ℝ) / m := by positivity
        have hub : hi x ≤ ((m : ℝ) - 1) / m + (k : ℝ) / m := by
          change (x.1 i₀ : ℝ) / m + sF x ≤ _
          exact add_le_add (div_le_div_of_nonneg_right hxm hm'.le) hsFx
        have hlt' : ((m : ℝ) - 1) / m + (k : ℝ) / m < 1 + c := by
          rw [← add_div, div_lt_iff₀ hm']
          linarith
        constructor
        · change -c < (x.1 i₀ : ℝ) / m + sF x
          linarith
        · linarith
      have hloy_mem : lo y + 1 / m ∈ Set.Ioo (-c) (1 + c) := by
        have heq : lo y + 1 / m = (y.1 i₀ : ℝ) / m := by
          change ((y.1 i₀ : ℝ) - 1) / m + 1 / m = _
          rw [← add_div, sub_add_cancel]
        rw [heq]
        constructor
        · have hnn : (0 : ℝ) ≤ (y.1 i₀ : ℝ) / m := by positivity
          linarith [hnn, hcpos]
        · have h1 : (y.1 i₀ : ℝ) / m ≤ ((m : ℝ) - 1) / m :=
            div_le_div_of_nonneg_right hym hm'.le
          have h2 : ((m : ℝ) - 1) / m < 1 := by rw [div_lt_iff₀ hm']; linarith
          linarith
      have hle' : hi x ≤ lo y := by
        change (x.1 i₀ : ℝ) / m + sF x ≤ ((y.1 i₀ : ℝ) - 1) / m
        have h4 : (x.1 i₀ : ℝ) + (k : ℝ) + 1 ≤ y.1 i₀ := by
          exact_mod_cast hsep'
        have hub : (x.1 i₀ : ℝ) / m + sF x ≤ (x.1 i₀ : ℝ) / m + (k : ℝ) / m :=
          add_le_add_right hsFx _
        rw [← add_div] at hub
        have hle2 : ((x.1 i₀ : ℝ) + k) / m ≤ ((y.1 i₀ : ℝ) - 1) / m :=
          div_le_div_of_nonneg_right (by linarith) hm'.le
        linarith [hub, hle2]
      exact unit_slope_mono hφ₀ (one_div_pos.mpr hm') hix_mem hloy_mem hle'
    have hjump : ∀ w ∈ S₂, Φ (lo w) + δ * m / ((k : ℝ) + 1) ≤ Φ (hi w) := by
      intro w hw
      have h1 := (hwits w).2.2
      rw [hiFi w hw] at h1
      show uslope H m P₀ i₀ (lo w) + δ * m / ((k : ℝ) + 1) ≤ uslope H m P₀ i₀ (hi w)
      rw [← huseq w hw (lo w), ← huseq w hw (hi w)]
      have hlo : lo w = basePt m w.1 i₀ - 1 / m := by
        show ((w.1 i₀ : ℝ) - 1) / m = _
        rw [sub_div]
        rfl
      have hhi : hi w = basePt m w.1 i₀ + sF w := rfl
      rw [hlo, hhi]
      exact h1
    -- telescoping the jumps along the line
    obtain ⟨a', ha', b', hb', hsumub⟩ :=
      sum_jumps_le (Φ := Φ) (g := fun w : {x // x ∈ I} ↦ w.1 i₀) (lo := lo) (hi := hi)
        (S₀ := S₂) hinj hmono S₂ (fun _ hx ↦ hx) hS₂ne
    have hsumlb : (S₂.card : ℝ) * (δ * m / ((k : ℝ) + 1)) ≤
        ∑ w ∈ S₂, (Φ (hi w) - Φ (lo w)) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro w hw
      have h := hjump w hw
      linarith
    have hℓ : (0 : ℝ) < S₂.card := by exact_mod_cast Finset.card_pos.mpr hS₂ne
    have hP2 : (0 : ℝ) < (m : ℝ) ^ (k - 1) := pow_pos hm' _
    -- endpoint slope bounds
    have hbound : ∀ w ∈ S₂, ∀ t : ℝ, (t = lo w ∨ t = hi w) → |Φ t| ≤ 4 / c := by
      intro w hw t ht
      rcases ht with rfl | rfl
      · have hwm : (w.1 i₀ : ℝ) ≤ (m : ℝ) - 1 := by
          have hle : w.1 i₀ ≤ m - 1 := by have h := hI w.1 w.2 i₀; omega
          have hcast : (w.1 i₀ : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hle
          rwa [Nat.cast_sub (Nat.one_le_of_lt hm), Nat.cast_one] at hcast
        have ht1 : -c / 2 ≤ lo w := by
          have h1 : (0 : ℝ) ≤ (w.1 i₀ : ℝ) := Nat.cast_nonneg _
          show -c / 2 ≤ ((w.1 i₀ : ℝ) - 1) / m
          rw [le_div_iff₀ hm']
          linarith [h1, hmc]
        have ht2 : lo w + 1 / m ≤ 1 + c / 2 := by
          show ((w.1 i₀ : ℝ) - 1) / m + 1 / m ≤ 1 + c / 2
          rw [← add_div, sub_add_cancel]
          have h1 : (w.1 i₀ : ℝ) / m ≤ ((m : ℝ) - 1) / m :=
            div_le_div_of_nonneg_right hwm hm'.le
          have h2 : ((m : ℝ) - 1) / m < 1 := by rw [div_lt_iff₀ hm']; linarith
          linarith
        exact abs_secant_le hcpos hφ₀ hφ₀bdd (one_div_pos.mpr hm') ht1 ht2
      · have hwm : (w.1 i₀ : ℝ) ≤ (m : ℝ) - 1 := by
          have hle : w.1 i₀ ≤ m - 1 := by have h := hI w.1 w.2 i₀; omega
          have hcast : (w.1 i₀ : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hle
          rwa [Nat.cast_sub (Nat.one_le_of_lt hm), Nat.cast_one] at hcast
        have ht1 : -c / 2 ≤ hi w := by
          show -c / 2 ≤ (w.1 i₀ : ℝ) / m + sF w
          have h1 : (0 : ℝ) ≤ (w.1 i₀ : ℝ) / m := by positivity
          have h2 : (0 : ℝ) ≤ sF w := (hwits w).1.le
          linarith
        have ht2 : hi w + 1 / m ≤ 1 + c / 2 := by
          show (w.1 i₀ : ℝ) / m + sF w + 1 / m ≤ 1 + c / 2
          have hub : (w.1 i₀ : ℝ) / m + sF w + 1 / m ≤
              ((m : ℝ) - 1) / m + (k : ℝ) / m + 1 / m := by
            have hA : (w.1 i₀ : ℝ) / m + sF w ≤ ((m : ℝ) - 1) / m + (k : ℝ) / m :=
              add_le_add (div_le_div_of_nonneg_right hwm hm'.le) (hwits w).2.1
            exact add_le_add_left hA (1 / m)
          have heq : ((m : ℝ) - 1) / m + (k : ℝ) / m + 1 / m = (m + k) / m := by
            rw [← add_div, ← add_div]; congr 1; ring
          rw [heq] at hub
          have hle : (m + k : ℝ) / m ≤ 1 + c / 2 := by
            rw [div_le_iff₀ hm']
            linarith [hmc]
          linarith
        exact abs_secant_le hcpos hφ₀ hφ₀bdd (one_div_pos.mpr hm') ht1 ht2
    have hlo' : -4 / c ≤ Φ (lo a') := by
      have h := (abs_le.mp (hbound a' ha' _ (Or.inl rfl))).1
      rwa [← neg_div] at h
    have hhi' : Φ (hi b') ≤ 4 / c :=
      (abs_le.mp (hbound b' hb' _ (Or.inr rfl))).2
    have htot2 : (S₂.card : ℝ) * (δ * m / ((k : ℝ) + 1)) ≤ 8 / c :=
      calc (S₂.card : ℝ) * (δ * m / ((k : ℝ) + 1))
          ≤ ∑ w ∈ S₂, (Φ (hi w) - Φ (lo w)) := hsumlb
        _ ≤ Φ (hi b') - Φ (lo a') := hsumub
        _ ≤ 4 / c - -4 / c := sub_le_sub hhi' hlo'
        _ = 8 / c := by ring_nf
    -- hence `δ * (c·m·ℓ) ≤ 8·(k+1)`
    have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hJeq : (S₂.card : ℝ) * (δ * m / ((k : ℝ) + 1)) * c ≤ 8 := by
      have h1 := mul_le_mul_of_nonneg_right htot2 hcpos.le
      rwa [div_mul_cancel₀ _ hcpos.ne'] at h1
    have hδle : δ * (c * m * (S₂.card : ℝ)) ≤ 8 * ((k : ℝ) + 1) := by
      have h2 := mul_le_mul_of_nonneg_right hJeq hk1pos.le
      have h3 : (S₂.card : ℝ) * (δ * m / ((k : ℝ) + 1)) * c * ((k : ℝ) + 1) =
          (S₂.card : ℝ) * δ * m * c := by
        field_simp
      rw [h3] at h2
      linarith [h2]
    -- expand `δ` and the bound `|I| ≤ k·m^{k−1}·(k+1)·ℓ`
    have hδeq : δ * (c * (I.card : ℝ)) =
        4 * ((k + 1 : ℕ) : ℝ) ^ 4 * (m : ℝ) ^ (((k + 1 : ℕ) : ℤ) - 3) := by
      rw [hδdef, div_mul_cancel₀ _ (mul_ne_zero hcpos.ne' hcardI.ne')]
    have hexp : ((k - 1 : ℕ) : ℤ) = (((k + 1 : ℕ) : ℤ)) - 2 := by
      rw [Nat.cast_sub hk1]
      push_cast
      ring
    have hz : (m : ℝ) ^ (((k + 1 : ℕ) : ℤ) - 3) * (m : ℝ) = (m : ℝ) ^ (k - 1) := by
      rw [← zpow_natCast, hexp, ← zpow_add_one₀ hm'.ne']
      congr 1
      ring
    have hA : 4 * ((k + 1 : ℕ) : ℝ) ^ 4 * (m : ℝ) ^ (k - 1) * (S₂.card : ℝ) ≤
        8 * ((k : ℝ) + 1) * (I.card : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hδle hcardI.le
      have h2 : δ * (c * m * (S₂.card : ℝ)) * (I.card : ℝ) =
          4 * ((k + 1 : ℕ) : ℝ) ^ 4 * (m : ℝ) ^ (k - 1) * (S₂.card : ℝ) := by
        calc δ * (c * m * (S₂.card : ℝ)) * (I.card : ℝ)
            = (δ * (c * (I.card : ℝ))) * (m * (S₂.card : ℝ)) := by ring
          _ = 4 * ((k + 1 : ℕ) : ℝ) ^ 4 * (m : ℝ) ^ (((k + 1 : ℕ) : ℤ) - 3) *
              ((m : ℝ) * (S₂.card : ℝ)) := by rw [hδeq]
          _ = 4 * ((k + 1 : ℕ) : ℝ) ^ 4 * ((m : ℝ) ^ (((k + 1 : ℕ) : ℤ) - 3) * (m : ℝ)) *
              (S₂.card : ℝ) := by ring
          _ = 4 * ((k + 1 : ℕ) : ℝ) ^ 4 * ((m : ℝ) ^ (k - 1)) * (S₂.card : ℝ) := by rw [hz]
      rwa [h2] at h1
    have hIle : (I.card : ℝ) ≤
        (k : ℝ) * (m : ℝ) ^ (k - 1) * ((k + 1 : ℕ) : ℝ) * (S₂.card : ℝ) := by
      exact_mod_cast hIbound
    have hB : (8 : ℝ) * ((k : ℝ) + 1) * (I.card : ℝ) ≤
        (8 : ℝ) * ((k : ℝ) + 1) *
          ((k : ℝ) * (m : ℝ) ^ (k - 1) * ((k + 1 : ℕ) : ℝ) * (S₂.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hIle (by positivity)
    -- `4·(k+1)⁴·m^{k−1}·ℓ ≤ 8·(k+1)²·k·m^{k−1}·ℓ`, hence `(k+1)² ≤ 2k`
    have hC : ((k : ℝ) + 1) ^ 2 ≤ 2 * (k : ℝ) := by
      have hpos' : (0 : ℝ) <
          4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ (k - 1) * (S₂.card : ℝ) :=
        mul_pos (mul_pos (mul_pos (by norm_num)
          (pow_pos (Nat.cast_pos.mpr (Nat.succ_pos k)) _)) hP2) hℓ
      have h' := le_trans hA hB
      have hkcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have key : ((k : ℝ) + 1) ^ 2 *
            (4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ (k - 1) * (S₂.card : ℝ)) ≤
          2 * (k : ℝ) *
            (4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ (k - 1) * (S₂.card : ℝ)) := by
        have e1 : ((k : ℝ) + 1) ^ 2 *
            (4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ (k - 1) * (S₂.card : ℝ)) =
            4 * ((k + 1 : ℕ) : ℝ) ^ 4 * (m : ℝ) ^ (k - 1) * (S₂.card : ℝ) := by
          rw [hkcast]; ring
        have e2 : 2 * (k : ℝ) *
            (4 * ((k + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ) ^ (k - 1) * (S₂.card : ℝ)) =
            8 * ((k : ℝ) + 1) * ((k : ℝ) * (m : ℝ) ^ (k - 1) * ((k + 1 : ℕ) : ℝ) *
              (S₂.card : ℝ)) := by
          rw [hkcast]; ring
        rw [e1, e2]
        exact h'
      exact (mul_le_mul_iff_left₀ hpos').mp key
    nlinarith [sq_nonneg ((k : ℝ))]

/-!
## Rough convex position of the dyadic boxes (equation (3))

The next lemmas are the combinatorial-geometric observation (3) of the
paper's proof of Lemma 1: if each dyadic `r`-box `B_i` contains *more* than
`δ|A|` points of a set `A` in `δ`-convex position, then the `4√d`-dilate of
`B_i` is never contained in the convex hull of the union of the other boxes.
-/

/-- **Segment escape**: if `s` is closed, `p ∈ s`, `q ∉ s`, and `D` is a
convex set containing both `p` and `q`, then `frontier s ∩ D` is
nonempty — the segment from `p` to `q` leaves `s` inside `D`.  This is
the existence statement for the boundary point `xᵢ ∈ ∂P ∩ B̃ᵢ` in the
paper's proof of Lemma 1. -/
theorem exists_mem_frontier_inter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} (hs : IsClosed s) {D : Set E}
    (hD : Convex ℝ D) {p q : E} (hp : p ∈ s) (hpD : p ∈ D)
    (hq : q ∉ s) (hqD : q ∈ D) :
    ∃ x ∈ frontier s, x ∈ D := by
  -- Parametrize the segment `[p, q]` by `t ↦ (1 - t) • p + t • q`.
  set L : ℝ → E := fun t ↦ (1 - t) • p + t • q with hLdef
  have hL : Continuous L := by
    show Continuous fun t : ℝ ↦ (1 - t) • p + t • q
    fun_prop
  set T : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 | L t ∈ s} with hTdef
  have hTsub : T ⊆ Set.Icc 0 1 := fun t ht ↦ ht.1
  have hTcl : IsClosed T := by
    have e : T = L ⁻¹' s ∩ Set.Icc (0 : ℝ) 1 := by
      ext t; simp [hTdef, and_comm]
    rw [e]
    exact (hs.preimage hL).inter isClosed_Icc
  have hTne : T.Nonempty := by
    refine ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩
    show L 0 ∈ s
    simp only [hLdef, sub_zero, one_smul, zero_smul, add_zero]
    exact hp
  have hTcomp : IsCompact T :=
    isCompact_Icc.of_isClosed_subset hTcl hTsub
  have hTbdd : BddAbove T := hTcomp.bddAbove
  set t₀ := sSup T with ht₀def
  have ht₀T : t₀ ∈ T := hTcomp.sSup_mem hTne
  have ht₀ge : ∀ t ∈ T, t ≤ t₀ := fun t ht ↦ le_csSup hTbdd ht
  have ht₀lt : t₀ < 1 := by
    refine lt_of_le_of_ne ht₀T.1.2 fun h ↦ ?_
    have hL1 : L 1 = q := by
      simp only [hLdef, sub_self, zero_smul, one_smul, zero_add]
    have h1T : (1 : ℝ) ∈ T := h ▸ ht₀T
    rw [hTdef] at h1T
    have h1s : L 1 ∈ s := h1T.2
    rw [hL1] at h1s
    exact hq h1s
  -- The last point of `T` is not interior to `s`: a small push past `t₀`
  -- stays inside `s`, contradicting maximality.
  have hnotint : L t₀ ∉ interior s := by
    intro hx
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp
      (isOpen_interior.mem_nhds hx)
    have hpre : L ⁻¹' Metric.ball (L t₀) ε ∈ nhds t₀ :=
      hL.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhds_iff.mp hpre
    set t' := t₀ + min ρ (1 - t₀) / 2 with ht'def
    have hmin : 0 < min ρ (1 - t₀) := lt_min hρ (sub_pos.mpr ht₀lt)
    have ht'T : t' ∈ T := by
      have hmem : t' ∈ Metric.ball t₀ ρ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have e : t' - t₀ = min ρ (1 - t₀) / 2 := by rw [ht'def]; ring
        rw [e, Real.norm_eq_abs, abs_of_pos (by linarith [hmin])]
        calc min ρ (1 - t₀) / 2 ≤ ρ / 2 :=
              div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
          _ < ρ := half_lt_self hρ
      have hLt' : L t' ∈ Metric.ball (L t₀) ε := hρs hmem
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [ht'def]; linarith [ht₀T.1.1]
      · have h2 : min ρ (1 - t₀) ≤ 1 - t₀ := min_le_right _ _
        rw [ht'def]
        linarith [ht₀T.1.2]
      · exact interior_subset (hεs hLt')
    have hle := ht₀ge t' ht'T
    rw [ht'def] at hle
    linarith
  refine ⟨L t₀, ⟨subset_closure ht₀T.2, hnotint⟩, ?_⟩
  exact hD hpD hqD (sub_nonneg.mpr ht₀T.1.2) ht₀T.1.1 (by ring)

/-- `x ↦ u · x` as a linear map `ℝ^k → ℝ`. -/
def dotLinear {k : ℕ} (u : Fin k → ℝ) : (Fin k → ℝ) →ₗ[ℝ] ℝ where
  toFun x := dot u x
  map_add' x y := by
    simp only [dot, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  map_smul' a x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring

@[simp]
theorem dotLinear_apply {k : ℕ} (u x : Fin k → ℝ) : dotLinear u x = dot u x := rfl

/-- The half-open box `∏ᵢ [lᵢ, lᵢ + r)`, the shape of the dyadic `r`-boxes
in the paper's proof of Lemma 1. -/
def dyadicBox {k : ℕ} (l : Fin k → ℝ) (r : ℝ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun i ↦ Set.Ico (l i) (l i + r)

/-- The closed box `∏ᵢ [cᵢ − s/2, cᵢ + s/2]` of side `s` centered at `c`. -/
def centeredBox {k : ℕ} (c : Fin k → ℝ) (s : ℝ) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun i ↦ Set.Icc (c i - s / 2) (c i + s / 2)

/-- **Equation (3) of the paper's proof of Lemma 1**: a family of `r`-boxes
each containing *more* than `δ|A|` points of a set `A` in `δ`-convex
position is "in convex position": the `4√d`-dilate of `B_{l₀}` about its
center contains a point outside `closure (conv (⋃ B_l))` (hence outside
the convex hull of the other boxes).

Proof: pick `a₀ ∈ A ∩ B_{l₀}` and its `δ`-small half-space `{u·x ≥ t}`.
Every other box contains `> δ|A|` points of `A`, hence a point with
`u·x < t`; being `r`-boxes, they are all contained in the slab
`{u·x ≤ t + r‖u‖₁}`.  On the other hand `B_{l₀}` straddles the hyperplane
`{u·x = t}` (it has `> δ|A|` points but the cap has `≤ δ|A|`), so its
`4√d`-dilate reaches beyond `u·x = t + r‖u‖₁`. -/
theorem dilatedBox_notsubset_convexHull {d : ℕ} (hd : 1 ≤ d)
    {A : Finset (Fin d → ℝ)} {δ : ℝ} (hδ : 0 < δ) (hcp : InDeltaConvexPosition A δ)
    {r : ℝ} (hr : 0 < r) {I : Finset (Fin d → ℝ)} {l₀ : Fin d → ℝ}
    (hl₀ : l₀ ∈ I)
    (hbig : ∀ l ∈ I, δ * A.card <
      ((A.filter fun a ↦ ∀ j, a j ∈ Set.Ico (l j) (l j + r)).card : ℝ)) :
    ∃ x ∈ centeredBox (fun j ↦ l₀ j + r / 2) (4 * Real.sqrt d * r),
      x ∉ closure (convexHull ℝ (⋃ l ∈ I, dyadicBox l r)) := by
  classical
  -- The base box meets `A`; in particular `A` is nonempty.
  have hF₀ne : (A.filter fun a ↦
      ∀ j, a j ∈ Set.Ico (l₀ j) (l₀ j + r)).Nonempty := by
    apply Finset.card_pos.mp
    have hnn : (0 : ℝ) ≤ δ * A.card := mul_nonneg hδ.le (Nat.cast_nonneg _)
    exact_mod_cast lt_of_le_of_lt hnn (hbig l₀ hl₀)
  obtain ⟨a₀, ha₀⟩ := hF₀ne
  rw [Finset.mem_filter] at ha₀
  obtain ⟨ha₀A, ha₀B⟩ := ha₀
  have hcardpos : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨a₀, ha₀A⟩
  obtain ⟨u, t, ht, hcap⟩ := hcp a₀ ha₀A
  set Sp : ℝ := ∑ j, max (u j) 0 with hSp
  set Sm : ℝ := ∑ j, max (-u j) 0 with hSm
  -- `u ≠ 0`, else the cap is all of `A` and `δ ≥ 1`, contradicting `hbig`.
  have hun : u ≠ 0 := by
    intro hu
    have hdot : ∀ x : Fin d → ℝ, dot u x = 0 := fun x ↦ by
      rw [hu]; simp [dot]
    have ht0 : t ≤ 0 := le_trans ht (le_of_eq (hdot a₀))
    have hfull : A.filter (fun x ↦ t ≤ dot u x) = A :=
      Finset.filter_eq_self.mpr fun x _ ↦ by rw [hdot]; exact ht0
    rw [hfull] at hcap
    have hδ1 : (1 : ℝ) ≤ δ :=
      le_of_mul_le_mul_right
        (show (1 : ℝ) * A.card ≤ δ * A.card by rwa [one_mul]) hcardpos
    have hle : ((A.filter fun a ↦
        ∀ j, a j ∈ Set.Ico (l₀ j) (l₀ j + r)).card : ℝ) ≤ A.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    linarith [hbig l₀ hl₀]
  -- Every box has a point of `A` strictly below the cap hyperplane.
  have hex : ∀ l ∈ I, ∃ a ∈ A,
      (∀ j, a j ∈ Set.Ico (l j) (l j + r)) ∧ dot u a < t := by
    intro l hl
    have hbig' := hbig l hl
    have hnsub : ¬ (A.filter fun a ↦ ∀ j, a j ∈ Set.Ico (l j) (l j + r)) ⊆
        A.filter fun x ↦ t ≤ dot u x := by
      intro hsub'
      have hlt : ((A.filter fun x ↦ t ≤ dot u x).card : ℝ) <
          ((A.filter fun a ↦ ∀ j, a j ∈ Set.Ico (l j) (l j + r)).card : ℝ) :=
        lt_of_le_of_lt hcap hbig'
      have hle' : ((A.filter fun a ↦ ∀ j, a j ∈ Set.Ico (l j) (l j + r)).card : ℝ)
          ≤ ((A.filter fun x ↦ t ≤ dot u x).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub'
      exact absurd hle' (not_le_of_gt hlt)
    obtain ⟨a, haB, haC⟩ := Finset.not_subset.mp hnsub
    rw [Finset.mem_filter] at haB haC
    push Not at haC
    exact ⟨a, haB.1, haB.2, haC haB.1⟩
  -- Two points of the same `r`-box differ by at most `r·‖u‖₁` under `dot u`.
  have hsub : ∀ x y : Fin d → ℝ, dot u x = dot u y + dot u (x - y) := by
    intro x y
    simp only [dot, Pi.sub_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hbox : ∀ l : Fin d → ℝ, ∀ x y : Fin d → ℝ,
      (∀ j, x j ∈ Set.Ico (l j) (l j + r)) →
      (∀ j, y j ∈ Set.Ico (l j) (l j + r)) →
      dot u x ≤ dot u y + r * ∑ j, |u j| := by
    intro l x y hx hy
    have hdiff : ∀ j, |x j - y j| ≤ r := fun j ↦ by
      have hxj := Set.mem_Ico.mp (hx j)
      have hyj := Set.mem_Ico.mp (hy j)
      rw [abs_le]
      constructor <;> linarith
    rw [hsub x y]
    calc dot u y + dot u (x - y)
        ≤ dot u y + ∑ j, |u j| * |x j - y j| :=
          add_le_add le_rfl (Finset.sum_le_sum fun j _ ↦ by
            simp only [Pi.sub_apply]
            calc u j * (x j - y j) ≤ |u j * (x j - y j)| := le_abs_self _
              _ = |u j| * |x j - y j| := abs_mul _ _)
      _ ≤ dot u y + ∑ j, |u j| * r :=
          add_le_add le_rfl (Finset.sum_le_sum fun j _ ↦
            mul_le_mul_of_nonneg_left (hdiff j) (abs_nonneg _))
      _ = dot u y + r * ∑ j, |u j| := by
          rw [← Finset.sum_mul]; ring
  -- The "width" `w = r·‖u‖₁` is positive.
  set w := r * ∑ j, |u j| with hw
  have hwpos : 0 < w := by
    have hs : (0 : ℝ) < ∑ j, |u j| := by
      apply Finset.sum_pos' (fun j _ ↦ abs_nonneg _)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hun
      exact ⟨j, Finset.mem_univ _, abs_pos.mpr (by simpa using hj)⟩
    exact mul_pos hr hs
  -- Each box — including `B_{l₀}` itself, which straddles `H` — lies in
  -- the half-space `{u·x ≤ t + w}`.
  have hupper : (⋃ l ∈ I, dyadicBox l r) ⊆
      {x : Fin d → ℝ | dot u x ≤ t + w} := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨a, -, haB, haLt⟩ := hex l (Finset.mem_coe.mp hl)
    calc dot u x ≤ dot u a + w :=
          hbox l x a (fun j ↦ Set.mem_univ_pi.mp hxl j) haB
      _ ≤ t + w := by linarith [haLt]
  have hconvsub : convexHull ℝ (⋃ l ∈ I, dyadicBox l r) ⊆
      {x : Fin d → ℝ | dot u x ≤ t + w} := by
    have hset : {x : Fin d → ℝ | dot u x ≤ t + w} =
        dotLinear u ⁻¹' Set.Iic (t + w) := rfl
    apply convexHull_min hupper
    rw [hset]
    exact (convex_Iic _).linear_preimage (dotLinear u)
  -- Lower bound `t − r·S⁺ ≤ u·l₀` from `a₀ ∈ B_{l₀}` with `t ≤ u·a₀`
  -- (here `S⁺ = Σ max(uⱼ, 0)`).
  have hdiff₀ : ∀ j, 0 ≤ a₀ j - l₀ j ∧ a₀ j - l₀ j ≤ r := fun j ↦ by
    have h := Set.mem_Ico.mp (ha₀B j)
    constructor <;> linarith
  have hstep : dot u a₀ ≤ dot u l₀ + r * Sp := by
    rw [hsub a₀ l₀]
    calc dot u l₀ + dot u (a₀ - l₀)
        ≤ dot u l₀ + ∑ j, max (u j) 0 * r :=
          add_le_add le_rfl (Finset.sum_le_sum fun j _ ↦ by
            simp only [Pi.sub_apply]
            calc u j * (a₀ j - l₀ j) ≤ max (u j) 0 * (a₀ j - l₀ j) :=
                  mul_le_mul_of_nonneg_right (le_max_left _ _) (hdiff₀ j).1
              _ ≤ max (u j) 0 * r :=
                  mul_le_mul_of_nonneg_left (hdiff₀ j).2 (le_max_right _ _))
      _ = dot u l₀ + r * Sp := by
          rw [← Finset.sum_mul, ← hSp]; ring
  have hlow : t - r * Sp ≤ dot u l₀ := by linarith [ht, hstep]
  -- The far vertex of the dilated box in direction `u`.
  set c : Fin d → ℝ := fun j ↦ l₀ j + r / 2 with hc
  set s : Fin d → ℝ := fun j ↦ if 0 ≤ u j then (1 : ℝ) else -1 with hs
  set v : Fin d → ℝ := fun j ↦ c j + 2 * Real.sqrt d * r * s j with hv
  have hsign : ∀ j, u j * s j = |u j| := fun j ↦ by
    show u j * (if 0 ≤ u j then (1 : ℝ) else -1) = |u j|
    by_cases hj : 0 ≤ u j
    · rw [if_pos hj, mul_one, abs_of_nonneg hj]
    · rw [if_neg hj, mul_neg, mul_one, abs_of_neg (lt_of_not_ge hj)]
  have hvc : dot u v = dot u c + 2 * Real.sqrt d * w := by
    have e : ∀ j : Fin d,
        u j * (c j + 2 * Real.sqrt d * r * s j) =
          u j * c j + 2 * Real.sqrt d * r * |u j| := fun j ↦ by
      have h : u j * (2 * Real.sqrt d * r * s j) =
          2 * Real.sqrt d * r * (u j * s j) := by ring
      rw [mul_add, h, hsign j]
    calc dot u v = ∑ j, u j * v j := rfl
      _ = ∑ j, (u j * c j + 2 * Real.sqrt d * r * |u j|) :=
          Finset.sum_congr rfl fun j _ ↦ e j
      _ = dot u c + 2 * Real.sqrt d * r * ∑ j, |u j| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
      _ = dot u c + 2 * Real.sqrt d * w := by rw [hw]; ring
  have hdotc : dot u c = dot u l₀ + r / 2 * ∑ j, u j := by
    have e : ∀ j : Fin d, u j * (l₀ j + r / 2) = u j * l₀ j + r / 2 * u j :=
      fun j ↦ by ring
    calc dot u c = ∑ j, (u j * l₀ j + r / 2 * u j) :=
          Finset.sum_congr rfl fun j _ ↦ e j
      _ = dot u l₀ + r / 2 * ∑ j, u j := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
  -- `Σ uⱼ = S⁺ − S⁻` and `Σ |uⱼ| = S⁺ + S⁻`, so `u·c ≥ t − w/2`.
  have hsplit : ∑ j, u j = Sp - Sm := by
    rw [hSp, hSm, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ (max_zero_sub_max_neg_zero_eq_self _).symm
  have hnorm : ∑ j, |u j| = Sp + Sm := by
    rw [hSp, hSm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : 0 ≤ u j
    · rw [abs_of_nonneg hj, max_eq_right (neg_nonpos.mpr hj),
        max_eq_left hj, add_zero]
    · rw [abs_of_neg (lt_of_not_ge hj), max_eq_left (neg_nonneg.mpr
        (le_of_not_ge hj)), max_eq_right (le_of_not_ge hj), zero_add]
  -- `u·v = u·c + 2√d·w ≥ (t − w/2) + 2√d·w > t + w`.
  have hdotclow : t - w / 2 ≤ dot u c := by
    have hwr : w = r * (Sp + Sm) := by rw [hw, hnorm]
    rw [hsplit] at hdotc
    linarith [hlow]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have h2w : 2 * w ≤ 2 * Real.sqrt d * w :=
    mul_le_mul_of_nonneg_right (by linarith) hwpos.le
  have hvg : t + w < dot u v := by linarith [hvc, hdotclow, h2w, hwpos]
  -- Membership of `v` in the `4√d·r`-box about `c`.
  have hvmem : v ∈ centeredBox c (4 * Real.sqrt d * r) := by
    rw [centeredBox, Set.mem_univ_pi]
    intro j
    rw [Set.mem_Icc]
    have hsj : s j = 1 ∨ s j = -1 := by
      by_cases hj : 0 ≤ u j
      · exact Or.inl (if_pos hj)
      · exact Or.inr (if_neg hj)
    have h2r : (0 : ℝ) ≤ 2 * Real.sqrt d * r :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hr.le
    show c j - 4 * Real.sqrt d * r / 2 ≤ c j + 2 * Real.sqrt d * r * s j ∧
        c j + 2 * Real.sqrt d * r * s j ≤ c j + 4 * Real.sqrt d * r / 2
    rcases hsj with hsj | hsj <;> rw [hsj] <;> constructor <;> linarith
  -- The half-space is closed, so `closure (conv (⋃ B_l)) ⊆ {u· ≤ t+w}`
  -- while `u·v > t+w`.
  have hclosure : closure (convexHull ℝ (⋃ l ∈ I, dyadicBox l r)) ⊆
      {x : Fin d → ℝ | dot u x ≤ t + w} := by
    have hcl : IsClosed {x : Fin d → ℝ | dot u x ≤ t + w} := by
      have hset : {x : Fin d → ℝ | dot u x ≤ t + w} =
          dotLinear u ⁻¹' Set.Iic (t + w) := rfl
      rw [hset]
      exact isClosed_Iic.preimage
        (LinearMap.continuous_of_finiteDimensional (dotLinear u))
    exact closure_minimal hconvsub hcl
  exact ⟨v, hvmem, fun hvcl ↦ absurd (hclosure hvcl) (not_le_of_gt hvg)⟩

/-- **The boundary point `xᵢ ∈ ∂P ∩ B̃ᵢ` exists**: under the hypotheses of
`dilatedBox_notsubset_convexHull`, the dilated box `B̃_{l₀}` meets the
boundary of `P̂ = closure (conv (⋃ B_l))` — the witness `q ∉ P̂` and the
box center `c ∈ B_{l₀} ⊆ P̂` are joined by a segment inside `B̃_{l₀}`,
which crosses `∂P̂`.  (In the paper this is the point `x_i` used to
define `y_i ∈ [−u,u]^{d−1}` and to ensure `B_i ⊆ x_i + S`.) -/
theorem exists_mem_frontier_centeredBox {d : ℕ} (hd : 1 ≤ d)
    {A : Finset (Fin d → ℝ)} {δ : ℝ} (hδ : 0 < δ)
    (hcp : InDeltaConvexPosition A δ) {r : ℝ} (hr : 0 < r)
    {I : Finset (Fin d → ℝ)} {l₀ : Fin d → ℝ} (hl₀ : l₀ ∈ I)
    (hbig : ∀ l ∈ I, δ * A.card <
      ((A.filter fun a ↦ ∀ j, a j ∈ Set.Ico (l j) (l j + r)).card : ℝ)) :
    ∃ x ∈ frontier (closure (convexHull ℝ (⋃ l ∈ I, dyadicBox l r))),
      x ∈ centeredBox (fun j ↦ l₀ j + r / 2) (4 * Real.sqrt d * r) := by
  obtain ⟨q, hqB, hqP⟩ :=
    dilatedBox_notsubset_convexHull hd hδ hcp hr hl₀ hbig
  set P := closure (convexHull ℝ (⋃ l ∈ I, dyadicBox l r)) with hPdef
  set c : Fin d → ℝ := fun j ↦ l₀ j + r / 2 with hcdef
  -- The box center `c` lies in `B_{l₀}` (hence in `P`) and in `B̃_{l₀}`.
  have hcB : c ∈ dyadicBox l₀ r := by
    rw [dyadicBox, Set.mem_univ_pi]
    intro j
    simp only [hcdef]
    rw [Set.mem_Ico]
    constructor <;> linarith
  have hcP : c ∈ P :=
    subset_closure
      (subset_convexHull ℝ _ (Set.mem_iUnion₂.mpr ⟨l₀, hl₀, hcB⟩))
  have hcD : c ∈ centeredBox c (4 * Real.sqrt d * r) := by
    rw [centeredBox, Set.mem_univ_pi]
    intro j
    rw [Set.mem_Icc]
    have hs : (0 : ℝ) ≤ 4 * Real.sqrt d * r :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hr.le
    constructor <;> linarith
  have hconvD : Convex ℝ (centeredBox c (4 * Real.sqrt d * r)) := by
    rw [centeredBox]
    exact convex_pi fun i _ ↦ convex_Icc _ _
  exact exists_mem_frontier_inter isClosed_closure hconvD hcP hcD hqP hqB

/-!
## The concave upper envelope (the function `h` of the paper's proof)

In the large-width case of the paper's proof of Lemma 1 one considers the
upper envelope `h(y) = sup {t | (y, t) ∈ P}` of the convex hull `P` of the
boxes (after a rotation).  The following lemmas show that `h` is concave —
this is what allows the linear-approximation Lemma 2
(`convex_linear_approx`) to be applied later.
-/

/-- `Fin.snoc` commutes with linear combinations:
`snoc (a•y₁ + b•y₂) (a·t₁ + b·t₂) = a•snoc y₁ t₁ + b•snoc y₂ t₂`. -/
theorem snoc_smul_add_smul {k : ℕ} (y₁ y₂ : Fin k → ℝ) (a b t₁ t₂ : ℝ) :
    Fin.snoc (a • y₁ + b • y₂) (a * t₁ + b * t₂) =
      a • Fin.snoc y₁ t₁ + b • Fin.snoc y₂ t₂ := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [Fin.snoc_last, smul_eq_mul]
  | cast i => simp [Fin.snoc_castSucc, smul_eq_mul]

/-- The *upper envelope* of `P ⊆ ℝ^{k+1}` over the first `k` coordinates:
`h(y) = sup {t | snoc y t ∈ P}`, where `snoc y t` is `(y, t)` viewed as a
point of `ℝ^{k+1}`. -/
noncomputable def upperEnv {k : ℕ} (P : Set (Fin (k + 1) → ℝ))
    (y : Fin k → ℝ) : ℝ :=
  sSup {t : ℝ | Fin.snoc y t ∈ P}

/-- Fibers of a bounded `P ⊆ ℝ^{k+1}` over the first `k` coordinates are
bounded above. -/
theorem bddAbove_upperEnv_fiber {k : ℕ} {P : Set (Fin (k + 1) → ℝ)}
    (hPb : Bornology.IsBounded P) (y : Fin k → ℝ) :
    BddAbove {t : ℝ | Fin.snoc y t ∈ P} := by
  obtain ⟨R, hR⟩ := hPb.subset_ball 0
  refine ⟨R, fun t ht ↦ ?_⟩
  have ht' : Fin.snoc y t ∈ P := ht
  have hp : dist (Fin.snoc y t) 0 < R := Metric.mem_ball.mp (hR ht')
  have h1 : dist ((Fin.snoc y t : Fin (k + 1) → ℝ) (Fin.last k)) 0 ≤
      dist (Fin.snoc y t : Fin (k + 1) → ℝ) 0 :=
    dist_le_pi_dist (Fin.snoc (α := fun _ : Fin (k + 1) ↦ ℝ) y t) 0 (Fin.last k)
  rw [Fin.snoc_last, dist_zero_right, dist_zero_right, Real.norm_eq_abs] at h1
  rw [dist_zero_right] at hp
  linarith [le_abs_self t]

/-- Any point `(y, t)` of `P` lies below the upper envelope. -/
theorem le_upperEnv {k : ℕ} {P : Set (Fin (k + 1) → ℝ)}
    (hPb : Bornology.IsBounded P) {y : Fin k → ℝ} {t : ℝ}
    (ht : Fin.snoc y t ∈ P) : t ≤ upperEnv P y :=
  le_csSup (bddAbove_upperEnv_fiber hPb y) ht

/-- **The upper envelope is concave**: if `P ⊆ ℝ^{k+1}` is convex and
bounded and every `y ∈ D` lies below some point of `P`, then `h` is
concave on `D`.  This is the convexity property of the function `h` in the
paper's proof of Lemma 1. -/
theorem concaveOn_upperEnv {k : ℕ} {P : Set (Fin (k + 1) → ℝ)}
    (hPc : Convex ℝ P) (hPb : Bornology.IsBounded P)
    {D : Set (Fin k → ℝ)} (hD : Convex ℝ D)
    (hsub : ∀ y ∈ D, ∃ t : ℝ, Fin.snoc y t ∈ P) :
    ConcaveOn ℝ D (upperEnv P) := by
  refine ⟨hD, fun y₁ hy₁ y₂ hy₂ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  obtain ⟨t₁, ht₁⟩ := hsub _ hy₁
  obtain ⟨t₂, ht₂⟩ := hsub _ hy₂
  -- The fiber at `a•y₁+b•y₂` contains `a·t₁ + b·t₂` for `tᵢ` in the fibers.
  have hmem : ∀ t₁' ∈ {t : ℝ | Fin.snoc y₁ t ∈ P},
      ∀ t₂' ∈ {t : ℝ | Fin.snoc y₂ t ∈ P},
      a * t₁' + b * t₂' ∈ {t : ℝ | Fin.snoc (a • y₁ + b • y₂) t ∈ P} := by
    intro t₁' ht₁' t₂' ht₂'
    show Fin.snoc (a • y₁ + b • y₂) (a * t₁' + b * t₂') ∈ P
    rw [snoc_smul_add_smul]
    exact hPc ht₁' ht₂' ha hb hab
  have hle : ∀ t₁' ∈ {t : ℝ | Fin.snoc y₁ t ∈ P},
      ∀ t₂' ∈ {t : ℝ | Fin.snoc y₂ t ∈ P},
      a * t₁' + b * t₂' ≤ upperEnv P (a • y₁ + b • y₂) :=
    fun t₁' ht₁' t₂' ht₂' ↦ le_csSup (bddAbove_upperEnv_fiber hPb _)
      (hmem t₁' ht₁' t₂' ht₂')
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · -- `a = 0`, so `b = 1` and `a•y₁ + b•y₂ = y₂`.
    have hb1 : b = 1 := by linarith
    subst ha0
    subst hb1
    simp
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · -- `b = 0`, so `a = 1` and `a•y₁ + b•y₂ = y₁`.
    have ha1 : a = 1 := by linarith
    subst hb0
    subst ha1
    simp
  · -- `0 < a`, `0 < b`: bound each sup separately and combine.
    have hstep₁ : ∀ t₂' ∈ {t : ℝ | Fin.snoc y₂ t ∈ P},
        a * upperEnv P y₁ ≤ upperEnv P (a • y₁ + b • y₂) - b * t₂' := by
      intro t₂' ht₂'
      have h : upperEnv P y₁ ≤
          (upperEnv P (a • y₁ + b • y₂) - b * t₂') / a := by
        apply csSup_le ⟨t₁, ht₁⟩
        intro t₁' ht₁'
        rw [le_div_iff₀ hapos, mul_comm]
        linarith [hle t₁' ht₁' t₂' ht₂']
      rw [mul_comm]
      exact (le_div_iff₀ hapos).mp h
    have hstep₂ : b * upperEnv P y₂ ≤
        upperEnv P (a • y₁ + b • y₂) - a * upperEnv P y₁ := by
      have h : upperEnv P y₂ ≤
          (upperEnv P (a • y₁ + b • y₂) - a * upperEnv P y₁) / b := by
        apply csSup_le ⟨t₂, ht₂⟩
        intro t₂' ht₂'
        rw [le_div_iff₀ hbpos, mul_comm]
        linarith [hstep₁ t₂' ht₂']
      rw [mul_comm]
      exact (le_div_iff₀ hbpos).mp h
    linarith

/-- The upper envelope is continuous on an open convex domain where all
fibers are nonempty: concave functions on finite-dimensional open sets
are locally Lipschitz.  This supplies the measurability needed for the
slab `Ω'` in Lemma 1. -/
theorem continuousOn_upperEnv {k : ℕ} {P : Set (Fin (k + 1) → ℝ)}
    (hPc : Convex ℝ P) (hPb : Bornology.IsBounded P)
    {D : Set (Fin k → ℝ)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hsub : ∀ y ∈ D, ∃ t : ℝ, Fin.snoc y t ∈ P) :
    ContinuousOn (upperEnv P) D :=
  (concaveOn_upperEnv hPc hPb hDc hsub).continuousOn hDo

/-- Normalizing the upper envelope by a bound `M` produces the
`[0,1]`-valued convex function `H = 1 − h/M` appearing in the proof of
Lemma 1 (with `M = 2√d`), matching the hypotheses of
`convex_linear_approx`. -/
theorem convexOn_one_sub_upperEnv_div {k : ℕ} {P : Set (Fin (k + 1) → ℝ)}
    (hPc : Convex ℝ P) (hPb : Bornology.IsBounded P)
    {D : Set (Fin k → ℝ)} (hDc : Convex ℝ D)
    (hsub : ∀ y ∈ D, ∃ t : ℝ, Fin.snoc y t ∈ P) {M : ℝ} (hM : 0 < M)
    (hbdd : ∀ y ∈ D, upperEnv P y ∈ Set.Icc 0 M) :
    ConvexOn ℝ D (fun y ↦ 1 - upperEnv P y / M) ∧
    ∀ y ∈ D, 1 - upperEnv P y / M ∈ Set.Icc (0 : ℝ) 1 := by
  have hcv : ConcaveOn ℝ D (upperEnv P) :=
    concaveOn_upperEnv hPc hPb hDc hsub
  constructor
  · have h1 : ConvexOn ℝ D (fun y ↦ -(upperEnv P y / M)) := by
      have h2 : ConcaveOn ℝ D (fun y ↦ upperEnv P y / M) := by
        have e : (fun y ↦ upperEnv P y / M) = (M⁻¹ : ℝ) • upperEnv P := by
          ext y
          simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
          ring
        rw [e]
        exact hcv.smul (inv_nonneg.mpr hM.le)
      exact h2.neg
    have h3 : ConvexOn ℝ D (fun y ↦ -(upperEnv P y / M) + 1) :=
      h1.add_const 1
    have e : (fun y ↦ 1 - upperEnv P y / M) =
        (fun y ↦ -(upperEnv P y / M) + 1) := by
      ext y; ring
    rwa [e]
  · intro y hy
    have hb := Set.mem_Icc.mp (hbdd y hy)
    rw [Set.mem_Icc]
    constructor
    · have h4 : upperEnv P y / M ≤ 1 := by
        rw [div_le_one hM]; exact hb.2
      linarith
    · have h5 : 0 ≤ upperEnv P y / M := div_nonneg hb.1 hM.le
      linarith

/-!
## The dyadic-level pigeonhole (equation (2))

The next lemma is the counting argument of equation (2) in the paper's
proof of Lemma 1: weights in `(n/2^J, n]` are grouped into the `J` dyadic
shells `{n/2^{j+1} < w ≤ n/2^j}`, so one shell carries at least a `1/J`
fraction of the total mass.
-/

/-- **Dyadic-shell pigeonhole**: if `w : T → ℝ` satisfies
`n / 2^J < w i ≤ n` for all `i ∈ T`, then some dyadic shell
`{n/2^{j+1} < w ≤ n/2^j}` with `j < J` carries at least `(Σ_T w)/J` of the
mass. -/
theorem exists_dyadic_shell_mass {ι : Type*} [DecidableEq ι] {T : Finset ι}
    {w : ι → ℝ} {n : ℝ} (hn : 0 < n) {J : ℕ} (hJ : 0 < J)
    (hlo : ∀ i ∈ T, n / 2 ^ J < w i) (hhi : ∀ i ∈ T, w i ≤ n) :
    ∃ j < J, (∑ i ∈ T, w i) / J ≤
      ∑ i ∈ T.filter (fun i ↦ n / 2 ^ (j + 1) < w i ∧ w i ≤ n / 2 ^ j), w i := by
  classical
  -- The shell containing `w i` is indexed by `⌊log₂(n / w i)⌋`.
  set lvl : ι → ℕ := fun i ↦ Nat.log 2 ⌊n / w i⌋₊ with hlvl
  have hmem : ∀ i ∈ T,
      lvl i < J ∧ n / 2 ^ (lvl i + 1) < w i ∧ w i ≤ n / 2 ^ lvl i := by
    intro i hi
    have hwi : 0 < w i := by
      have h2J : (0 : ℝ) < n / 2 ^ J := div_pos hn (pow_pos (by norm_num) _)
      linarith [hlo i hi]
    have hnw : (1 : ℝ) ≤ n / w i :=
      (le_div_iff₀ hwi).mpr (by rw [one_mul]; exact hhi i hi)
    have hm : 0 < ⌊n / w i⌋₊ := (Nat.floor_pos (a := n / w i)).mpr hnw
    have hpow : 2 ^ lvl i ≤ ⌊n / w i⌋₊ := Nat.pow_log_le_self _ (by omega)
    have hpow2 : ⌊n / w i⌋₊ < 2 ^ (lvl i + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have hup : w i ≤ n / 2 ^ lvl i := by
      rw [le_div_iff₀ (pow_pos (by norm_num) _)]
      calc w i * 2 ^ lvl i ≤ w i * (n / w i) := by
            apply mul_le_mul_of_nonneg_left _ hwi.le
            have h1 : (2 : ℝ) ^ lvl i ≤ ⌊n / w i⌋₊ := by exact_mod_cast hpow
            exact h1.trans (Nat.floor_le (zero_le_one.trans hnw))
        _ = n := mul_div_cancel₀ n (ne_of_gt hwi)
    have hlow : n / 2 ^ (lvl i + 1) < w i := by
      rw [div_lt_iff₀ (pow_pos (by norm_num) _)]
      have h1 : n / w i < (2 : ℝ) ^ (lvl i + 1) :=
        (Nat.lt_floor_add_one _).trans_le
          (by exact_mod_cast Nat.succ_le_of_lt hpow2)
      have h2 : n < (2 : ℝ) ^ (lvl i + 1) * w i := (div_lt_iff₀ hwi).mp h1
      rwa [mul_comm] at h2
    have hlt : lvl i < J := by
      simp only [hlvl]
      have h2J : (⌊n / w i⌋₊ : ℝ) < 2 ^ J := by
        have h3 : n / w i < (2 : ℝ) ^ J := by
          have h4 : n < (2 : ℝ) ^ J * w i := by
            have := hlo i hi
            rw [div_lt_iff₀ (pow_pos (by norm_num) _)] at this
            rwa [mul_comm] at this
          exact (div_lt_iff₀ hwi).mpr h4
        exact lt_of_le_of_lt (Nat.floor_le (zero_le_one.trans hnw)) h3
      exact (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr
        (by exact_mod_cast h2J)
    exact ⟨hlt, hlow, hup⟩
  -- `T` is covered by the `J` shells.
  have hsub : T ⊆ (Finset.range J).biUnion
      (fun j ↦ T.filter fun i ↦ n / 2 ^ (j + 1) < w i ∧ w i ≤ n / 2 ^ j) := by
    intro i hi
    rw [Finset.mem_biUnion]
    exact ⟨lvl i, Finset.mem_range.mpr (hmem i hi).1,
      Finset.mem_filter.mpr ⟨hi, (hmem i hi).2⟩⟩
  -- The shells are pairwise disjoint.
  have hdisj : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint
      (fun j ↦ T.filter fun i ↦ n / 2 ^ (j + 1) < w i ∧ w i ≤ n / 2 ^ j) := by
    intro j₁ hj₁ j₂ hj₂ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    intro i hi₁ hi₂
    rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
    · have h2 : (2 : ℝ) ^ (j₁ + 1) ≤ 2 ^ j₂ :=
        pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hlt)
      have hn1 : n / 2 ^ j₂ ≤ n / 2 ^ (j₁ + 1) :=
        div_le_div_of_nonneg_left hn.le (pow_pos (by norm_num) _) h2
      linarith [hi₁.2.1, hi₂.2.2]
    · exact hne heq
    · have h2 : (2 : ℝ) ^ (j₂ + 1) ≤ 2 ^ j₁ :=
        pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hgt)
      have hn1 : n / 2 ^ j₁ ≤ n / 2 ^ (j₂ + 1) :=
        div_le_div_of_nonneg_left hn.le (pow_pos (by norm_num) _) h2
      linarith [hi₂.2.1, hi₁.2.2]
  -- Hence the masses in the shells sum to `Σ_T w`.
  have hsum : ∑ i ∈ T, w i = ∑ j ∈ Finset.range J,
      ∑ i ∈ T.filter (fun i ↦ n / 2 ^ (j + 1) < w i ∧ w i ≤ n / 2 ^ j),
        w i := by
    rw [← Finset.sum_biUnion hdisj]
    apply Finset.sum_congr _ (fun i _ ↦ rfl)
    exact le_antisymm hsub
      (Finset.biUnion_subset.mpr fun j _ ↦ Finset.filter_subset _ T)
  -- Some shell therefore carries at least the average mass `(Σ w)/J`.
  have hJR : (J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hJ)
  obtain ⟨j, hj, hjm⟩ :
      ∃ j ∈ Finset.range J, (∑ i ∈ T, w i) / J ≤
        ∑ i ∈ T.filter (fun i ↦ n / 2 ^ (j + 1) < w i ∧ w i ≤ n / 2 ^ j),
          w i := by
    apply Finset.exists_le_of_sum_le
      (Finset.nonempty_range_iff.mpr (ne_of_gt hJ))
    refine le_of_eq ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ hJR, hsum]
  exact ⟨j, Finset.mem_range.mp hj, hjm⟩

/-!
## The dyadic box decomposition

The next block formalizes the opening move in the paper's proof of
Lemma 1: the finite set `A ⊆ [-1,1]^d` is decomposed into dyadic
`2^{-k}`-boxes, the boxes with fewer than `|A|/2^{d(k+2)+2}` points are
discarded, and the remaining boxes are grouped by dyadic mass.  At the
scale `k` the surviving boxes still carry a `≥ 3/(4(d(k+2)+2))` fraction
of `A`, and `exists_dyadic_shell_mass` then selects a mass level
`μ = 2^{-j}` at which the total mass is `≥ |A|/(d(k+2)+2)`
(compare equation (2) of the paper).
-/

/-- Membership in a dyadic `1/N`-box `∏ᵢ [zᵢ/N, (zᵢ+1)/N)` is equivalent
to the coordinatewise floor condition `⌊N·aᵢ⌋ = zᵢ`: the combinatorial
fact behind the dyadic decomposition in the proof of Lemma 1. -/
theorem mem_dyadic_box_iff_floor {d : ℕ} {N : ℕ} (hN : 0 < N)
    (a : Fin d → ℝ) (z : Fin d → ℤ) :
    (∀ i, a i ∈ Set.Ico ((z i : ℝ) / N) (((z i : ℝ) + 1) / N)) ↔
      (fun i ↦ ⌊(N : ℝ) * a i⌋) = z := by
  rw [funext_iff]
  refine forall_congr' fun i ↦ ?_
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [Set.mem_Ico]
  constructor
  · rintro ⟨hlo, hhi⟩
    have e1 : (z i : ℝ) ≤ (N : ℝ) * a i := by
      have h := (div_le_iff₀ hNR).mp hlo; linarith
    have e2 : (N : ℝ) * a i < (z i : ℝ) + 1 := by
      have h := (lt_div_iff₀ hNR).mp hhi; linarith
    exact le_antisymm (Int.floor_le_iff.mpr e2) (Int.le_floor.mpr e1)
  · intro h
    rw [← h]
    have hle : (⌊(N : ℝ) * a i⌋ : ℝ) ≤ (N : ℝ) * a i := Int.floor_le _
    have hlt : (N : ℝ) * a i < (⌊(N : ℝ) * a i⌋ : ℝ) + 1 :=
      Int.lt_floor_add_one _
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hNR]; linarith
    · rw [lt_div_iff₀ hNR]; linarith

/-- **Dyadic box decomposition and scale selection** (the first step in
the proof of Lemma 1, culminating in the mass bound (2)): for a finite
`A ⊆ [-1,1]^d` and scale `k`, the dyadic `2^{-k}`-boxes carrying more
than `|A|/2^{d(k+2)+2}` points are grouped by dyadic mass.  There is a
mass level `j < d(k+2)+2` and a family `I` of box corners such that

* every `l ∈ I` is a corner `z/2^k` of a `2^{-k}`-box inside `[-1,1]^d`
  whose `A`-mass lies in the dyadic shell
  `(|A|/2^{j+1}, |A|/2^j]` — in particular it carries `> δ|A|` points
  once `δ < 2^{-(d(k+2)+2)}`;
* distinct corners give disjoint `dyadicBox`es;
* the selected boxes cover at least `3|A|/(4(d(k+2)+2))` points of `A`;
* `|I| ≤ (3·2^k)^d`. -/
theorem exists_dyadic_box_scale {d : ℕ} (A : Finset (Fin d → ℝ))
    (hA : A.Nonempty) (hA1 : ∀ a ∈ A, ∀ i, a i ∈ Set.Icc (-1) 1) (k : ℕ) :
    ∃ j : ℕ, j < d * (k + 2) + 2 ∧ ∃ I : Finset (Fin d → ℝ),
      (∀ l ∈ I, ∃ z : Fin d → ℤ, (∀ i, l i = (z i : ℝ) / 2 ^ k) ∧
        (∀ i, l i ∈ Set.Icc (-1) 1) ∧
        (A.card : ℝ) / 2 ^ (j + 1) <
          ((A.filter fun a ↦ ∀ i, a i ∈ Set.Ico (l i)
            (l i + ((2 : ℝ) ^ k)⁻¹)).card : ℝ) ∧
        ((A.filter fun a ↦ ∀ i, a i ∈ Set.Ico (l i)
            (l i + ((2 : ℝ) ^ k)⁻¹)).card : ℝ) ≤
          (A.card : ℝ) / 2 ^ j) ∧
      ((I : Set (Fin d → ℝ)).PairwiseDisjoint
        fun l ↦ dyadicBox l ((2 : ℝ) ^ k)⁻¹) ∧
      (3 / 4 * (A.card : ℝ) / (d * (k + 2) + 2)) ≤
        (((I.biUnion fun l ↦ A.filter fun a ↦
          ∀ i, a i ∈ Set.Ico (l i) (l i + ((2 : ℝ) ^ k)⁻¹))).card : ℝ) ∧
      I.card ≤ (3 * 2 ^ k) ^ d ∧
      (1 : ℝ) / 2 ^ (d * (k + 2) + 2) ≤ 1 / 2 ^ (j + 1) := by
  classical
  have hcardpos : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hA
  -- `N = 2^k` boxes per coordinate and `r = N⁻¹` the box width.
  set N : ℕ := 2 ^ k with hNdef
  have hNpos : 0 < N := pow_pos (by norm_num) _
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hNcast : ((N : ℕ) : ℝ) = (2 : ℝ) ^ k := by
    rw [hNdef]; norm_cast
  set r : ℝ := ((2 : ℝ) ^ k)⁻¹ with hrdef
  have hrN : r = (N : ℝ)⁻¹ := by rw [hrdef, hNcast]
  -- The box index `idx a` of a point, and the index set `T`.
  set idx : (Fin d → ℝ) → Fin d → ℤ := fun a i ↦ ⌊(N : ℝ) * a i⌋ with hidx
  set T : Finset (Fin d → ℤ) :=
    Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(N : ℤ)) (N : ℤ) with hTdef
  have hTcard : T.card = (2 * N + 1) ^ d := by
    rw [hTdef, Fintype.card_piFinset]
    have he : ∀ i : Fin d,
        (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := fun i ↦ by
      rw [Int.card_Icc]
      have h : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [h]
      exact Int.toNat_natCast _
    rw [Finset.prod_congr rfl fun i _ ↦ he i, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hTcard3 : T.card ≤ (3 * N) ^ d := by
    rw [hTcard]
    exact Nat.pow_le_pow_left (by omega) _
  have hidxT : ∀ a ∈ A, idx a ∈ T := by
    intro a ha
    rw [hTdef, Fintype.mem_piFinset]
    intro i
    have hai := Set.mem_Icc.mp (hA1 a ha i)
    have h1 : ((-(N : ℤ)) : ℝ) ≤ (N : ℝ) * a i := by
      have hNN : ((-(N : ℤ)) : ℝ) = -(N : ℝ) := by push_cast; ring
      rw [hNN]
      nlinarith [hai.1, hNR.le]
    have h2 : (N : ℝ) * a i ≤ ((N : ℤ) : ℝ) := by
      have hNN : ((N : ℤ) : ℝ) = (N : ℝ) := by push_cast; ring
      rw [hNN]
      nlinarith [hai.2, hNR.le]
    rw [Finset.mem_Icc]
    constructor
    · exact Int.le_floor.mpr (by
        rw [Int.cast_neg, Int.cast_natCast]
        nlinarith [hai.1, hNR.le])
    · exact Int.floor_le_iff.mpr (lt_of_le_of_lt h2 (lt_add_one _))
  -- The `Ico` boxes at `r = 1/N` and the fiber filter coincide.
  have hIco : ∀ (z : ℤ) (x : ℝ),
      x ∈ Set.Ico ((z : ℝ) / N) ((z : ℝ) / N + r) ↔
        x ∈ Set.Ico ((z : ℝ) / N) (((z : ℝ) + 1) / N) := by
    intro z x
    have e : (z : ℝ) / N + r = ((z : ℝ) + 1) / N := by
      rw [hrN, inv_eq_one_div, ← add_div]
    rw [e]
  have hfilter : ∀ z : Fin d → ℤ,
      (A.filter fun a ↦ ∀ i, a i ∈ Set.Ico ((z i : ℝ) / N)
          ((z i : ℝ) / N + r)) =
      A.filter fun a ↦ idx a = z := by
    intro z
    apply Finset.filter_congr
    intro a _
    rw [show (∀ i, a i ∈ Set.Ico ((z i : ℝ) / N) ((z i : ℝ) / N + r)) ↔
        ∀ i, a i ∈ Set.Ico ((z i : ℝ) / N) (((z i : ℝ) + 1) / N) from
      forall_congr' fun i ↦ hIco (z i) (a i)]
    exact mem_dyadic_box_iff_floor hNpos a z
  set w : (Fin d → ℤ) → ℝ := fun z ↦
    ((A.filter fun a ↦ idx a = z).card : ℝ) with hwdef
  have hsumT : ∑ z ∈ T, w z = (A.card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := A) (t := T) (f := idx)
      hidxT
    simp only [hwdef]
    rw [← Nat.cast_sum]
    exact_mod_cast h.symm
  set J : ℕ := d * (k + 2) + 2 with hJdef
  have hJpos : 0 < J := by omega
  have hJR : (0 : ℝ) < (J : ℝ) := Nat.cast_pos.mpr hJpos
  -- Discarding the low-mass indices loses at most `|A|/4`.
  have hdiscard :
      ∑ z ∈ T.filter (fun z ↦ ¬ (A.card : ℝ) / 2 ^ J < w z), w z ≤
        (A.card : ℝ) / 4 := by
    have hle : ∀ z ∈ T.filter (fun z ↦ ¬ (A.card : ℝ) / 2 ^ J < w z),
        w z ≤ (A.card : ℝ) / 2 ^ J := fun z hz ↦
      not_lt.mp (Finset.mem_filter.mp hz).2
    calc ∑ z ∈ T.filter (fun z ↦ ¬ (A.card : ℝ) / 2 ^ J < w z), w z
        ≤ ∑ _z ∈ T.filter (fun z ↦ ¬ (A.card : ℝ) / 2 ^ J < w z),
            (A.card : ℝ) / 2 ^ J := Finset.sum_le_sum hle
      _ = (T.filter (fun z ↦ ¬ (A.card : ℝ) / 2 ^ J < w z)).card *
            ((A.card : ℝ) / 2 ^ J) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 * N : ℝ) ^ d * ((A.card : ℝ) / 2 ^ J) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hsub : (T.filter (fun z ↦ ¬ (A.card : ℝ) / 2 ^ J < w z)).card
              ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
          exact_mod_cast le_trans hsub hTcard3
      _ ≤ (A.card : ℝ) / 4 := by
          have hpow : (3 * N : ℝ) ^ d / (2 : ℝ) ^ J ≤ 1 / 4 := by
            rw [div_le_iff₀ (pow_pos (by norm_num) _)]
            have h3 : (3 : ℝ) ^ d ≤ 4 ^ d := by gcongr; norm_num
            have h2J : (2 : ℝ) ^ J = ((2 : ℝ) ^ k) ^ d * (4 : ℝ) ^ (d + 1) := by
              rw [hJdef,
                show d * (k + 2) + 2 = k * d + 2 * (d + 1) from by ring,
                pow_add, pow_mul, pow_mul,
                show (2 : ℝ) ^ 2 = 4 from by norm_num]
            rw [h2J, hNcast, mul_pow, pow_succ]
            rw [show (1 / 4 : ℝ) * (((2 : ℝ) ^ k) ^ d * ((4 : ℝ) ^ d * 4)) =
              (4 : ℝ) ^ d * ((2 : ℝ) ^ k) ^ d from by ring]
            exact mul_le_mul_of_nonneg_right h3 (pow_nonneg (by norm_num) _)
          have e : (3 * N : ℝ) ^ d * ((A.card : ℝ) / 2 ^ J) =
              (A.card : ℝ) * ((3 * N : ℝ) ^ d / 2 ^ J) := by ring
          rw [e]
          calc (A.card : ℝ) * ((3 * N : ℝ) ^ d / 2 ^ J)
              ≤ (A.card : ℝ) * (1 / 4) :=
                mul_le_mul_of_nonneg_left hpow hcardpos.le
            _ = (A.card : ℝ) / 4 := by ring
  -- Hence the surviving indices still carry `3|A|/4` of the mass.
  have hsurv : (3 / 4 : ℝ) * A.card ≤
      ∑ z ∈ T.filter (fun z ↦ (A.card : ℝ) / 2 ^ J < w z), w z := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := T)
      (p := fun z ↦ (A.card : ℝ) / 2 ^ J < w z) (f := w)
    rw [hsumT] at hsplit
    linarith [hdiscard]
  -- `exists_dyadic_shell_mass` picks the dyadic mass level `j`.
  obtain ⟨j, hjJ, hjm⟩ := exists_dyadic_shell_mass
    (T := T.filter (fun z ↦ (A.card : ℝ) / 2 ^ J < w z))
    (w := w) (n := (A.card : ℝ)) hcardpos hJpos
    (fun z hz ↦ (Finset.mem_filter.mp hz).2)
    (fun z _ ↦ by
      have hsub := Finset.card_le_card
        (Finset.filter_subset _ A : (A.filter fun a ↦ idx a = z) ⊆ A)
      show ((A.filter fun a ↦ idx a = z).card : ℝ) ≤ (A.card : ℝ)
      exact_mod_cast hsub)
  -- The selected index set `S` and its image `I` under the corner map.
  set S : Finset (Fin d → ℤ) :=
    (T.filter fun z ↦ (A.card : ℝ) / 2 ^ J < w z).filter
      (fun z ↦ (A.card : ℝ) / 2 ^ (j + 1) < w z ∧
        w z ≤ (A.card : ℝ) / 2 ^ j) with hSdef
  set I : Finset (Fin d → ℝ) :=
    S.image fun z i ↦ (z i : ℝ) / N with hIdef
  have hSsub : S ⊆ T.filter (fun z ↦ (A.card : ℝ) / 2 ^ J < w z) :=
    fun z hz ↦ Finset.mem_of_mem_filter _ hz
  have hper : ∀ l ∈ I, ∃ z : Fin d → ℤ,
      (∀ i, l i = (z i : ℝ) / 2 ^ k) ∧ (∀ i, l i ∈ Set.Icc (-1) 1) ∧
      (A.card : ℝ) / 2 ^ (j + 1) <
        ((A.filter fun a ↦ ∀ i, a i ∈ Set.Ico (l i) (l i + r)).card : ℝ) ∧
      ((A.filter fun a ↦ ∀ i, a i ∈ Set.Ico (l i) (l i + r)).card : ℝ) ≤
        (A.card : ℝ) / 2 ^ j := by
    intro l hl
    rw [hIdef] at hl
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hl
    have hqz : (A.card : ℝ) / 2 ^ (j + 1) < w z ∧
        w z ≤ (A.card : ℝ) / 2 ^ j := (Finset.mem_filter.mp hzS).2
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    · intro i
      show (z i : ℝ) / N = (z i : ℝ) / 2 ^ k
      rw [hNcast]
    · intro i
      show (z i : ℝ) / N ∈ Set.Icc (-1) 1
      have hzT : z ∈ T :=
        Finset.mem_of_mem_filter _ (Finset.mem_of_mem_filter _ hzS)
      rw [hTdef] at hzT
      have hzi := (Fintype.mem_piFinset.mp hzT) i
      rw [Finset.mem_Icc] at hzi
      rw [Set.mem_Icc]
      constructor
      · rw [le_div_iff₀ hNR]
        have e : (-1 : ℝ) * N = (-(N : ℤ) : ℝ) := by push_cast; ring
        rw [e]
        exact_mod_cast hzi.1
      · rw [div_le_iff₀ hNR]
        have e : (1 : ℝ) * N = ((N : ℤ) : ℝ) := by push_cast; ring
        rw [e]
        exact_mod_cast hzi.2
    · show (A.card : ℝ) / 2 ^ (j + 1) <
        ((A.filter fun a ↦ ∀ i, a i ∈ Set.Ico ((z i : ℝ) / N)
          ((z i : ℝ) / N + r)).card : ℝ)
      rw [hfilter z]
      exact hqz.1
    · show ((A.filter fun a ↦ ∀ i, a i ∈ Set.Ico ((z i : ℝ) / N)
          ((z i : ℝ) / N + r)).card : ℝ) ≤ (A.card : ℝ) / 2 ^ j
      rw [hfilter z]
      exact hqz.2
  -- Distinct corners give disjoint boxes.
  have hdisj : ((I : Set (Fin d → ℝ)).PairwiseDisjoint
      fun l ↦ dyadicBox l r) := by
    intro l hl l' hl' hne
    rw [hIdef] at hl hl'
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hl)
    obtain ⟨z', hz'S, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hl')
    have hnezz : z ≠ z' := fun h ↦ hne (by rw [h])
    show Disjoint (dyadicBox (fun i ↦ (z i : ℝ) / N) r)
      (dyadicBox (fun i ↦ (z' i : ℝ) / N) r)
    rw [Set.disjoint_left]
    intro a ha ha'
    simp only [dyadicBox, Set.mem_univ_pi] at ha ha'
    have e1 : (fun i ↦ ⌊(N : ℝ) * a i⌋) = z :=
      (mem_dyadic_box_iff_floor hNpos a z).mp fun i ↦
        (hIco (z i) (a i)).mp (ha i)
    have e2 : (fun i ↦ ⌊(N : ℝ) * a i⌋) = z' :=
      (mem_dyadic_box_iff_floor hNpos a z').mp fun i ↦
        (hIco (z' i) (a i)).mp (ha' i)
    exact hnezz (e1.symm.trans e2)
  -- The selected boxes cover at least `(3/4)|A|/J` points of `A`.
  have hcover : (3 / 4 : ℝ) * A.card / J ≤
      (((I.biUnion fun l ↦ A.filter fun a ↦
        ∀ i, a i ∈ Set.Ico (l i) (l i + r))).card : ℝ) := by
    have hkey : I.biUnion (fun l : Fin d → ℝ ↦ A.filter fun a ↦
          ∀ i, a i ∈ Set.Ico (l i) (l i + r)) =
        S.biUnion (fun z ↦ A.filter fun a ↦ idx a = z) := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨l, hl, haA, hbox⟩
        rw [hIdef] at hl
        obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hl
        exact ⟨z, hzS, haA,
          (mem_dyadic_box_iff_floor hNpos a z).mp fun i ↦
            (hIco (z i) (a i)).mp (hbox i)⟩
      · rintro ⟨z, hzS, haA, hfl⟩
        exact ⟨(fun i ↦ (z i : ℝ) / N),
          by rw [hIdef]; exact Finset.mem_image.mpr ⟨z, hzS, rfl⟩,
          haA, fun i ↦ (hIco (z i) (a i)).mpr
            ((mem_dyadic_box_iff_floor hNpos a z).mpr hfl i)⟩
    rw [hkey]
    have hcardbi : (S.biUnion fun z ↦ A.filter fun a ↦ idx a = z).card =
        ∑ z ∈ S, (A.filter fun a ↦ idx a = z).card := by
      apply Finset.card_biUnion
      intro z hz z' hz' hne
      show Disjoint (A.filter fun a ↦ idx a = z)
        (A.filter fun a ↦ idx a = z')
      rw [Finset.disjoint_left]
      intro a ha ha'
      rw [Finset.mem_filter] at ha ha'
      exact hne (ha.2.symm.trans ha'.2)
    rw [hcardbi, Nat.cast_sum]
    calc (3 / 4 : ℝ) * A.card / J
        ≤ (∑ z ∈ T.filter (fun z ↦ (A.card : ℝ) / 2 ^ J < w z), w z) / J :=
          div_le_div_of_nonneg_right hsurv hJR.le
      _ ≤ ∑ z ∈ S, w z := hjm
      _ = ∑ z ∈ S, ((A.filter fun a ↦ idx a = z).card : ℝ) :=
          Finset.sum_congr rfl fun z _ ↦ rfl
  have hIcard : I.card ≤ (3 * N) ^ d := by
    calc I.card ≤ S.card := Finset.card_image_le
      _ ≤ (T.filter (fun z ↦ (A.card : ℝ) / 2 ^ J < w z)).card :=
          Finset.card_le_card hSsub
      _ ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ (3 * N) ^ d := hTcard3
  have hμ : (1 : ℝ) / 2 ^ J ≤ 1 / 2 ^ (j + 1) := by
    apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hcover' : (3 / 4 * (A.card : ℝ) / (d * (k + 2) + 2)) ≤
      (((I.biUnion fun l ↦ A.filter fun a ↦
        ∀ i, a i ∈ Set.Ico (l i) (l i + r))).card : ℝ) := by
    have e : (d : ℝ) * ((k : ℝ) + 2) + 2 = (J : ℝ) := by
      rw [hJdef]; push_cast; ring
    rw [e]
    exact hcover
  exact ⟨j, hjJ, I, hper, hdisj, hcover', hIcard, hμ⟩

/-- **Lemma 1 in dimension `1` is vacuous**: a nonempty `A ⊆ ℝ` in
`δ`-convex position needs `δ ≥ 1/2`.  Indeed, the half-space witnessing
`a ∈ A` is `{x : t ≤ u·x}`; if `u > 0` it contains every `x ≥ a`, so `a` is
among the `δ|A|` largest points, and if `u < 0` it contains every `x ≤ a`,
so `a` is among the `δ|A|` smallest points (the case `u = 0` forces
`δ ≥ 1`).  The `δ|A|` largest and `δ|A|` smallest points together number
at most `2δ|A| < |A|`, so they cannot cover `A`. -/
theorem not_inDeltaConvexPosition_one {A : Finset (Fin 1 → ℝ)} {δ : ℝ}
    (hδ : δ < 1 / 2) (hA : A.Nonempty) : ¬ InDeltaConvexPosition A δ := by
  classical
  intro hcp
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨u₀, t₀, ht₀, hcard₀⟩ := hcp a₀ ha₀
  have hcardpos : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨a₀, ha₀⟩
  have hδpos : (0 : ℝ) < δ := by
    have hmem₀ : a₀ ∈ A.filter (fun x ↦ t₀ ≤ dot u₀ x) :=
      Finset.mem_filter.mpr ⟨ha₀, ht₀⟩
    have h1 : (1 : ℝ) ≤ ((A.filter fun x ↦ t₀ ≤ dot u₀ x).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨a₀, hmem₀⟩
    exact pos_of_mul_pos_left
      (zero_lt_one.trans_le (h1.trans hcard₀)) (Nat.cast_nonneg _)
  -- `T`: points among the `δ|A|` largest; `B`: among the `δ|A|` smallest.
  set T := A.filter fun a ↦
    ((A.filter fun x ↦ a 0 ≤ x 0).card : ℝ) ≤ δ * A.card with hTdef
  set B := A.filter fun a ↦
    ((A.filter fun x ↦ x 0 ≤ a 0).card : ℝ) ≤ δ * A.card with hBdef
  have hcover : A ⊆ T ∪ B := by
    intro a ha
    obtain ⟨u, t, ht, hcard⟩ := hcp a ha
    have hdot : ∀ x : Fin 1 → ℝ, dot u x = u 0 * x 0 := fun x ↦ by
      rw [dot]; simp only [Fin.sum_univ_one]
    rcases lt_trichotomy (u 0) 0 with hu | hu | hu
    · -- `u < 0`: `{x ∈ A : x₀ ≤ a₀}` is inside the small half-space.
      apply Finset.mem_union_right
      rw [hBdef, Finset.mem_filter]
      refine ⟨ha, ?_⟩
      have hsub : A.filter (fun x ↦ x 0 ≤ a 0) ⊆
          A.filter (fun x ↦ t ≤ dot u x) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        have hle : u 0 * a 0 ≤ u 0 * x 0 := mul_le_mul_of_nonpos_left hx.2 hu.le
        rw [← hdot a, ← hdot x] at hle
        exact le_trans ht hle
      exact le_trans (by exact_mod_cast Finset.card_le_card hsub) hcard
    · -- `u = 0`: the half-space contains all of `A`, forcing `δ ≥ 1`.
      exfalso
      have hfull : A.filter (fun x ↦ t ≤ dot u x) = A := by
        apply Finset.filter_eq_self.mpr
        intro x _
        rw [hdot, hu, zero_mul]
        rwa [hdot, hu, zero_mul] at ht
      rw [hfull] at hcard
      have h1 : (1 : ℝ) ≤ δ :=
        le_of_mul_le_mul_right
          (show (1 : ℝ) * A.card ≤ δ * A.card by rwa [one_mul]) hcardpos
      linarith
    · -- `u > 0`: `{x ∈ A : x₀ ≥ a₀}` is inside the small half-space.
      apply Finset.mem_union_left
      rw [hTdef, Finset.mem_filter]
      refine ⟨ha, ?_⟩
      have hsub : A.filter (fun x ↦ a 0 ≤ x 0) ⊆
          A.filter (fun x ↦ t ≤ dot u x) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        have hle : u 0 * a 0 ≤ u 0 * x 0 := mul_le_mul_of_nonneg_left hx.2 hu.le
        rw [← hdot a, ← hdot x] at hle
        exact le_trans ht hle
      exact le_trans (by exact_mod_cast Finset.card_le_card hsub) hcard
  have hT : (T.card : ℝ) ≤ δ * A.card := by
    rcases T.eq_empty_or_nonempty with hT' | hT'
    · rw [hT']
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · obtain ⟨a₁, ha₁, hmin⟩ := Finset.exists_min_image T (fun x ↦ x 0) hT'
      have ha₁' := Finset.mem_filter.mp (hTdef ▸ ha₁)
      have hsub : T ⊆ A.filter (fun x ↦ a₁ 0 ≤ x 0) := by
        intro x hx
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp (hTdef ▸ hx)).1, hmin x hx⟩
      exact le_trans (by exact_mod_cast Finset.card_le_card hsub) ha₁'.2
  have hB : (B.card : ℝ) ≤ δ * A.card := by
    rcases B.eq_empty_or_nonempty with hB' | hB'
    · rw [hB']
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · obtain ⟨a₁, ha₁, hmax⟩ := Finset.exists_max_image B (fun x ↦ x 0) hB'
      have ha₁' := Finset.mem_filter.mp (hBdef ▸ ha₁)
      have hsub : B ⊆ A.filter (fun x ↦ x 0 ≤ a₁ 0) := by
        intro x hx
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp (hBdef ▸ hx)).1, hmax x hx⟩
      exact le_trans (by exact_mod_cast Finset.card_le_card hsub) ha₁'.2
  -- `|A| ≤ |T| + |B| ≤ 2δ|A|` forces `δ ≥ 1/2`, a contradiction.
  have hcardle : (A.card : ℝ) ≤ T.card + B.card := by
    exact_mod_cast le_trans (Finset.card_le_card hcover) (Finset.card_union_le T B)
  have h2δ : (0 : ℝ) < 1 - 2 * δ := by linarith
  have := mul_pos h2δ hcardpos
  nlinarith

/-- **The geometric core of Lemma 1**: the genuinely difficult case of a
*finite-volume* `Ω` in which `A` is not already confined to a thin set
(`vol(conv A) > δ·vol Ω`).  The complementary cases are handled by
`DensityIncrementGoal.of_volume_eq_top` (`vol Ω = ∞`, take `Ω' = Ω`) and
`DensityIncrementGoal.of_convexHull_volume_le` (`vol conv A ≤ δ·vol Ω`,
take `Ω' = conv A`).

This is the case where the paper's machinery is needed: dyadic `r`-boxes
(`r ~ δ^{1/d}`), the observation that boxes containing `> δ|A|` points are
in "rough convex position" (equation (3)), the width/inradius dichotomy for
`P = conv(⋃ Bᵢ)`, the averaging over `SO(d)` putting `~u^{d−1}` of the
boundary points `xᵢ` above the cap `[−u,u]^{d−1}`, the concave envelope `h`,
an application of `convex_linear_approx` (Lemma 2), and the volume estimate
of the resulting graph-slab `Ω'`. -/
theorem density_increment_core (d : ℕ) (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ M : ℕ, ∀ (Ω : Set (Fin d → ℝ)) (A : Finset (Fin d → ℝ)),
        Convex ℝ Ω → (interior Ω).Nonempty →
        (∀ a ∈ A, (a : Fin d → ℝ) ∈ Ω) →
        InDeltaConvexPosition A δ → M ≤ A.card →
        volume Ω ≠ ⊤ →
        ENNReal.ofReal δ * volume Ω <
          volume (convexHull ℝ (A : Set (Fin d → ℝ))) →
        DensityIncrementGoal d δ τ ε Ω A := by
  sorry

/-- **Lemma 1 (density increment)**.  For `d ≥ 1` and `ε > 0` there exist
`τ ∈ (0,1)` and `δ₀ > 0` such that for every `δ ∈ (0, δ₀)` the following
holds.  Let `Ω ⊂ ℝ^d` be a convex body with nonempty interior and let
`A ⊂ Ω` be a finite set in δ-convex position, sufficiently large in `δ`.
Then for some `η ∈ [δ, δ^τ]` there is a convex `Ω' ⊂ Ω` with
`Vol(Ω') ≤ η·Vol(Ω)` and `|A ∩ Ω'| ≥ η^{(d−1)/(d+1)+ε}|A|`. -/
theorem density_increment (d : ℕ) (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ M : ℕ, ∀ (Ω : Set (Fin d → ℝ)) (A : Finset (Fin d → ℝ)),
        Convex ℝ Ω → (interior Ω).Nonempty →
        (∀ a ∈ A, (a : Fin d → ℝ) ∈ Ω) →
        InDeltaConvexPosition A δ → M ≤ A.card →
        ∃ η : ℝ, δ ≤ η ∧ η ≤ δ ^ τ ∧ ∃ Ω' : Set (Fin d → ℝ),
          Convex ℝ Ω' ∧ Ω' ⊆ Ω ∧
          volume Ω' ≤ ENNReal.ofReal η * volume Ω ∧
          η ^ ((d - 1 : ℝ) / (d + 1) + ε) * A.card ≤
            ((A.filter fun a ↦ (a : Fin d → ℝ) ∈ Ω').card : ℝ) := by
  rcases eq_or_lt_of_le hd with rfl | hd2
  · -- `d = 1`: `InDeltaConvexPosition A δ` is impossible for `δ < 1/2`
    -- (`not_inDeltaConvexPosition_one`), so the implication is vacuous.
    refine ⟨1 / 2, by norm_num, by norm_num, 1 / 2, by norm_num,
      fun δ _hδ hδ' ↦ ⟨1, fun _Ω A _ _ _ hcp hM ↦ ?_⟩⟩
    exact absurd hcp (not_inDeltaConvexPosition_one hδ'
      (Finset.card_pos.mp (by omega)))
  · obtain ⟨τ, hτ0, hτ1, δ₀, hδ₀, H⟩ := density_increment_core d hd2 hε
    -- Shrink `δ₀` to `≤ 1` so that `δ < 1` and the interval `[δ, δ^τ]` is
    -- nonempty (for `δ ≥ 1` it would be empty).
    refine ⟨τ, hτ0, hτ1, min δ₀ 1, lt_min hδ₀ zero_lt_one, fun δ hδ hδ' ↦ ?_⟩
    have hδ1 : δ < 1 := lt_of_lt_of_le hδ' (min_le_right _ _)
    obtain ⟨M, HM⟩ := H δ hδ (lt_of_lt_of_le hδ' (min_le_left _ _))
    -- `M ≥ 1` additionally ensures `A ≠ ∅`, which is harmless.
    refine ⟨max M 1, fun Ω A hconv _hint hsub hcp hM ↦ ?_⟩
    have hM' : M ≤ A.card := le_trans (le_max_left M 1) hM
    show DensityIncrementGoal d δ τ ε Ω A
    by_cases hvol : volume Ω = ⊤
    · -- `vol Ω = ∞`: `Ω' = Ω` and `η = δ^τ` work.
      exact DensityIncrementGoal.of_volume_eq_top hconv hsub hvol
        (le_rpow_self_of_le_one hδ hδ1.le hτ1.le) le_rfl
        (Real.rpow_pos_of_pos hδ _) (rpow_le_one_of_pos hδ hδ1.le hτ0.le)
        (density_exponent_nonneg hd hε.le)
    · by_cases hhull : volume (convexHull ℝ (A : Set (Fin d → ℝ))) ≤
          ENNReal.ofReal δ * volume Ω
      · -- `conv A` already thin: `Ω' = conv A` and `η = δ` work.
        exact DensityIncrementGoal.of_convexHull_volume_le hconv hsub hhull
          le_rfl (le_rpow_self_of_le_one hδ hδ1.le hτ1.le) hδ hδ1.le
          (density_exponent_nonneg hd hε.le)
      · push Not at hhull
        exact HM Ω A hconv _hint hsub hcp hM' hvol hhull

end Nonaveraging
