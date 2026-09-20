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
  have hc0 : (0 : ℝ) < c := by
    have h2 : (0 : ℝ) < 2 * (d : ℝ) / m := by positivity
    linarith
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · -- **Case `d = 1`**: the domain `Fin 0 → ℝ` is a singleton; take `L ≡ H`.
    have hd1 : d = 1 := by omega
    subst hd1
    obtain ⟨v, hv⟩ := hIne
    refine ⟨v, hv, H (fun _ ↦ 0), fun _ ↦ 0, fun x _ ↦ ?_⟩
    have hx : x = fun _ ↦ (0 : ℝ) := by funext i; exact i.elim0
    have h0 : H x - (H (fun _ ↦ (0 : ℝ)) + dot (fun _ ↦ (0 : ℝ)) x) = 0 := by
      rw [hx]; simp [dot]
    rw [h0, abs_zero]
    apply div_nonneg
    · positivity
    · exact mul_nonneg hc0.le (Nat.cast_nonneg _)
  · -- **Case `d ≥ 2`**: the pigeonhole/telescoping argument.
    haveI : Nonempty (Fin (d - 1)) := ⟨⟨d - 2, by omega⟩⟩
    have hcardI : 0 < I.card := Finset.card_pos.mpr hIne
    have hIcR : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hcardI
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hdm0 : (0 : ℝ) ≤ (d : ℝ) / m := by positivity
    set δ := 4 * (d : ℝ) ^ 4 * (m : ℝ) ^ ((d : ℤ) - 3) / (c * I.card) with hδdef
    have hδ : 0 < δ := by
      rw [hδdef]
      apply div_pos
      · positivity
      · exact mul_pos hc0 hIcR
    have basePt_mem : ∀ v ∈ I, basePt m v ∈ openBox c := by
      intro v hv
      rw [mem_openBox]; intro j
      have hvj := hI v hv j
      have h4 : (v j : ℝ) ≤ (m : ℝ) - 1 := by
        have h5 : v j + 1 ≤ m := hvj
        have h6 : (v j : ℝ) + 1 ≤ m := by exact_mod_cast h5
        linarith
      have h1 : (v j : ℝ) / m ≤ ((m : ℝ) - 1) / m :=
        div_le_div_of_nonneg_right h4 hmR.le
      have h2 : ((m : ℝ) - 1) / m < 1 := by rw [div_lt_one hmR]; linarith
      constructor
      · show (-c : ℝ) < (v j : ℝ) / m
        have h3 : (0 : ℝ) ≤ (v j : ℝ) / m := by positivity
        linarith [hc0]
      · show (v j : ℝ) / m < 1 + c
        exact lt_of_le_of_lt h1 (by linarith)
    by_contra hbad
    push_neg at hbad
    ------------------------------------------------------------------------
    -- **Per-cube claim** (paper Claim 3, derivative-free): on each `Q_v` the
    -- secant slopes of `H` along some coordinate line jump by `> δm/d`
    -- across an interval of length `≤ d/m` inside `[vᵢ/m − d/m, vᵢ/m + d/m]`.
    have claim : ∀ v ∈ I, ∃ i : Fin (d - 1), ∃ α β : ℝ,
        (v i : ℝ) / m - (d : ℝ) / m ≤ α ∧ α ≤ (v i : ℝ) / m ∧ (v i : ℝ) / m ≤ β ∧
          β ≤ (v i : ℝ) / m + (d : ℝ) / m ∧
            δ * m / d < uslope H m (basePt m v) i β - uslope H m (basePt m v) i α := by
      intro v hv
      set p := basePt m v with hpdef
      have hpj : ∀ j, p j = (v j : ℝ) / m := fun j ↦ rfl
      have hp_mem : p ∈ openBox c := basePt_mem v hv
      set l := fun j ↦ (H (Function.update p j ((v j : ℝ) / m + 1 / m)) - H p) / (1 / m)
        with hldef
      set b := H p - dot l p with hbdef
      obtain ⟨y, hy, hyg⟩ := hbad v hv b l
      have hy_mem : y ∈ openBox c := cubeOf_subset_openBox hc0 (hI v hv) hy
      set a := fun j ↦ y j - p j with hadef
      have ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1 / m := by
        intro j
        have h1 := (mem_cubeOf.mp hy) j
        have h2 : ((v j : ℝ) + 1) / m = (v j : ℝ) / m + 1 / m := by rw [add_div]
        rw [← hpj j, h2] at h1
        exact ⟨by simp only [hadef]; linarith [h1.1], by simp only [hadef]; linarith [h1.2]⟩
      set s := ∑ j, a j with hsdef
      have hs_ub : s ≤ ((d : ℝ) - 1) / m := by
        have h1 : s ≤ Finset.univ.card • ((1 : ℝ) / m) :=
          Finset.sum_le_card_nsmul _ _ _ fun j _ ↦ (ha j).2
        rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        have h2 : ((d - 1 : ℕ) : ℝ) * (1 / m) = ((d : ℝ) - 1) / m := by
          rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]; ring
        rwa [h2] at h1
      have hs_ub' : s ≤ (d : ℝ) / m := by
        refine le_trans hs_ub (div_le_div_of_nonneg_right ?_ hmR.le)
        linarith
      have hLp : b + dot l p = H p := by rw [hbdef]; ring
      have hLz : ∀ (i : Fin (d - 1)) (t : ℝ),
          b + dot l (Function.update p i t) = H p + l i * (t - p i) := by
        intro i t
        have hdot : dot l (Function.update p i t) = dot l p + l i * (t - p i) := by
          have key : ∀ j, l j * (Function.update p i t) j
              = l j * p j + (if j = i then l j * (t - p j) else 0) := by
            intro j; by_cases hji : j = i
            · subst hji; simp; ring
            · simp [Function.update_of_ne hji, hji]
          simp only [dot]
          rw [Finset.sum_congr rfl (fun j _ ↦ key j), Finset.sum_add_distrib]
          rw [Finset.sum_ite_eq' univ i (fun j ↦ l j * (t - p j))]
          simp only [Finset.mem_univ, ite_true]
          ring
        rw [hdot, hbdef]; ring
      have hLaff : ∀ (w : Fin (d - 1) → ℝ) (z : Fin (d - 1) → Fin (d - 1) → ℝ),
          ∑ j, w j = 1 → b + dot l (∑ j, w j • z j) = ∑ j, w j * (b + dot l (z j)) := by
        intro w z hw
        have h1 : dot l (∑ j, w j • z j) = ∑ j, w j * dot l (z j) := by
          simp only [dot, Pi.smul_apply, smul_eq_mul]
          have step1 : ∀ i : Fin (d - 1), l i * (∑ j, w j * z j i)
              = ∑ j, l i * (w j * z j i) :=
            fun i ↦ (Finset.mul_sum univ _ (l i)).symm
          rw [Finset.sum_congr rfl fun i _ ↦ step1 i]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          have step2 : ∀ i : Fin (d - 1), l i * (w j * z j i) = w j * (l i * z j i) :=
            fun i ↦ by ring
          rw [Finset.sum_congr rfl fun i _ ↦ step2 i]
          exact (Finset.mul_sum univ _ (w j)).symm
        calc b + dot l (∑ j, w j • z j)
            = (∑ j, w j) * b + dot l (∑ j, w j • z j) := by rw [hw, one_mul]
          _ = ∑ j, w j * b + ∑ j, w j * dot l (z j) := by rw [Finset.sum_mul, h1]
          _ = ∑ j, w j * (b + dot l (z j)) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _; rw [← mul_add]
      have hLaff2 : ∀ (w q : ℝ) (x z : Fin (d - 1) → ℝ), w + q = 1 →
          b + dot l (w • x + q • z) = w * (b + dot l x) + q * (b + dot l z) := by
        intro w q x z hw
        have h1 : dot l (w • x + q • z) = w * dot l x + q * dot l z := by
          simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have h2 : ∀ j, l j * (w * x j + q * z j)
              = w * (l j * x j) + q * (l j * z j) := fun j ↦ by ring
          rw [Finset.sum_congr rfl (fun j _ ↦ h2 j), Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
        have h3 : b = (w + q) * b := by rw [hw]; ring
        linarith [h1, h3]
      -- `s > 0`, since `y ≠ p`.
      have hs : 0 < s := by
        by_contra hs0
        push_neg at hs0
        have ha0 : ∀ j, a j = 0 := fun j ↦
          le_antisymm ((Finset.single_le_sum (fun i _ ↦ (ha i).1)
            (Finset.mem_univ j)).trans hs0) (ha j).1
        have hyeq : y = p := by
          funext j
          have h0 : a j = 0 := ha0 j
          rw [hadef] at h0
          simp only [] at h0
          linarith [h0]
        rw [hyeq, hLp, sub_self, abs_zero] at hyg
        linarith [hδ]
      -- The deviation `H − L` exceeds `δ` at some point `p + t·eᵢ` with `|t| ≤ (d−1)/m`.
      obtain ⟨i, t, htne, htle, hdev⟩ :
          ∃ (i : Fin (d - 1)) (t : ℝ), t ≠ 0 ∧ |t| ≤ ((d : ℝ) - 1) / m ∧
            δ < H (Function.update p i ((v i : ℝ) / m + t)) -
              (b + dot l (Function.update p i ((v i : ℝ) / m + t))) := by
        rcases lt_or_ge (H y - (b + dot l y)) δ with hB | hA
        swap
        · -- `H y ≥ L y + δ`: write `y = Σ (aⱼ/s)(p + s·eⱼ)`.
          set z := fun j ↦ Function.update p j ((v j : ℝ) / m + s) with hzdef
          have hz_mem : ∀ j, z j ∈ openBox c := by
            intro j
            apply update_mem_openBox hp_mem j
            have hvj : (v j : ℝ) / m ≤ ((m : ℝ) - 1) / m := by
              apply div_le_div_of_nonneg_right _ hmR.le
              have h5 : v j + 1 ≤ m := hI v hv j
              have h6 : (v j : ℝ) + 1 ≤ m := by exact_mod_cast h5
              linarith
            constructor
            · have h3 : (0 : ℝ) ≤ (v j : ℝ) / m + s := add_nonneg (by positivity) hs.le
              linarith [hc0]
            · have h4 : (v j : ℝ) / m + s ≤ ((m : ℝ) - 1) / m + ((d : ℝ) - 1) / m :=
                add_le_add hvj hs_ub
              have h5 : ((m : ℝ) - 1) / m + ((d : ℝ) - 1) / m < 1 + c := by
                have hdm : ((d : ℝ) - 2) / m < c := by
                  have h1 : (d : ℝ) / m < c := by linarith [hc]
                  have h2 : ((d : ℝ) - 2) / m ≤ (d : ℝ) / m :=
                    div_le_div_of_nonneg_right (by linarith) hmR.le
                  linarith
                have h3 : ((m : ℝ) - 1) / m + ((d : ℝ) - 1) / m = 1 + ((d : ℝ) - 2) / m := by
                  field_simp; ring
                rw [h3]; linarith
              exact lt_of_le_of_lt h4 h5
          have hy_conv : y = ∑ j, (a j / s) • z j := by
            funext i
            have hzij : ∀ j, z j i = p i + (if i = j then s else 0) := by
              intro j; by_cases hji : i = j
              · subst hji; simp [hzdef, hpj]
              · simp only [hzdef, Function.update_of_ne hji, hji, if_false, add_zero]
            simp only [Pi.smul_apply, smul_eq_mul, hzij, mul_add]
            rw [Finset.sum_add_distrib]
            have hsw : ∑ j, a j / s = 1 := by
              rw [← Finset.sum_div, div_self (ne_of_gt hs)]
            have h1 : ∑ j, a j / s * p i = p i := by
              rw [← Finset.sum_mul, hsw, one_mul]
            have h2 : ∑ j, a j / s * (if i = j then s else (0 : ℝ)) = a i := by
              have h3 : ∀ j, a j / s * (if i = j then s else (0 : ℝ))
                  = if i = j then a j else 0 := by
                intro j; by_cases hji : i = j
                · simp [hji, div_mul_cancel₀ _ (ne_of_gt hs)]
                · simp [hji]
              rw [Finset.sum_congr rfl (fun j _ ↦ h3 j), Finset.sum_ite_eq']
              simp
            rw [h1, h2]
            have : a i = y i - p i := rfl
            rw [this]; ring
          have hJ := hconv.map_sum_le (t := univ) (w := fun j ↦ a j / s) (p := z)
            (fun j _ ↦ div_nonneg (ha j).1 hs.le)
            (by rw [← Finset.sum_div, div_self (ne_of_gt hs)])
            (fun j _ ↦ hz_mem j)
          rw [← hy_conv] at hJ
          have hLy := hLaff (fun j ↦ a j / s) z
            (by rw [← Finset.sum_div, div_self (ne_of_gt hs)])
          rw [← hy_conv] at hLy
          have hsumlt : ∑ j, (a j / s) * δ < ∑ j, (a j / s) * (H (z j) - (b + dot l (z j))) := by
            have h1 : ∑ j, (a j / s) * δ = δ := by
              rw [← Finset.sum_mul, ← Finset.sum_div, div_self (ne_of_gt hs), one_mul]
            rw [h1]
            have h2 : ∑ j, (a j / s) * (H (z j) - (b + dot l (z j)))
                = ∑ j, (a j / s) • H (z j) - ∑ j, (a j / s) * (b + dot l (z j)) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro j _; rw [smul_eq_mul]; ring
            rw [h2, ← hLy]
            linarith [hJ, hA]
          obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt hsumlt
          have hai : 0 < a i / s := by
            by_contra hh
            push_neg at hh
            have h0 : a i / s = 0 := le_antisymm hh (div_nonneg (ha i).1 hs.le)
            rw [h0] at hi; simp at hi
          have hΔi : δ < H (z i) - (b + dot l (z i)) :=
            (mul_lt_mul_left hai).mp hi
          refine ⟨i, s, ne_of_gt hs, ?_, ?_⟩
          · rw [abs_of_pos hs]; exact hs_ub
          · rwa [hzdef]
        · -- `H y < L y - δ`: write `p = (1/2)y + (1/2)zbar` with `zbar = Σ (aⱼ/s)(p − s·eⱼ)`.
          have hB' : H y - (b + dot l y) < -δ := by
            rcases lt_or_ge (H y - (b + dot l y)) 0 with h1 | h1
            · rw [abs_of_neg h1] at hyg; linarith
            · rw [abs_of_nonneg h1] at hyg; linarith
          set z := fun j ↦ Function.update p j ((v j : ℝ) / m - s) with hzdef
          have hz_mem : ∀ j, z j ∈ openBox c := by
            intro j
            apply update_mem_openBox hp_mem j
            have hvj : (v j : ℝ) / m ≤ ((m : ℝ) - 1) / m := by
              apply div_le_div_of_nonneg_right _ hmR.le
              have h5 : v j + 1 ≤ m := hI v hv j
              have h6 : (v j : ℝ) + 1 ≤ m := by exact_mod_cast h5
              linarith
            have h6 : ((m : ℝ) - 1) / m < 1 := by rw [div_lt_one hmR]; linarith
            constructor
            · have h3 : -((d : ℝ) - 1) / m ≤ (v j : ℝ) / m - s := by
                have h7 : (0 : ℝ) ≤ (v j : ℝ) / m := by positivity
                linarith [hs_ub]
              have h4 : -c < -((d : ℝ) - 1) / m := by
                have hdm : (d : ℝ) / m < c := by linarith [hc]
                have h5 : ((d : ℝ) - 1) / m ≤ (d : ℝ) / m :=
                  div_le_div_of_nonneg_right (by linarith) hmR.le
                linarith
              linarith
            · linarith [hvj]
          set zbar := ∑ j, (a j / s) • z j with hzbar
          have hzbar_mem : zbar ∈ openBox c := by
            apply hconv.1.sum_mem (fun j _ ↦ div_nonneg (ha j).1 hs.le) _ (fun j _ ↦ hz_mem j)
            rw [← Finset.sum_div]
            have hss : ∑ j, a j = s := rfl
            rw [hss]; exact div_self (ne_of_gt hs)
          have hp_conv : p = (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • zbar := by
            funext i0
            have hzij : ∀ j, z j i0 = p i0 + (if i0 = j then -s else 0) := by
              intro j; by_cases hji : i0 = j
              · subst hji; simp [hzdef, hpj, sub_eq_add_neg]
              · simp only [hzdef, Function.update_of_ne hji, hji, if_false, add_zero]
            have hzbari : zbar i0 = p i0 - a i0 := by
              simp only [hzbar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hzij, mul_add]
              rw [Finset.sum_add_distrib]
              have hsw : ∑ j, a j / s = 1 := by
                rw [← Finset.sum_div]; exact div_self (ne_of_gt hs)
              have h1 : ∑ j, a j / s * p i0 = p i0 := by
                rw [← Finset.sum_mul, hsw, one_mul]
              have h2 : ∑ j, a j / s * (if i0 = j then -s else (0 : ℝ)) = -a i0 := by
                have h3 : ∀ j, a j / s * (if i0 = j then -s else (0 : ℝ))
                    = if i0 = j then -a j else 0 := by
                  intro j; by_cases hji : i0 = j
                  · simp [hji]
                  · simp [hji]
                rw [Finset.sum_congr rfl (fun j _ ↦ h3 j), Finset.sum_ite_eq']
              rw [h1, h2]; ring
            simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hzbari]
            have hai : a i0 = y i0 - p i0 := rfl
            rw [hai]; ring
          have hJ := hconv.2 hy_mem hzbar_mem
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
            (by norm_num : (1/2:ℝ) + 1/2 = 1)
          rw [← hp_conv] at hJ
          -- `hJ : H p ≤ (1/2)•H y + (1/2)•H zbar`
          have hJ2 := hconv.map_sum_le (t := univ) (w := fun j ↦ a j / s) (p := z)
            (fun j _ ↦ div_nonneg (ha j).1 hs.le)
            (by rw [← Finset.sum_div]
                have hss : ∑ j, a j = s := rfl
                rw [hss]; exact div_self (ne_of_gt hs))
            (fun j _ ↦ hz_mem j)
          -- `hJ2 : H zbar ≤ ∑ (aⱼ/s) • H (zⱼ)`
          have hLzbar := hLaff (fun j ↦ a j / s) z
            (by rw [← Finset.sum_div]
                have hss : ∑ j, a j = s := rfl
                rw [hss]; exact div_self (ne_of_gt hs))
          have hLpz : b + dot l p = (1/2) * (b + dot l y) + (1/2) * (b + dot l zbar) := by
            have h1 := hLaff2 (1/2) (1/2) y zbar (by norm_num : (1:ℝ)/2 + 1/2 = 1)
            have h2 : b + dot l ((1/2:ℝ) • y + (1/2:ℝ) • zbar)
                = b + dot l p := by rw [← hp_conv]
            rw [h2] at h1
            simp only [smul_eq_mul] at h1 ⊢
            linarith [h1]
          -- Combine: `0 = Δp ≤ (1/2)Δy + Σ wⱼ Δzⱼ`, so `δ/2 < Σ wⱼ Δzⱼ`.
          have hsumlt : ∑ j, (a j / (2 * s)) * δ
              < ∑ j, (a j / (2 * s)) * (H (z j) - (b + dot l (z j))) := by
            have hsw : ∑ j, a j / (2 * s) = 1 / 2 := by
              rw [← Finset.sum_div]
              have hss : ∑ j, a j = s := rfl
              rw [hss]; field_simp; ring
            have h1 : ∑ j, (a j / (2 * s)) * δ = δ / 2 := by
              rw [← Finset.sum_mul, hsw]; ring
            rw [h1]
            have h2 : ∑ j, (a j / (2 * s)) * (H (z j) - (b + dot l (z j)))
                = (1/2) * (H zbar - (b + dot l zbar))
                  + ∑ j, (a j / (2 * s)) * (H (z j) - (b + dot l (z j)))
                  - (1/2) * ∑ j, (a j / s) * (H (z j) - (b + dot l (z j))) := by
              rw [Finset.mul_sum]
              have h3 : ∀ j, (a j / (2 * s)) * (H (z j) - (b + dot l (z j)))
                  = (1/2) * ((a j / s) * (H (z j) - (b + dot l (z j)))) := by
                intro j; field_simp; ring
              rw [Finset.sum_congr rfl (fun j _ ↦ h3 j), ← Finset.mul_sum]
              ring
            rw [h2]
            have hJ2' : H zbar ≤ ∑ j, (a j / s) * (H (z j)) := by
              have := hJ2
              simp only [smul_eq_mul] at this ⊢
              exact this
            have hLzbar' : b + dot l zbar = ∑ j, (a j / s) * (b + dot l (z j)) := hLzbar
            have hkey : (1/2) * (H zbar - (b + dot l zbar))
                ≤ (1/2) * ∑ j, (a j / s) * (H (z j) - (b + dot l (z j))) := by
              have h4 : ∑ j, (a j / s) * (H (z j) - (b + dot l (z j)))
                  = ∑ j, (a j / s) * H (z j) - ∑ j, (a j / s) * (b + dot l (z j)) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl; intro j _; ring
              rw [h4, ← hLzbar']
              nlinarith [hJ2']
            have hHp : (1/2) * (H y - (b + dot l y)) + (1/2) * (H zbar - (b + dot l zbar)) ≥ 0 := by
              have hHp' : H p = b + dot l p := by rw [hbdef]; ring
              have hJ' : H p ≤ (1/2) * H y + (1/2) * H zbar := by
                have := hJ
                simp only [smul_eq_mul] at this ⊢
                exact this
              linarith [hLpz, hHp', hJ']
            linarith [hkey, hHp, hB']
          obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt hsumlt
          have hai : 0 < a i / (2 * s) := by
            by_contra hh
            push_neg at hh
            have h0 : a i / (2 * s) = 0 :=
              le_antisymm hh (div_nonneg (ha i).1 (by positivity))
            rw [h0] at hi; simp at hi
          have hΔi : δ < H (z i) - (b + dot l (z i)) :=
            (mul_lt_mul_left hai).mp hi
          refine ⟨i, -s, by linarith, ?_, ?_⟩
          · rw [abs_neg, abs_of_pos hs]; exact hs_ub
          · convert hΔi using 2
            rw [hzdef]; ring_nf
      -- Secant-slope analysis on the `i`-th coordinate line.
      set φ := fun t ↦ H (Function.update p i t) with hφdef
      have hf : ConvexOn ℝ (Set.Ioo (-c) (1 + c)) φ := convexOn_update_line hconv hp_mem i
      have hupdeq : Function.update p i ((v i : ℝ) / m) = p := by
        have h1 : (v i : ℝ) / m = p i := (hpj i).symm
        rw [h1]; exact Function.update_eq_self _ _
      have hφp : φ ((v i : ℝ) / m) = H p := by
        show H (Function.update p i ((v i : ℝ) / m)) = H p
        rw [hupdeq]
      have hvm0 : (0 : ℝ) ≤ (v i : ℝ) / m := by positivity
      have hvm1 : (v i : ℝ) / m ≤ ((m : ℝ) - 1) / m := by
        apply div_le_div_of_nonneg_right _ hmR.le
        have h5 : v i + 1 ≤ m := hI v hv i
        have h6 : (v i : ℝ) + 1 ≤ m := by exact_mod_cast h5
        linarith
      have hdm : (d : ℝ) / m < c := by
        have h2 : (d : ℝ) / m ≤ 2 * (d : ℝ) / m :=
          div_le_div_of_nonneg_right (by linarith) hmR.le
        linarith [hc]
      have hmemI : ∀ u : ℝ, |u - (v i : ℝ) / m| ≤ (d : ℝ) / m → u ∈ Set.Ioo (-c) (1 + c) := by
        intro u hu
        rw [abs_le] at hu
        have h1 : -c < -(d : ℝ) / m := by linarith [hdm]
        have h2 : (v i : ℝ) / m + (d : ℝ) / m < 1 + c := by
          have h3 : (v i : ℝ) / m + (d : ℝ) / m ≤ ((m : ℝ) - 1) / m + (d : ℝ) / m := by linarith
          have h4 : ((m : ℝ) - 1) / m + (d : ℝ) / m = 1 + ((d : ℝ) - 1) / m := by
            field_simp; ring
          have h5 : ((d : ℝ) - 1) / m < c := by
            have h6 : ((d : ℝ) - 1) / m ≤ 2 * (d : ℝ) / m :=
              div_le_div_of_nonneg_right (by linarith) hmR.le
            linarith [hc]
          linarith
        exact ⟨by linarith [hu.1, hvm0, h1], by linarith [hu.2, h2]⟩
      have hdev' : δ < φ ((v i : ℝ) / m + t) - (H p + l i * t) := by
        have h := hdev
        rw [hLz i ((v i : ℝ) / m + t)] at h
        have hpi : p i = (v i : ℝ) / m := hpj i
        rw [hpi] at h
        have hsub : (v i : ℝ) / m + t - (v i : ℝ) / m = t := by ring
        rw [hsub] at h
        exact h
      have hli : l i = (φ ((v i : ℝ) / m + 1 / m) - H p) / (1 / m) := by
        show l i = (H (Function.update p i ((v i : ℝ) / m + 1 / m)) - H p) / (1 / m)
        rw [hldef]
      have hlp : uslope H m p i ((v i : ℝ) / m) = l i := by
        rw [uslope, hφp]
        exact hli.symm
      rcases lt_or_gt_of_ne htne with htn | htp
      · -- `t < 0`: the jump is below `vᵢ/m`; set `u = −t ∈ (0, (d−1)/m]`.
        set u := -t with hudef
        have hu0 : 0 < u := by linarith
        have htu : t = -u := by linarith
        have hub : u ≤ ((d : ℝ) - 1) / m := by
          have h1 : |t| = u := by rw [htu, abs_neg, abs_of_pos hu0]
          rw [h1] at htle; exact htle
        have hub2 : u + 1 / m ≤ (d : ℝ) / m := by
          have h1 : u + 1 / m ≤ ((d : ℝ) - 1) / m + 1 / m := add_le_add_right hub _
          have h2 : ((d : ℝ) - 1) / m + 1 / m = (d : ℝ) / m := by field_simp; ring
          linarith [h1, h2]
        refine ⟨i, (v i : ℝ) / m - u - 1 / m, (v i : ℝ) / m, ?_, le_rfl, le_rfl, ?_, ?_⟩
        · linarith [hub2]
        · have hdm0 : (0 : ℝ) ≤ (d : ℝ) / m := by positivity
          linarith
        · -- `uslope(vᵢ/m) − uslope(vᵢ/m − u − 1/m) > δm/d`.
          have hx1 : (v i : ℝ) / m - u - 1 / m ∈ Set.Ioo (-c) (1 + c) := by
            apply hmemI; rw [abs_le]; constructor <;> linarith
          have hz1 : (v i : ℝ) / m ∈ Set.Ioo (-c) (1 + c) := by
            apply hmemI; rw [abs_le]; constructor <;> linarith [hdm]
          have hs1 : (φ ((v i : ℝ) / m - u) - φ ((v i : ℝ) / m - u - 1 / m)) / (1 / m)
              ≤ (φ ((v i : ℝ) / m) - φ ((v i : ℝ) / m - u)) / u := by
            have ha2 := hf.secant_mono_aux2 hx1 hz1
              (x := (v i : ℝ) / m - u - 1 / m) (y := (v i : ℝ) / m - u) (z := (v i : ℝ) / m)
              (by linarith) (by linarith)
            have ha3 := hf.secant_mono_aux3 hx1 hz1
              (x := (v i : ℝ) / m - u - 1 / m) (y := (v i : ℝ) / m - u) (z := (v i : ℝ) / m)
              (by linarith) (by linarith)
            have e1 : (v i : ℝ) / m - u - ((v i : ℝ) / m - u - 1 / m) = 1 / m := by ring
            have e2 : (v i : ℝ) / m - ((v i : ℝ) / m - u) = u := by ring
            rw [e1] at ha2; rw [e2] at ha3
            exact le_trans ha2 ha3
          have hs2 : (φ ((v i : ℝ) / m) - φ ((v i : ℝ) / m - u)) / u < l i - δ / u := by
            have hdev2 : δ < φ ((v i : ℝ) / m - u) - (H p - l i * u) := by
              have h := hdev'
              rw [htu] at h
              convert h using 2
              · congr 1; ring
              · ring
            have h1 : φ ((v i : ℝ) / m) - φ ((v i : ℝ) / m - u) < l i * u - δ := by
              rw [hφp]; linarith [hdev2]
            have h2 : (φ ((v i : ℝ) / m) - φ ((v i : ℝ) / m - u)) / u
                < (l i * u - δ) / u := by gcongr
            have h3 : (l i * u - δ) / u = l i - δ / u := by field_simp
            linarith [h2, h3]
          have hdu : δ * m / d ≤ δ / u := by
            have h1 : δ / ((d : ℝ) / m) ≤ δ / u :=
              div_le_div_of_nonneg_left hδ.le hu0 (le_trans hub
                (div_le_div_of_nonneg_right (by linarith) hmR.le))
            have h2 : δ / ((d : ℝ) / m) = δ * m / d := by field_simp; ring
            linarith [h1, h2]
          have hαeq : uslope H m p i ((v i : ℝ) / m - u - 1 / m)
              = (φ ((v i : ℝ) / m - u) - φ ((v i : ℝ) / m - u - 1 / m)) / (1 / m) := by
            rw [uslope]
            have e1 : (v i : ℝ) / m - u - 1 / m + 1 / m = (v i : ℝ) / m - u := by ring
            rw [e1]
          rw [hlp, hαeq]
          linarith [hs1, hs2, hdu]
      · -- `t > 0`: necessarily `t > 1/m`; the jump is above `vᵢ/m`.
        have ht1 : 1 / m < t := by
          rcases lt_trichotomy t (1 / m) with h1 | h1 | h1
          · exfalso
            have hm1 : (v i : ℝ) / m ∈ Set.Ioo (-c) (1 + c) := by
              apply hmemI; rw [abs_le]; constructor <;> linarith [hdm]
            have hm3 : (v i : ℝ) / m + 1 / m ∈ Set.Ioo (-c) (1 + c) := by
              apply hmemI; rw [abs_le]; constructor <;> linarith [hdm]
            have hsm := hf.secant_mono_aux2 hm1 hm3
              (x := (v i : ℝ) / m) (y := (v i : ℝ) / m + t) (z := (v i : ℝ) / m + 1 / m)
              (by linarith) (by linarith)
            have e1 : (v i : ℝ) / m + t - (v i : ℝ) / m = t := by ring
            have e2 : (v i : ℝ) / m + 1 / m - (v i : ℝ) / m = 1 / m := by ring
            rw [e1, e2, hφp] at hsm
            rw [← hli] at hsm
            -- `hsm : (φ(vᵢ/m+t) − Hp)/t ≤ l i`
            have hgt : l i * t + δ < φ ((v i : ℝ) / m + t) - H p := by linarith [hdev']
            have hle : φ ((v i : ℝ) / m + t) - H p ≤ l i * t := by
              have h2 := (div_le_iff₀ htp).mp hsm
              linarith [h2]
            linarith
          · exfalso
            rw [← h1] at hdev'
            have hli' : l i * (1 / m) = φ ((v i : ℝ) / m + 1 / m) - H p := by
              rw [hli]; field_simp
            linarith [hdev', hδ, hli']
          · exact h1
        refine ⟨i, (v i : ℝ) / m, (v i : ℝ) / m + t, ?_, le_rfl, le_rfl, ?_, ?_⟩
        · have hdm0 : (0 : ℝ) ≤ (d : ℝ) / m := by positivity
          linarith
        · have h2 : t ≤ ((d : ℝ) - 1) / m := by
            have h3 : |t| = t := abs_of_pos htp
            rw [h3] at htle; exact htle
          have h4 : ((d : ℝ) - 1) / m ≤ (d : ℝ) / m :=
            div_le_div_of_nonneg_right (by linarith) hmR.le
          linarith
        · -- `uslope(vᵢ/m + t) − uslope(vᵢ/m) > δm/d`.
          have hm1 : (v i : ℝ) / m ∈ Set.Ioo (-c) (1 + c) := by
            apply hmemI; rw [abs_le]; constructor <;> linarith [hdm]
          have hmz : (v i : ℝ) / m + t + 1 / m ∈ Set.Ioo (-c) (1 + c) := by
            apply hmemI; rw [abs_le]
            have h2 : t ≤ (d : ℝ) / m := le_trans
              (by have h3 : |t| = t := abs_of_pos htp
                  rw [h3] at htle; exact htle)
              (div_le_div_of_nonneg_right (by linarith) hmR.le)
            constructor <;> linarith
          have hstep : (φ ((v i : ℝ) / m + t) - H p) / t
              ≤ uslope H m p i ((v i : ℝ) / m + t) := by
            have ha2 := hf.secant_mono_aux2 hm1 hmz
              (x := (v i : ℝ) / m) (y := (v i : ℝ) / m + t) (z := (v i : ℝ) / m + t + 1 / m)
              (by linarith) (by linarith)
            have ha3 := hf.secant_mono_aux3 hm1 hmz
              (x := (v i : ℝ) / m) (y := (v i : ℝ) / m + t) (z := (v i : ℝ) / m + t + 1 / m)
              (by linarith) (by linarith)
            have e1 : (v i : ℝ) / m + t - (v i : ℝ) / m = t := by ring
            have e2 : (v i : ℝ) / m + t + 1 / m - ((v i : ℝ) / m + t) = 1 / m := by ring
            rw [e1] at ha2; rw [e2] at ha3; rw [hφp] at ha2
            have huseq : (φ ((v i : ℝ) / m + t + 1 / m) - φ ((v i : ℝ) / m + t)) / (1 / m)
                = uslope H m p i ((v i : ℝ) / m + t) := by rw [uslope]
            rw [← huseq] at ha3
            exact le_trans ha2 ha3
          have hgt : l i + δ / t < (φ ((v i : ℝ) / m + t) - H p) / t := by
            have h1 : l i * t + δ < φ ((v i : ℝ) / m + t) - H p := by linarith [hdev']
            have h2 : (l i * t + δ) / t < (φ ((v i : ℝ) / m + t) - H p) / t := by gcongr
            have h3 : (l i * t + δ) / t = l i + δ / t := by field_simp
            linarith [h2, h3]
          have hdu : δ * m / d ≤ δ / t := by
            have h4 : t ≤ (d : ℝ) / m := le_trans
              (by have h3 : |t| = t := abs_of_pos htp
                  rw [h3] at htle; exact htle)
              (div_le_div_of_nonneg_right (by linarith) hmR.le)
            have h1 : δ / ((d : ℝ) / m) ≤ δ / t :=
              div_le_div_of_nonneg_left hδ.le htp h4
            have h2 : δ / ((d : ℝ) / m) = δ * m / d := by field_simp; ring
            linarith [h1, h2]
          rw [hlp]
          linarith [hstep, hgt, hdu]
    ------------------------------------------------------------------------
    -- Pigeonhole: many cubes sharing a coordinate `i'`, a projection off `i'`,
    -- and a residue class of `v i'` mod `2d`.
    choose! i α β hsel using claim
    obtain ⟨i', _, hi'⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := I) (t := (univ : Finset (Fin (d - 1)))) (f := i)
      (fun v _ ↦ mem_univ _)
      (by rw [card_univ, Fintype.card_fin]
          have h1 : (d - 1) * ((I.card - 1) / (d - 1)) ≤ I.card - 1 := Nat.mul_div_le _ _
          have h2 : (d - 1) * ((I.card - 1) / (d - 1)) < I.card := by omega
          exact h2)
    set F := I.filter (fun v ↦ i v = i') with hFdef
    have hFpos : 0 < F.card := by omega
    have hF1 : I.card ≤ (d - 1) * F.card := by
      have h2 := Nat.div_add_mod (I.card - 1) (d - 1)
      have h3 := Nat.mod_lt (I.card - 1) (by omega : 0 < d - 1)
      have h4 : (d - 1) * ((I.card - 1) / (d - 1) + 1) ≥ I.card := by omega
      have h5 : (d - 1) * F.card ≥ (d - 1) * ((I.card - 1) / (d - 1) + 1) := by
        apply Nat.mul_le_mul_left
        omega
      omega
    -- Projection off `i'` : `Fin (d-2) → ℕ`.
    set Proj := fun (v : Fin (d - 1) → ℕ) (j : Fin (d - 2)) ↦ v (i'.succAbove j)
      with hProjdef
    set T := Fintype.piFinset (fun _ : Fin (d - 2) ↦ Finset.range m) with hTdef
    have hTcard : T.card = m ^ (d - 2) := by
      rw [hTdef, Fintype.card_piFinset, Finset.prod_const, card_univ, Fintype.card_fin]
    have hmaps2 : ∀ v ∈ F, Proj v ∈ T := by
      intro v hv
      rw [hTdef, Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_range]
      exact hI v (Finset.mem_of_mem_filter hv) (i'.succAbove j)
    obtain ⟨π₀, _, hπ₀⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := F) (t := T) (f := Proj) hmaps2
      (by rw [hTcard]
          have h1 : m ^ (d - 2) * ((F.card - 1) / m ^ (d - 2)) ≤ F.card - 1 :=
            Nat.mul_div_le _ _
          omega)
    set W := F.filter (fun v ↦ Proj v = π₀) with hWdef
    have hWpos : 0 < W.card := by omega
    have hW1 : F.card ≤ m ^ (d - 2) * W.card := by
      have h2 := Nat.div_add_mod (F.card - 1) (m ^ (d - 2))
      have h3 := Nat.mod_lt (F.card - 1) (pow_pos hm _)
      have h4 : m ^ (d - 2) * ((F.card - 1) / m ^ (d - 2) + 1) ≥ F.card := by omega
      have h5 : m ^ (d - 2) * W.card ≥ m ^ (d - 2) * ((F.card - 1) / m ^ (d - 2) + 1) := by
        apply Nat.mul_le_mul_left
        omega
      omega
    obtain ⟨r, _, hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := W) (t := Finset.range (2 * d)) (f := fun v ↦ v i' % (2 * d))
      (fun v _ ↦ Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
      (by rw [Finset.card_range]
          have h1 : 2 * d * ((W.card - 1) / (2 * d)) ≤ W.card - 1 := Nat.mul_div_le _ _
          omega)
    set G := W.filter (fun v ↦ v i' % (2 * d) = r) with hGdef
    have hGpos : 0 < G.card := by omega
    have hG1 : W.card ≤ 2 * d * G.card := by
      have h2 := Nat.div_add_mod (W.card - 1) (2 * d)
      have h3 := Nat.mod_lt (W.card - 1) (by omega : 0 < 2 * d)
      have h4 : 2 * d * ((W.card - 1) / (2 * d) + 1) ≥ W.card := by omega
      have h5 : 2 * d * G.card ≥ 2 * d * ((W.card - 1) / (2 * d) + 1) := by
        apply Nat.mul_le_mul_left
        omega
      omega
    have hGI : I.card ≤ 2 * d * (d - 1) * m ^ (d - 2) * G.card := by
      have h1 : (d - 1) * F.card ≤ (d - 1) * (m ^ (d - 2) * W.card) :=
        Nat.mul_le_mul_left _ hW1
      have h2 : m ^ (d - 2) * W.card ≤ m ^ (d - 2) * (2 * d * G.card) :=
        Nat.mul_le_mul_left _ hG1
      have h3 : (d - 1) * (m ^ (d - 2) * W.card)
          ≤ (d - 1) * (m ^ (d - 2) * (2 * d * G.card)) :=
        Nat.mul_le_mul_left _ h2
      have h4 := le_trans (le_trans hF1 h1) h3
      have h5 : (d - 1) * (m ^ (d - 2) * (2 * d * G.card))
          = 2 * d * (d - 1) * m ^ (d - 2) * G.card := by ring
      rw [h5] at h4; exact h4
    ------------------------------------------------------------------------
    -- Sort the selected cubes by their `i'`-th coordinate.
    set g := G.card with hgdef
    have hgpos : 0 < g := hGpos
    have hinj : ∀ v ∈ G, ∀ w ∈ G, v i' = w i' → v = w := by
      intro v hv w hw hvw
      funext k
      by_cases hk : k = i'
      · rw [hk]; exact hvw
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk
        have hvP : Proj v = π₀ := (Finset.mem_filter.mp (Finset.mem_of_mem_filter hv)).2
        have hwP : Proj w = π₀ := (Finset.mem_filter.mp (Finset.mem_of_mem_filter hw)).2
        have e1 : v (i'.succAbove j) = π₀ j := congr_fun hvP j
        have e2 : w (i'.succAbove j) = π₀ j := congr_fun hwP j
        rw [← hj, e1, e2]
    set E := G.image (fun v ↦ v i') with hEdef
    have hEcard : E.card = g := by
      rw [hEdef]
      exact (Finset.card_image_of_injOn (fun v hv w hw ↦ hinj v hv w hw)).trans rfl
    set u := Finset.orderEmbOfFin E hEcard with hudef
    have hu_mem : ∀ j : Fin g, u j ∈ E := fun j ↦ Finset.orderEmbOfFin_mem _ _ _
    have hpre : ∀ j : Fin g, ∃ v ∈ G, v i' = u j := fun j ↦ Finset.mem_image.mp (hu_mem j)
    choose! vv hvvG hvvi using hpre
    have hvvI : ∀ j : Fin g, vv j ∈ I := fun j ↦
      Finset.mem_of_mem_filter (Finset.mem_of_mem_filter (Finset.mem_of_mem_filter (hvvG j)))
    have hvvi' : ∀ j : Fin g, i (vv j) = i' := fun j ↦
      (Finset.mem_filter.mp (Finset.mem_of_mem_filter (Finset.mem_of_mem_filter (hvvG j)))).2
    have hvvP : ∀ j : Fin g, Proj (vv j) = π₀ := fun j ↦
      (Finset.mem_filter.mp (Finset.mem_of_mem_filter (hvvG j))).2
    have hvvmod : ∀ j : Fin g, (vv j) i' % (2 * d) = r := fun j ↦
      (Finset.mem_filter.mp (hvvG j)).2
    have hgap : ∀ j₁ j₂ : Fin g, j₁ < j₂ → (vv j₁) i' + 2 * d ≤ (vv j₂) i' := by
      intro j₁ j₂ hjj
      have hlt : (vv j₁) i' < (vv j₂) i' := by
        rw [hvvi, hvvi]
        exact (u.lt_iff_lt).mpr hjj
      have hmod : (vv j₁) i' ≡ (vv j₂) i' [MOD 2 * d] := by
        rw [Nat.ModEq, hvvmod, hvvmod]
      have hdvd : 2 * d ∣ (vv j₂) i' - (vv j₁) i' :=
        (Nat.modEq_iff_dvd' hlt.le).mp hmod
      have hle := Nat.le_of_dvd (by omega : 0 < (vv j₂) i' - (vv j₁) i') hdvd
      omega
    -- The common coordinate line: all `basePt (vv j)` agree off `i'`.
    set P := basePt m (vv ⟨0, hgpos⟩) with hPdef
    have hPi : ∀ j : Fin g, ∀ t : ℝ,
        Function.update (basePt m (vv j)) i' t = Function.update P i' t := by
      intro j t
      funext k
      by_cases hk : k = i'
      · simp [hk]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        obtain ⟨jj, hjj⟩ := Fin.exists_succAbove_eq hk
        have e1 : (vv j) (i'.succAbove jj) = π₀ jj := congr_fun (hvvP j) jj
        have e2 : (vv ⟨0, hgpos⟩) (i'.succAbove jj) = π₀ jj :=
          congr_fun (hvvP ⟨0, hgpos⟩) jj
        rw [← hjj]
        simp only [basePt]
        rw [e1, e2]
    set U := fun t ↦ uslope H m P i' t with hUdef
    have hUeq : ∀ j : Fin g, ∀ t : ℝ, uslope H m (basePt m (vv j)) i' t = U t := by
      intro j t
      simp only [uslope, hUdef]
      rw [hPi j (t + 1 / m), hPi j t]
    have hPm : P ∈ openBox c := basePt_mem _ (hvvI ⟨0, hgpos⟩)
    -- Membership criterion for the slope estimates.
    have hmemP : ∀ j : Fin g, ∀ u' : ℝ,
        |u' - (vv j) i' / m| ≤ ((d : ℝ) + 1) / m → u' ∈ Set.Ioo (-c) (1 + c) := by
      intro j u' hu
      have hv0 : (0 : ℝ) ≤ (vv j) i' / m := by positivity
      have hv1 : (vv j) i' / m ≤ ((m : ℝ) - 1) / m := by
        apply div_le_div_of_nonneg_right _ hmR.le
        have h5 : (vv j) i' + 1 ≤ m := hI _ (hvvI j) i'
        have h6 : ((vv j) i' : ℝ) + 1 ≤ m := by exact_mod_cast h5
        linarith
      have hd1 : ((d : ℝ) + 1) / m ≤ 2 * (d : ℝ) / m :=
        div_le_div_of_nonneg_right (by linarith [hd]) hmR.le
      rw [abs_le] at hu
      constructor
      · linarith [hu.1, hv0, hd1, hc]
      · have h2 : (vv j) i' / m + ((d : ℝ) + 1) / m ≤ 1 + (d : ℝ) / m := by
          have h3 : ((m : ℝ) - 1) / m + ((d : ℝ) + 1) / m = 1 + (d : ℝ) / m := by
            field_simp; ring
          linarith [hv1, h3]
        have h4 : (d : ℝ) / m < c := by
          have h5 : (d : ℝ) / m ≤ 2 * (d : ℝ) / m :=
            div_le_div_of_nonneg_right (by linarith) hmR.le
          linarith [hc]
        linarith [hu.2, h2, h4]
    -- Collected facts about each selected cube.
    set A := fun j : Fin g ↦ α (vv j) with hAdef
    set B := fun j : Fin g ↦ β (vv j) with hBdef
    have hfacts : ∀ j : Fin g,
        (vv j) i' / m - (d : ℝ) / m ≤ A j ∧ A j ≤ (vv j) i' / m ∧
          (vv j) i' / m ≤ B j ∧ B j ≤ (vv j) i' / m + (d : ℝ) / m ∧
            δ * m / d < U (B j) - U (A j) := by
      intro j
      have hs := hsel (vv j) (hvvI j)
      rw [hvvi' j] at hs
      have h1 := hs.1
      have h2 := hs.2.1
      have h3 := hs.2.2.1
      have h4 := hs.2.2.2.1
      have h5 := hs.2.2.2.2
      rw [hUeq j (β (vv j)), hUeq j (α (vv j))] at h5
      exact ⟨h1, h2, h3, h4, h5⟩
    -- `U` is monotone over unit steps.
    have hUmono : ∀ (t₁ t₂ : ℝ),
        t₁ ∈ Set.Ioo (-c) (1 + c) → t₂ + 1 / m ∈ Set.Ioo (-c) (1 + c) → t₁ ≤ t₂ →
          U t₁ ≤ U t₂ := by
      intro t₁ t₂ ht₁ ht₂ hle
      have hfP : ConvexOn ℝ (Set.Ioo (-c) (1 + c)) (fun t ↦ H (Function.update P i' t)) :=
        convexOn_update_line hconv hPm i'
      have h := unit_slope_mono hfP (by positivity : (0:ℝ) < 1 / m) ht₁ ht₂ hle
      simp only [uslope, hUdef]
      exact h
    -- `U` is bounded by `2/c` on the middle interval.
    have hUbound : ∀ t : ℝ, t ∈ Set.Ioo (-c / 2) (1 + c / 2) → -2 / c ≤ U t ∧ U t ≤ 2 / c := by
      intro t ht
      have hcm : (4 : ℝ) < c * m := by
        have h1 : 2 * (d : ℝ) / m * m < c * m := mul_lt_mul_of_pos_right hc hmR
        have h2 : 2 * (d : ℝ) / m * m = 2 * d := by field_simp
        rw [h2] at h1
        nlinarith [h1, hd2]
      have h1m : (1 : ℝ) / m < c / 2 := by
        rw [div_lt_div_iff hmR (by norm_num : (0:ℝ) < 2)]
        nlinarith [hcm]
      have hfP : ConvexOn ℝ (Set.Ioo (-c) (1 + c)) (fun t ↦ H (Function.update P i' t)) :=
        convexOn_update_line hconv hPm i'
      have htm : t ∈ Set.Ioo (-c) (1 + c) := ⟨by linarith [ht.1, hc0], by linarith [ht.2, hc0]⟩
      have ht1 : t + 1 / m ∈ Set.Ioo (-c) (1 + c) :=
        ⟨by linarith [ht.1, h1m], by linarith [ht.2, h1m]⟩
      have ht2 : t + c / 2 ∈ Set.Ioo (-c) (1 + c) :=
        ⟨by linarith [ht.1, hc0], by linarith [ht.2]⟩
      have ht3 : t - c / 2 ∈ Set.Ioo (-c) (1 + c) :=
        ⟨by linarith [ht.1], by linarith [ht.2, hc0]⟩
      have φbd : ∀ u : ℝ, u ∈ Set.Ioo (-c) (1 + c) → 0 ≤ H (Function.update P i' u) ∧
          H (Function.update P i' u) ≤ 1 := fun u hu ↦
        hbdd _ (update_mem_openBox hPm i' hu)
      constructor
      · -- `U t ≥ slope(t − c/2, t) ≥ −2/c`.
        have ha2 := hfP.secant_mono_aux2 ht3 ht1
          (x := t - c / 2) (y := t) (z := t + 1 / m) (by linarith) (by linarith)
        have ha3 := hfP.secant_mono_aux3 ht3 ht1
          (x := t - c / 2) (y := t) (z := t + 1 / m) (by linarith) (by linarith)
        have e1 : t + 1 / m - t = 1 / m := by ring
        have e2 : t - (t - c / 2) = c / 2 := by ring
        have e3 : t + 1 / m - (t - c / 2) = c / 2 + 1 / m := by ring
        rw [e2] at ha2; rw [e3] at ha2 ha3; rw [e1] at ha3
        -- `slope(t−c/2, t) ≤ slope(t−c/2, t+1/m) ≤ slope(t, t+1/m)`
        have hb1 := (φbd (t - c / 2) ht3).2
        have hb2 := (φbd t htm).1
        have hlow : -1 / (c / 2) ≤ (H (Function.update P i' t) - H (Function.update P i' (t - c / 2))) / (c / 2) := by
          apply (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < c / 2)).mpr
          linarith [hb1, hb2]
        have hUeq' : uslope H m P i' t = (H (Function.update P i' (t + 1 / m)) - H (Function.update P i' t)) / (1 / m) := rfl
        have h6 : -2 / c = -1 / (c / 2) := by field_simp
        rw [h6]
        calc -1 / (c / 2) ≤ (H (Function.update P i' t) - H (Function.update P i' (t - c / 2))) / (c / 2) := hlow
          _ ≤ _ := le_trans ha2 ha3
      · -- `U t ≤ slope(t, t + c/2) ≤ 2/c`.
        have ha2 := hfP.secant_mono_aux2 htm ht2
          (x := t) (y := t + 1 / m) (z := t + c / 2) (by linarith) (by linarith)
        have e1 : t + 1 / m - t = 1 / m := by ring
        have e2 : t + c / 2 - t = c / 2 := by ring
        rw [e1, e2] at ha2
        have hb1 := (φbd (t + c / 2) ht2).2
        have hb2 := (φbd t htm).1
        have hup : (H (Function.update P i' (t + c / 2)) - H (Function.update P i' t)) / (c / 2) ≤ 1 / (c / 2) := by
          apply (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < c / 2)).mpr
          linarith [hb1, hb2]
        have h6 : 2 / c = 1 / (c / 2) := by field_simp
        rw [h6]
        exact le_trans ha2 hup
    -- The telescope: `U(B_{g−1}) − U(A_0) > g·δm/d`.
    set J := δ * m / d with hJdef
    have hJpos : 0 < J := by
      rw [hJdef]
      apply div_pos
      · exact mul_pos hδ hmR
      · exact_mod_cast hd
    have hInd : ∀ k : ℕ, ∀ hk : k < g,
        U (A ⟨0, hgpos⟩) + k * J ≤ U (A ⟨k, hk⟩) := by
      intro k
      induction k with
      | zero => intro hk; simp
      | succ k ih =>
        intro hk
        have hk' : k < g := by omega
        have h1 := ih hk'
        have hjump := (hfacts ⟨k, hk'⟩).2.2.2.2
        have hconn : U (B ⟨k, hk'⟩) ≤ U (A ⟨k + 1, hk⟩) := by
          apply hUmono
          · -- `B_k ∈ Ioo`
            have hb1 := (hfacts ⟨k, hk'⟩).1
            have hb2 := (hfacts ⟨k, hk'⟩).2.2.1
            apply hmemP ⟨k, hk'⟩
            rw [abs_le]
            constructor <;> linarith [hb1, hb2]
          · -- `A_{k+1} + 1/m ∈ Ioo`
            have ha1 := (hfacts ⟨k + 1, hk⟩).1
            have ha2 := (hfacts ⟨k + 1, hk⟩).2.1
            apply hmemP ⟨k + 1, hk⟩
            rw [abs_le]
            constructor <;> linarith [ha1, ha2]
          · -- `B_k ≤ A_{k+1}`
            have hb2 := (hfacts ⟨k, hk'⟩).2.2.1
            have ha1 := (hfacts ⟨k + 1, hk⟩).1
            have hg := hgap ⟨k, hk'⟩ ⟨k + 1, hk⟩ (by simp)
            have hg' : ((vv ⟨k, hk'⟩) i' + 2 * d : ℝ) / m ≤ (vv ⟨k + 1, hk⟩) i' / m := by
              apply div_le_div_of_nonneg_right _ hmR.le
              exact_mod_cast hg
            have hg'' : (vv ⟨k, hk'⟩) i' / m + (d : ℝ) / m
                ≤ (vv ⟨k + 1, hk⟩) i' / m - (d : ℝ) / m := by
              have h6 : ((vv ⟨k, hk'⟩) i' + 2 * d : ℝ) / m
                  = (vv ⟨k, hk'⟩) i' / m + 2 * (d : ℝ) / m := by
                push_cast; ring
              rw [h6] at hg'
              linarith
            linarith [hb2, ha1, hg'']
        have h7 : (k + 1 : ℝ) * J = k * J + J := by ring
        linarith [h1, hjump, hconn, h7]
    -- The final contradiction.
    have hfin : U (A ⟨0, hgpos⟩) + g * J < U (B ⟨g - 1, by omega⟩) := by
      have h1 := hInd (g - 1) (by omega)
      have hjump := (hfacts ⟨g - 1, by omega⟩).2.2.2.2
      have hg1 : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one]
      have h7 : (g : ℝ) * J = ((g - 1 : ℕ) : ℝ) * J + J := by rw [hg1]; ring
      linarith [h1, hjump, h7]
    have hcap : U (B ⟨g - 1, by omega⟩) - U (A ⟨0, hgpos⟩) ≤ 4 / c := by
      have hA0 : A ⟨0, hgpos⟩ ∈ Set.Ioo (-c / 2) (1 + c / 2) := by
        have ha1 := (hfacts ⟨0, hgpos⟩).1
        have ha2 := (hfacts ⟨0, hgpos⟩).2.1
        have hcm : (d : ℝ) / m < c / 2 := by
          have h5 : (d : ℝ) / m < c := by
            have h6 : (d : ℝ) / m ≤ 2 * (d : ℝ) / m :=
              div_le_div_of_nonneg_right (by linarith) hmR.le
            linarith [hc]
          linarith [h5]
        have hv0 : (0 : ℝ) ≤ (vv ⟨0, hgpos⟩) i' / m := by positivity
        have hv1 : (vv ⟨0, hgpos⟩) i' / m ≤ ((m : ℝ) - 1) / m := by
          apply div_le_div_of_nonneg_right _ hmR.le
          have h5 : (vv ⟨0, hgpos⟩) i' + 1 ≤ m := hI _ (hvvI ⟨0, hgpos⟩) i'
          have h6 : ((vv ⟨0, hgpos⟩) i' : ℝ) + 1 ≤ m := by exact_mod_cast h5
          linarith
        have h6 : ((m : ℝ) - 1) / m < 1 := by rw [div_lt_one hmR]; linarith
        constructor <;> linarith
      have hBg : B ⟨g - 1, by omega⟩ ∈ Set.Ioo (-c / 2) (1 + c / 2) := by
        have hb1 := (hfacts ⟨g - 1, by omega⟩).2.1
        have hb2 := (hfacts ⟨g - 1, by omega⟩).2.2.1
        have hcm : (d : ℝ) / m < c / 2 := by
          have h5 : (d : ℝ) / m < c := by
            have h6 : (d : ℝ) / m ≤ 2 * (d : ℝ) / m :=
              div_le_div_of_nonneg_right (by linarith) hmR.le
            linarith [hc]
          linarith [h5]
        have hv0 : (0 : ℝ) ≤ (vv ⟨g - 1, by omega⟩) i' / m := by positivity
        have hv1 : (vv ⟨g - 1, by omega⟩) i' / m ≤ ((m : ℝ) - 1) / m := by
          apply div_le_div_of_nonneg_right _ hmR.le
          have h5 : (vv ⟨g - 1, by omega⟩) i' + 1 ≤ m := hI _ (hvvI ⟨g - 1, by omega⟩) i'
          have h6 : ((vv ⟨g - 1, by omega⟩) i' : ℝ) + 1 ≤ m := by exact_mod_cast h5
          linarith
        have h6 : ((m : ℝ) - 1) / m + (d : ℝ) / m = 1 + ((d : ℝ) - 1) / m := by
          field_simp; ring
        have h7 : ((d : ℝ) - 1) / m < c / 2 := by
          have h8 : ((d : ℝ) - 1) / m < (d : ℝ) / m := by
            apply div_lt_div_of_pos_right hmR; linarith
          linarith
        constructor <;> linarith
      have h1 := (hUbound (A ⟨0, hgpos⟩) hA0).1
      have h2 := (hUbound (B ⟨g - 1, by omega⟩) hBg).2
      linarith
    -- `g · J ≥ 4/c`, contradicting `hfin` and `hcap`.
    have hgJ : (4 : ℝ) / c ≤ g * J := by
      have hgR : (I.card : ℝ) / (2 * d * (d - 1) * (m : ℝ) ^ (d - 2)) ≤ g := by
        have h1 : (I.card : ℝ) ≤ 2 * d * (d - 1) * (m : ℝ) ^ (d - 2) * g := by
          have h2 := hGI
          push_cast at h2 ⊢
          have h3 : (2 * d * (d - 1) * m ^ (d - 2) * G.card : ℝ)
              = 2 * (d : ℝ) * (d - 1) * (m : ℝ) ^ (d - 2) * g := by
            push_cast; ring
          linarith [h2, h3]
        rw [div_le_iff (by positivity : (0:ℝ) < 2 * d * (d - 1) * (m : ℝ) ^ (d - 2))]
        have h4 : (2 * (d : ℝ) * (d - 1) * (m : ℝ) ^ (d - 2)) * g
            = 2 * d * (d - 1) * (m : ℝ) ^ (d - 2) * g := by ring
        linarith [h1, h4]
      have hJeq : g * J = g * δ * m / d := by rw [hJdef]; ring
      have hstep : (I.card : ℝ) / (2 * d * (d - 1) * (m : ℝ) ^ (d - 2)) * (δ * m / d)
          = 2 * d ^ 2 / ((d - 1) * c) := by
        have hδI : (I.card : ℝ) * δ = 4 * (d : ℝ) ^ 4 * (m : ℝ) ^ ((d : ℤ) - 3) / c := by
          rw [hδdef]; field_simp; ring
        have hmp : (m : ℝ) ^ ((d : ℤ) - 3) = (m : ℝ) ^ (d - 2) / m := by
          have he : (d : ℤ) - 3 = ((d - 2 : ℕ) : ℤ) - 1 := by
            rw [Int.ofNat_sub (by omega : 2 ≤ d)]; push_cast; ring
          rw [he]
          rw [zpow_sub_one₀ (by positivity : (m : ℝ) ≠ 0)]
          rw [zpow_natCast]
        rw [hmp] at hδI
        -- multiply `hstep`-LHS out
        have hK : (0:ℝ) < 2 * d * (d - 1) * (m : ℝ) ^ (d - 2) := by positivity
        field_simp
        -- goal: |I|·δ·m·((d−1)·c) = 2d²·(2d(d−1)m^{d−2})·c ... evaluate
        nlinarith [hδI, hK]
      have hge : (2 : ℝ) * d ^ 2 / ((d - 1) * c) ≥ 4 / c := by
        rw [div_le_div_iff (by positivity : (0:ℝ) < (d - 1) * c) hc0]
        nlinarith [hc0, hd2]
      rw [hJeq]
      calc (4 : ℝ) / c ≤ 2 * d ^ 2 / ((d - 1) * c) := hge
        _ = (I.card : ℝ) / (2 * d * (d - 1) * (m : ℝ) ^ (d - 2)) * (δ * m / d) := hstep.symm
        _ ≤ g * (δ * m / d) := by gcongr
    linarith [hfin, hcap, hgJ]
  done

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
  sorry

end Nonaveraging
