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
  sorry

end Nonaveraging
