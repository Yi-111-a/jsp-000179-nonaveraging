import Nonaveraging.MaxSize

/-!
# Bosznay's lower-bound construction

The explicit construction of [Bo89] (see arXiv:2410.14624v2, §1):
for `q ≥ 2`, the set

    A_q = { i·q³ + i(i+1)/2 : 1 ≤ i ≤ q−1 } ⊆ [q⁴]

is non-averaging and has `q−1` elements, so `h(q⁴) ≥ q−1`.
Combined with monotonicity of `h` this yields `h(n) ≥ n^{1/4} − O(1)`.

The proof is a two-moment argument: if `a = n_j` were an average of a
`k`-element subset of `A_q ∖ {a}`, then reducing modulo `q³` (all correction
terms are `< q³` in absolute value) forces both `j = avg(indices)` and
`T_j = avg(T_i)` where `T_i = i(i+1)/2`; the variance identity then collapses
to `i = j` for every index used — a contradiction.
-/

open Finset

namespace Nonaveraging

/-- The triangular correction `T_i = i(i+1)/2`, packaged as `(i+1).choose 2`. -/
def tri (i : ℕ) : ℤ := ((i + 1).choose 2 : ℤ)

theorem tri_nonneg (i : ℕ) : 0 ≤ tri i := Nat.cast_nonneg _

theorem two_mul_tri (i : ℕ) : 2 * tri i = (i : ℤ) * (i + 1) := by
  have hdvd : (2 : ℕ) ∣ (i + 1) * i := by
    rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (i + 1), by rw [hk]; ring⟩
    · exact ⟨(k + 1) * i, by rw [hk]; ring⟩
  calc 2 * tri i = 2 * (((i + 1) * i / 2 : ℕ) : ℤ) := by
        rw [tri, Nat.choose_two_right, Nat.add_sub_cancel]
    _ = (((i + 1) * i / 2 * 2 : ℕ) : ℤ) := by push_cast; ring
    _ = (((i + 1) * i : ℕ) : ℤ) := by rw [Nat.div_mul_cancel hdvd]
    _ = (i : ℤ) * (i + 1) := by push_cast; ring

theorem tri_strictMono : StrictMono tri := by
  intro i j hij
  have hi := two_mul_tri i
  have hj := two_mul_tri j
  have hc : (i : ℤ) < j := by exact_mod_cast hij
  have hpos : (0 : ℤ) < ((j : ℤ) - i) * (i + j + 1) :=
    mul_pos (sub_pos.mpr hc) (by positivity)
  nlinarith

/-- The `i`-th term of Bosznay's construction: `n_i = i·q³ + T_i`. -/
def bosznayTerm (q i : ℕ) : ℤ := i * q ^ 3 + tri i

theorem bosznayTerm_strictMono (q : ℕ) : StrictMono (bosznayTerm q) := by
  intro i j hij
  have h1 : (i : ℤ) * q ^ 3 ≤ j * q ^ 3 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij.le) (by positivity)
  have h2 := tri_strictMono hij
  unfold bosznayTerm
  linarith

/-- Bosznay's set `A_q = {n_i : 1 ≤ i ≤ q−1}`. -/
def bosznay (q : ℕ) : Finset ℤ := (Finset.Icc 1 (q - 1)).image (bosznayTerm q)

theorem bosznay_card (q : ℕ) : (bosznay q).card = q - 1 := by
  rw [bosznay, Finset.card_image_of_injective _ (bosznayTerm_strictMono q).injective,
    Nat.card_Icc]
  omega

theorem bosznay_mem_Icc {q : ℕ} (hq : 1 ≤ q) :
    bosznay q ⊆ Finset.Icc 1 ((q ^ 4 : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Icc] at hi ⊢
  refine ⟨?_, ?_⟩
  · rw [← hix]
    have hq3 : (0 : ℤ) < (q : ℤ) ^ 3 := by positivity
    have hq3' : (1 : ℤ) ≤ (q : ℤ) ^ 3 := one_le_pow₀ (by exact_mod_cast hq)
    have hi1 : (1 : ℤ) ≤ i := by exact_mod_cast hi.1
    have hprod := mul_nonneg (sub_nonneg.mpr hi1) hq3.le
    have := tri_nonneg i
    unfold bosznayTerm
    nlinarith
  · rw [← hix]
    have hi1 : (1 : ℤ) ≤ i := by exact_mod_cast hi.1
    have hi2 : i ≤ q - 1 := hi.2
    have hi2' : (i : ℤ) ≤ (q : ℤ) - 1 := by omega
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
    have h1 : (i : ℤ) * q ^ 3 ≤ (q - 1 : ℤ) * q ^ 3 :=
      mul_le_mul_of_nonneg_right hi2' (by positivity)
    have htri : tri i ≤ (i : ℤ) ^ 2 := by
      have h := two_mul_tri i
      nlinarith [mul_nonneg (sub_nonneg.mpr hi1) (show (0 : ℤ) ≤ i by linarith)]
    have hsqi : (i : ℤ) ^ 2 ≤ ((q : ℤ) - 1) ^ 2 := by
      have h := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ) - 1 - i by omega)
        (show (0 : ℤ) ≤ (q : ℤ) - 1 + i by linarith)
      nlinarith
    have hcast : ((q ^ 4 : ℕ) : ℤ) = (q : ℤ) ^ 4 := by push_cast; ring
    have hqq : (q - 1 : ℤ) * q ^ 3 + ((q : ℤ) - 1) ^ 2 ≤ (q : ℤ) ^ 4 := by
      have h := mul_nonneg (sq_nonneg (q : ℤ)) (sub_nonneg.mpr hq1)
      nlinarith
    unfold bosznayTerm
    rw [hcast]
    nlinarith

/-- **Bosznay's theorem**: `A_q` is non-averaging for `q ≥ 2`. -/
theorem bosznay_nonAveraging {q : ℕ} (hq : 2 ≤ q) : NonAveraging (bosznay q) := by
  intro a ha S hS hne havg
  obtain ⟨j, hjI, hja⟩ := Finset.mem_image.mp ha
  set I := (Finset.Icc 1 (q - 1)).filter (fun i ↦ bosznayTerm q i ∈ S) with hI
  have hinj : Set.InjOn (bosznayTerm q) I :=
    Set.injOn_of_injective (bosznayTerm_strictMono q).injective
  have hSI : S = I.image (bosznayTerm q) := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hx' := hS hx
      rw [Finset.mem_erase] at hx'
      obtain ⟨i, hiI, hix⟩ := Finset.mem_image.mp hx'.2
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiI, hix ▸ hx⟩, hix⟩
    · intro x hx
      obtain ⟨i, hiI, hix⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at hiI
      exact hix ▸ hiI.2
  have hcardS : S.card = I.card := by
    rw [hSI, Finset.card_image_of_injOn hinj]
  have hsumS : S.sum id = ∑ i ∈ I, bosznayTerm q i := by
    rw [hSI, Finset.sum_image hinj]
    simp only [id_eq]
  have hIne : I.Nonempty := by
    have : (I.image (bosznayTerm q)).Nonempty := hSI ▸ hne
    exact Finset.image_nonempty.mp this
  rw [hcardS, hsumS, ← hja, nsmul_eq_mul] at havg
  set k : ℤ := (I.card : ℤ) with hk
  have hk1 : (1 : ℤ) ≤ k := by
    rw [hk]
    exact_mod_cast (Finset.card_pos.mpr hIne)
  have hk_le : k ≤ (q : ℤ) - 1 := by
    have hc : I.card ≤ q - 1 := by
      calc I.card ≤ (Finset.Icc 1 (q - 1)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = q - 1 := by rw [Nat.card_Icc]; omega
    rw [hk]
    omega
  -- expand `havg` into the two-moment system
  set S1 : ℤ := ∑ i ∈ I, (i : ℤ) with hS1
  set S2 : ℤ := ∑ i ∈ I, tri i with hS2
  have hsum : ∑ i ∈ I, bosznayTerm q i = S1 * (q : ℤ) ^ 3 + S2 := by
    rw [hS1, hS2]
    simp only [bosznayTerm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hsum] at havg
  -- `q³ (k j − S1) = S2 − k T_j`
  have hkey : (q : ℤ) ^ 3 * (k * j - S1) = S2 - k * tri j := by
    have := havg
    unfold bosznayTerm at this
    linear_combination this
  -- every `T_i` in the sum lies in `[0, T_{q-1}]`
  have hTmax : ∀ i ∈ I, 0 ≤ tri i ∧ tri i ≤ tri (q - 1) := by
    intro i hi
    have hiI := (Finset.mem_filter.mp hi).1
    rw [Finset.mem_Icc] at hiI
    exact ⟨tri_nonneg i, (tri_strictMono.monotone) hiI.2⟩
  have hS2bd : 0 ≤ S2 ∧ S2 ≤ k * tri (q - 1) := by
    refine ⟨Finset.sum_nonneg fun i hi ↦ (hTmax i hi).1, ?_⟩
    calc S2 ≤ ∑ _ ∈ I, tri (q - 1) := Finset.sum_le_sum fun i hi ↦ (hTmax i hi).2
      _ = k * tri (q - 1) := by rw [Finset.sum_const, nsmul_eq_mul, hk]
  have hkTbd : 0 ≤ k * tri j ∧ k * tri j ≤ k * tri (q - 1) := by
    have hj : tri j ≤ tri (q - 1) := by
      apply tri_strictMono.monotone
      rw [Finset.mem_Icc] at hjI
      exact hjI.2
    exact ⟨mul_nonneg (by linarith) (tri_nonneg j),
      mul_le_mul_of_nonneg_left hj (by linarith)⟩
  -- `|S2 − k T_j| < q³`, forcing `k j = S1`
  have hbound : |S2 - k * tri j| < (q : ℤ) ^ 3 := by
    have hqT : (q - 1 : ℤ) * tri (q - 1) < (q : ℤ) ^ 3 := by
      have h2 := two_mul_tri (q - 1)
      have hq1' : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := Nat.cast_sub (by omega)
      rw [hq1'] at h2
      have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
      have h3 : 2 * ((q - 1 : ℤ) * tri (q - 1)) = (q - 1 : ℤ) ^ 2 * q := by
        linear_combination (q - 1 : ℤ) * h2
      have h4 := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ) - 1 by linarith)
        (sq_nonneg ((q : ℤ) - 1))
      have h5 := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ) by linarith)
        (show (0 : ℤ) ≤ (q : ℤ) - 1 by linarith)
      nlinarith
    have hle : |S2 - k * tri j| ≤ k * tri (q - 1) := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hS2bd.1, hS2bd.2, hkTbd.1, hkTbd.2]
    calc |S2 - k * tri j| ≤ k * tri (q - 1) := hle
      _ ≤ (q - 1 : ℤ) * tri (q - 1) :=
          mul_le_mul_of_nonneg_right hk_le (tri_nonneg _)
      _ < (q : ℤ) ^ 3 := hqT
  have hz : k * j - S1 = 0 := by
    by_contra hz
    have hx1 : (1 : ℤ) ≤ |k * j - S1| := by
      have : (0 : ℤ) < |k * j - S1| := abs_pos.mpr hz
      omega
    have : (q : ℤ) ^ 3 ≤ |(q : ℤ) ^ 3 * (k * j - S1)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (q : ℤ) ^ 3)]
      calc (q : ℤ) ^ 3 = (q : ℤ) ^ 3 * 1 := by ring
        _ ≤ (q : ℤ) ^ 3 * |k * j - S1| :=
            mul_le_mul_of_nonneg_left hx1 (by positivity)
    rw [hkey] at this
    linarith [hbound]
  have hkj : k * j = S1 := sub_eq_zero.mp hz
  have hS2' : S2 = k * tri j := by
    rw [hz, mul_zero] at hkey
    linarith
  -- variance collapse: `∑ (i − j)² = 0`
  have hsumsq : ∑ i ∈ I, (i : ℤ) ^ 2 = k * j ^ 2 := by
    have e2 : 2 * S2 = ∑ i ∈ I, ((i : ℤ) * (i + 1)) := by
      rw [hS2, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [two_mul_tri]
    have e3 : (∑ i ∈ I, ((i : ℤ) * (i + 1))) = ∑ i ∈ I, (i : ℤ) ^ 2 + S1 := by
      rw [hS1, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [e3] at e2
    have e4 : 2 * (k * tri j) = k * j ^ 2 + k * j := by
      rw [show 2 * (k * tri j) = k * (2 * tri j) by ring, two_mul_tri]
      ring
    rw [hS2'] at e2
    linarith [hkj]
  have hvar : ∑ i ∈ I, ((i : ℤ) - j) ^ 2 = 0 := by
    have e1 : ∑ i ∈ I, ((i : ℤ) - j) ^ 2 = ∑ i ∈ I, (i : ℤ) ^ 2 - 2 * j * S1 + k * j ^ 2 := by
      have hsq : ∀ i ∈ I, ((i : ℤ) - j) ^ 2 = (i : ℤ) ^ 2 - 2 * j * i + j ^ 2 :=
        fun i _ ↦ by ring
      rw [Finset.sum_congr rfl hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← hS1, ← hk]
    rw [e1, hsumsq, ← hkj]
    ring
  have hall : ∀ i ∈ I, ((i : ℤ) - j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg _).mp hvar
  obtain ⟨i₀, hi₀⟩ := hIne
  have hij : (i₀ : ℤ) = j := by
    have := hall i₀ hi₀
    rw [sq_eq_zero_iff, sub_eq_zero] at this
    exact this
  have hi₀j : i₀ = j := by exact_mod_cast hij
  subst hi₀j
  have hmem : bosznayTerm q i₀ ∈ S := (Finset.mem_filter.mp hi₀).2
  have hnerase := Finset.mem_erase.mp (hS hmem)
  exact hnerase.1 hja

/-- Bosznay's bound: `h(q⁴) ≥ q − 1`. -/
theorem h_ge_quarter {q : ℕ} (hq : 2 ≤ q) : q - 1 ≤ h (q ^ 4) := by
  have hb := card_le_h (n := q ^ 4) (bosznay_mem_Icc (by omega)) (bosznay_nonAveraging hq)
  rwa [bosznay_card] at hb

/-- For every `n`, `h n ≥ ⌊√⌊√n⌋⌋ − 1`. -/
theorem h_ge_sqrt_sqrt_sub_one (n : ℕ) : n.sqrt.sqrt - 1 ≤ h n := by
  set q := n.sqrt.sqrt with hqdef
  have hq4 : q ^ 4 ≤ n := by
    have h1 : q * q ≤ n.sqrt := Nat.sqrt_le _
    have h2 : n.sqrt * n.sqrt ≤ n := Nat.sqrt_le _
    calc q ^ 4 = (q * q) * (q * q) := by ring
      _ ≤ n.sqrt * n.sqrt := Nat.mul_le_mul h1 h1
      _ ≤ n := h2
  by_cases hq : 2 ≤ q
  · exact (h_ge_quarter hq).trans (h_mono hq4)
  · have : q - 1 = 0 := by omega
    rw [this]
    exact Nat.zero_le _

end Nonaveraging
