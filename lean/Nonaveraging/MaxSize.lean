import Nonaveraging.Defs

/-!
# `h n`: the maximum size of a non-averaging subset of `[n]`

The Erdős–Straus function `h(n)`: the largest cardinality of a non-averaging
subset of `{1, …, n} ⊆ ℤ`.
-/

open Finset

namespace Nonaveraging

/-- `h n` = maximum cardinality of a non-averaging subset of `{1,…,n} ⊆ ℤ`. -/
noncomputable def h (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 (n : ℤ)).powerset.filter NonAveraging).sup Finset.card

theorem h_le (n : ℕ) : h n ≤ n := by
  classical
  unfold h
  apply Finset.sup_le
  intro A hA
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  calc A.card ≤ (Finset.Icc 1 (n : ℤ)).card := Finset.card_le_card hA.1
    _ = n := by simp [Int.card_Icc]

/-- Any concrete non-averaging subset of `[n]` gives a lower bound on `h n`. -/
theorem card_le_h {n : ℕ} {A : Finset ℤ} (hsub : A ⊆ Finset.Icc 1 (n : ℤ))
    (hA : NonAveraging A) : A.card ≤ h n := by
  classical
  unfold h
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hA⟩)

theorem h_mono : Monotone h := by
  intro m n hmn
  classical
  unfold h
  apply Finset.sup_le
  intro A hA
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  apply Finset.le_sup
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hA.1.trans (Finset.Icc_subset_Icc_right (by exact_mod_cast hmn)), hA.2⟩

/-- The maximum is attained: some non-averaging `A ⊆ [n]` has `A.card = h n`. -/
theorem exists_nonAveraging_card_eq (n : ℕ) :
    ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 (n : ℤ) ∧ NonAveraging A ∧ A.card = h n := by
  classical
  set F := (Finset.Icc 1 (n : ℤ)).powerset.filter NonAveraging with hF
  have hne : F.Nonempty := ⟨∅, by simp [hF, nonAveraging_empty]⟩
  have him : (F.image Finset.card).Nonempty := hne.image _
  have hmaxsup : (F.image Finset.card).max' him = F.sup Finset.card := by
    apply le_antisymm
    · obtain ⟨A', hA', hA'eq⟩ := Finset.mem_image.mp (Finset.max'_mem _ him)
      rw [← hA'eq]
      exact Finset.le_sup hA'
    · apply Finset.sup_le
      intro A' hA'
      exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hA')
  obtain ⟨A, hAF, hcard⟩ : ∃ A ∈ F, A.card = (F.image Finset.card).max' him :=
    Finset.mem_image.mp (Finset.max'_mem _ him)
  refine ⟨A, ?_, ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_powerset] at hAF
    exact hAF.1
  · rw [Finset.mem_filter] at hAF
    exact hAF.2
  · unfold h
    rw [← hF, hcard, hmaxsup]

end Nonaveraging
