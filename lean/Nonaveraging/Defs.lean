import Mathlib

/-!
# Non-averaging sets: definition and basic API

`A ⊆ ℤ` is *non-averaging* if no element of `A` is the average of a nonempty
subset of the remaining elements.  Equivalently `A` avoids solutions in
distinct variables to `k·x₀ = x₁ + ⋯ + xₖ`.

Reference: arXiv:2410.14624v2, §1.
-/

open Finset

namespace Nonaveraging

variable {α : Type*} [DecidableEq α] [AddCommGroup α]
variable {A B : Finset α} {a : α} {n : ℕ}

/-- A finset `A` of integers is *non-averaging* if no `a ∈ A` satisfies
`|S|·a = ∑_{x ∈ S} x` for a nonempty `S ⊆ A ∖ {a}`.  (This is the
cleared-denominator form of "`a` is the average of `S`", stated for an
arbitrary additive group.) -/
def NonAveraging (A : Finset α) : Prop :=
  ∀ a ∈ A, ∀ S : Finset α, S ⊆ A.erase a → S.Nonempty → S.card • a ≠ S.sum id

theorem nonAveraging_empty : NonAveraging (∅ : Finset α) :=
  fun _ ha ↦ absurd ha (Finset.notMem_empty _)

theorem nonAveraging_singleton (x : α) : NonAveraging {x} := by
  rintro a ha S hS ⟨b, hb⟩
  rw [Finset.mem_singleton] at ha
  subst ha
  rw [Finset.erase_singleton] at hS
  exact absurd (hS hb) (Finset.notMem_empty b)

/-- A subset of a non-averaging set is non-averaging. -/
theorem NonAveraging.mono (hAB : B ⊆ A) (hA : NonAveraging A) : NonAveraging B :=
  fun a ha S hS hne ↦
    hA a (hAB ha) S (hS.trans (Finset.erase_subset_erase _ hAB)) hne

/-- The set of subset sums of `A`; `0` arises from the empty subset. -/
def subsetSums (A : Finset α) : Finset α := A.powerset.image (·.sum id)

theorem mem_subsetSums {x : α} : x ∈ subsetSums A ↔ ∃ S ⊆ A, S.sum id = x := by
  simp [subsetSums]

theorem zero_mem_subsetSums (A : Finset α) : (0 : α) ∈ subsetSums A :=
  mem_subsetSums.mpr ⟨∅, Finset.empty_subset _, by simp⟩

/-- The Erdős–Straus observation (equation (1) of the paper), in usable form:
if `A` is non-averaging, `a ∈ A` and `B₁, B₂ ⊆ A ∖ {a}` are disjoint, then a
common subset sum of `B₁ − a` and `a − B₂` must be zero. -/
theorem NonAveraging.subsetSum_eq_zero (hA : NonAveraging A) (ha : a ∈ A)
    {B₁ B₂ : Finset α} (h₁ : B₁ ⊆ A.erase a) (h₂ : B₂ ⊆ A.erase a)
    (hdisj : Disjoint B₁ B₂)
    (hsum : ∑ x ∈ B₁, (x - a) = ∑ y ∈ B₂, (a - y)) :
    ∑ x ∈ B₁, (x - a) = 0 := by
  by_contra hne
  have hne₁ : B₁.Nonempty := by
    rcases B₁.eq_empty_or_nonempty with h | h
    · simp [h] at hne
    · exact h
  have hne₂ : B₂.Nonempty := by
    rcases B₂.eq_empty_or_nonempty with h | h
    · simp [h] at hsum hne
      exact absurd hsum hne
    · exact h
  have e1 : ∑ x ∈ B₁, (x - a) = ∑ x ∈ B₁, x - B₁.card • a := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
  have e2 : ∑ y ∈ B₂, (a - y) = B₂.card • a - ∑ y ∈ B₂, y := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
  have hSsub : B₁ ∪ B₂ ⊆ A.erase a := Finset.union_subset h₁ h₂
  have hSne : (B₁ ∪ B₂).Nonempty := hne₁.mono Finset.subset_union_left
  have key : (B₁ ∪ B₂).card • a = ∑ x ∈ B₁ ∪ B₂, x := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.sum_union hdisj, add_nsmul]
    have hsum' : ∑ x ∈ B₁, x - B₁.card • a = B₂.card • a - ∑ y ∈ B₂, y := by
      rw [← e1, ← e2]; exact hsum
    calc B₁.card • a + B₂.card • a
        = (B₂.card • a - ∑ y ∈ B₂, y) + B₁.card • a + ∑ y ∈ B₂, y := by abel
      _ = (∑ x ∈ B₁, x - B₁.card • a) + B₁.card • a + ∑ y ∈ B₂, y := by rw [← hsum']
      _ = ∑ x ∈ B₁, x + ∑ y ∈ B₂, y := by abel
  exact hA a ha _ hSsub hSne key

/-- Specialization to `ℤ`: the average condition in multiplicative form. -/
theorem nonAveraging_int_iff (A : Finset ℤ) :
    NonAveraging A ↔
      ∀ a ∈ A, ∀ S : Finset ℤ, S ⊆ A.erase a → S.Nonempty →
        (S.card : ℤ) * a ≠ S.sum id := by
  simp [NonAveraging]

end Nonaveraging
