import Nonaveraging.ConvexPosition
import Nonaveraging.GeoNumbers

open Finset MeasureTheory

namespace Nonaveraging

namespace GAP

variable {ℓ d : ℕ}

theorem mem_subsetSumsL {A : Finset (Fin ℓ → ℤ)} {x : Fin ℓ → ℤ} :
    x ∈ GAP.subsetSumsL A ↔ ∃ S ⊆ A, S.sum id = x := by
  simp only [subsetSumsL, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, hS, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, hS, rfl⟩

theorem subsetSumsL_mono {S T : Finset (Fin ℓ → ℤ)} (h : S ⊆ T) :
    GAP.subsetSumsL S ⊆ GAP.subsetSumsL T := by
  intro x hx
  rw [mem_subsetSumsL] at hx ⊢
  obtain ⟨S', hS', rfl⟩ := hx
  exact ⟨S', hS'.trans h, rfl⟩

/-- For disjoint `S T`, subset sums split: `Σ(S) + Σ(T) ⊆ Σ(S ∪ T)`. -/
theorem subsetSumsL_add {S T : Finset (Fin ℓ → ℤ)}
    (hdisj : Disjoint S T) {u v : Fin ℓ → ℤ}
    (hu : u ∈ GAP.subsetSumsL S) (hv : v ∈ GAP.subsetSumsL T) :
    u + v ∈ GAP.subsetSumsL (S ∪ T) := by
  rw [mem_subsetSumsL] at hu hv ⊢
  obtain ⟨S', hS', rfl⟩ := hu
  obtain ⟨T', hT', rfl⟩ := hv
  refine ⟨S' ∪ T', Finset.union_subset (hS'.trans Finset.subset_union_left)
    (hT'.trans Finset.subset_union_right), ?_⟩
  rw [Finset.sum_union (hdisj.mono hS' hT')]

/-- The negated GAP `−P = {−b − Σ nᵢ sᵢ}` (same widths). -/
def neg (P : GAP ℓ d) : GAP ℓ d := ⟨−P.base, fun i ↦ −P.step i, P.width⟩

theorem eval_neg (P : GAP ℓ d) (n : Fin d → ℕ) :
    P.neg.eval n = −P.eval n := by
  show (−P.base) + ∑ i, (n i : ℤ) • (−P.step i)
      = −(P.base + ∑ i, (n i : ℤ) • P.step i)
  simp [smul_neg]

theorem coeffs_neg (P : GAP ℓ d) : P.neg.coeffs = P.coeffs := rfl

theorem toFinset_neg (P : GAP ℓ d) :
    P.neg.toFinset = P.toFinset.image Neg.neg := by
  show (P.neg.coeffs.image P.neg.eval) = (P.coeffs.image P.eval).image Neg.neg
  rw [coeffs_neg, Finset.image_image]
  exact Finset.image_congr fun n _ ↦ eval_neg P n

theorem proper_neg {P : GAP ℓ d} : P.neg.Proper ↔ P.Proper := by
  unfold GAP.Proper
  rw [coeffs_neg]
  constructor
  · intro h n hn m hm hnm
    apply h hn hm
    rw [eval_neg, eval_neg, hnm]
  · intro h n hn m hm hnm
    apply h hn hm
    rw [eval_neg, eval_neg] at hnm
    exact neg_injective hnm

theorem translate_neg (P : GAP ℓ d) (t : Fin ℓ → ℤ) :
    P.neg.translate (−t) = (P.translate t).neg := by
  unfold GAP.translate neg
  congr 1
  · funext i; simp
  · funext i; rfl

theorem smul_neg (P : GAP ℓ d) (k : ℤ) : k • P.neg = (k • P).neg := by
  unfold HSMul.hSMul instHSMul SMul.smul instSMul GAP.smul neg
  simp [smul_neg]

theorem subsetSumsL_neg {A : Finset (Fin ℓ → ℤ)} :
    GAP.subsetSumsL (A.image Neg.neg) = (GAP.subsetSumsL A).image Neg.neg := by
  ext x
  rw [mem_subsetSumsL, Finset.mem_image]
  constructor
  · rintro ⟨S', hS', rfl⟩
    refine ⟨(S'.image Neg.neg).sum id, ?_, ?_⟩
    · rw [mem_subsetSumsL]
      refine ⟨S'.image Neg.neg, ?_, rfl⟩
      intro a ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      have hy' : y ∈ A.image Neg.neg := hS' hy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy'
      rw [← hzy, neg_neg]
      exact hz
    · rw [Finset.sum_image (fun x _ y _ h ↦ neg_injective h)]
      show (∑ x ∈ S', id (−x)) = -_
      simp [id_eq, Finset.sum_neg_distrib]
  · rintro ⟨v, hv, hvx⟩
    rw [mem_subsetSumsL] at hv
    obtain ⟨T, hT, rfl⟩ := hv
    refine ⟨T.image Neg.neg, Finset.image_subset_image hT, ?_⟩
    rw [Finset.sum_image (fun x _ y _ h ↦ neg_injective h)]
    show (∑ x ∈ T, id (−x)) = x
    simp [id_eq, Finset.sum_neg_distrib]
    exact hvx

end GAP

end Nonaveraging
