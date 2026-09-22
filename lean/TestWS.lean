import Nonaveraging.Defs

open Finset Asymptotics Filter

namespace Nonaveraging

structure GAP (ℓ d : ℕ) where
  base : Fin ℓ → ℤ
  step : Fin d → (Fin ℓ → ℤ)
  width : Fin d → ℕ

namespace GAP

variable {ℓ d : ℕ} (P : GAP ℓ d)

def coeffs : Finset (Fin d → ℕ) :=
  Finset.univ.image fun n : Π i, Fin (P.width i) ↦ fun i ↦ (n i : ℕ)

def eval (n : Fin d → ℕ) : Fin ℓ → ℤ :=
  P.base + ∑ i, (n i : ℤ) • P.step i

def toFinset : Finset (Fin ℓ → ℤ) := P.coeffs.image P.eval

def Proper : Prop := Set.InjOn P.eval P.coeffs

def translate (t : Fin ℓ → ℤ) : GAP ℓ d := ⟨t + P.base, P.step, P.width⟩

def widthScale (P : GAP ℓ d) (k : ℕ) : GAP ℓ d :=
  ⟨P.base, P.step, fun i ↦ k * P.width i⟩

@[simp] theorem widthScale_base (P : GAP ℓ d) (k : ℕ) :
    (P.widthScale k).base = P.base := rfl

@[simp] theorem widthScale_step (P : GAP ℓ d) (k : ℕ) :
    (P.widthScale k).step = P.step := rfl

@[simp] theorem widthScale_width (P : GAP ℓ d) (k : ℕ) :
    (P.widthScale k).width = fun i ↦ k * P.width i := rfl

theorem widthScale_eval (P : GAP ℓ d) (k : ℕ) (n : Fin d → ℕ) :
    (P.widthScale k).eval n = P.eval n := rfl

theorem widthScale_translate (P : GAP ℓ d) (k : ℕ) (t : Fin ℓ → ℤ) :
    (P.widthScale k).translate t = (P.translate t).widthScale k := rfl

theorem widthScale_one (P : GAP ℓ d) : P.widthScale 1 = P := by
  show GAP.mk P.base P.step (fun i ↦ 1 * P.width i) =
    GAP.mk P.base P.step P.width
  congr 1
  funext i
  exact one_mul _

theorem widthScale_widthScale (P : GAP ℓ d) (j k : ℕ) :
    (P.widthScale j).widthScale k = P.widthScale (k * j) := by
  show GAP.mk P.base P.step (fun i ↦ k * (j * P.width i)) =
    GAP.mk P.base P.step (fun i ↦ (k * j) * P.width i)
  congr 1
  funext i
  exact (mul_assoc k j (P.width i)).symm

theorem coeffs_subset_widthScale (P : GAP ℓ d) {k : ℕ} (hk : 1 ≤ k) :
    P.coeffs ⊆ (P.widthScale k).coeffs := by
  intro n hn
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hn
  refine Finset.mem_image.mpr ⟨fun i ↦ ⟨(m i : ℕ), ?_⟩, Finset.mem_univ _, ?_⟩
  · exact lt_of_lt_of_le (m i).isLt (Nat.le_mul_of_pos_left _ hk)
  · rw [← hm]
    funext i
    rfl

theorem toFinset_subset_widthScale (P : GAP ℓ d) {k : ℕ} (hk : 1 ≤ k) :
    P.toFinset ⊆ (P.widthScale k).toFinset := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨n, P.coeffs_subset_widthScale hk hn, rfl⟩

theorem Proper.of_widthScale {P : GAP ℓ d} {k : ℕ} (hk : 1 ≤ k)
    (h : (P.widthScale k).Proper) : P.Proper :=
  h.mono (P.coeffs_subset_widthScale hk)

end GAP
end Nonaveraging
