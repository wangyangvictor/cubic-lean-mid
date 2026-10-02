import CubicTenVariables.CountingEndpoint
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Elementary lattice counting through an integral linear projection.

The matrix, the finite set of lattice points, and each projection fiber are
literal objects. The only counting hypothesis is the displayed bound on those
finite fibers. No geometric projection theorem or Hessian rank bound is assumed
or proved here.
-/

namespace CubicTenVariables
open scoped BigOperators

/-- A concrete coefficient bound for an integral matrix: the sum of the
absolute values of all its entries. It also bounds every row's absolute sum. -/
def integerProjectionCoefficientBound {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) : ℕ :=
  ∑ i, ∑ j, (A i j).natAbs

/-- The exact cardinality of the actual integer box, including its boundary. -/
@[simp] theorem card_integerBox (n B : ℕ) :
    (integerBox n B).card = (2 * B + 1) ^ n := by
  have hinterval : (Finset.Icc (-(B : ℤ)) (B : ℤ)).card = 2 * B + 1 := by
    rw [Int.card_Icc]
    have he : (B : ℤ) + 1 - -(B : ℤ) = ((2 * B + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [he, Int.toNat_natCast]
  simp [integerBox, Fintype.card_piFinset, hinterval]

theorem integerProjection_row_sum_le {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (i : Fin r) :
    (∑ j, |A i j|) ≤ (integerProjectionCoefficientBound A : ℤ) := by
  have hi : (∑ j, (A i j).natAbs) ≤ integerProjectionCoefficientBound A := by
    unfold integerProjectionCoefficientBound
    exact Finset.single_le_sum (f := fun k => ∑ j, (A k j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hi' := (Nat.cast_le (α := ℤ)).mpr hi
  simpa only [Nat.cast_sum, Int.natCast_natAbs] using hi'

/-- Every coordinate of the projected point lies in the explicitly bounded
interval. The bound is valid also for zero-dimensional matrices and radius 0. -/
theorem integerProjection_mem_integerBox {r n B : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) {x : Fin n → ℤ}
    (hx : x ∈ integerBox n B) :
    A.mulVec x ∈ integerBox r (integerProjectionCoefficientBound A * B) := by
  rw [mem_integerBox] at hx ⊢
  intro i
  calc
    |A.mulVec x i| = |∑ j, A i j * x j| := rfl
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |x j| := by simp only [abs_mul]
    _ ≤ ∑ j, |A i j| * (B : ℤ) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * (B : ℤ) := (Finset.sum_mul ..).symm
    _ ≤ (integerProjectionCoefficientBound A : ℤ) * (B : ℤ) :=
      mul_le_mul_of_nonneg_right (integerProjection_row_sum_le A i) (Nat.cast_nonneg B)
    _ = ((integerProjectionCoefficientBound A * B : ℕ) : ℤ) := by push_cast; rfl

/-- The actual image of any finite subset of an integer box lies in the
explicit target box. -/
theorem integerProjection_image_subset {r n B : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (S : Finset (Fin n → ℤ))
    (hS : S ⊆ integerBox n B) :
    S.image A.mulVec ⊆ integerBox r (integerProjectionCoefficientBound A * B) := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact integerProjection_mem_integerBox A (hS hx)

/-- Bounded fibers of an integral projection give a literal finite lattice
count, with an explicit constant determined by its matrix. -/
theorem card_le_integerProjection_bound {r n B M : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (S : Finset (Fin n → ℤ))
    (hS : S ⊆ integerBox n B)
    (hfiber : ∀ y : Fin r → ℤ, (S.filter fun x => A.mulVec x = y).card ≤ M) :
    S.card ≤ M * (2 * integerProjectionCoefficientBound A * B + 1) ^ r := by
  classical
  have h := Finset.card_le_mul_card_image_of_maps_to
    (fun x hx => integerProjection_mem_integerBox A (hS hx)) M
    (fun y _ => hfiber y)
  simpa only [card_integerBox, Nat.mul_assoc] using h

end CubicTenVariables
