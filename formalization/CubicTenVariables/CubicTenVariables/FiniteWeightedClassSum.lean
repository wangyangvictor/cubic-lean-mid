import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-! Finite weighted sums controlled by a majorant on each residue class. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteWeightedClassSum
open scoped BigOperators

/-- A common bound for every fiber sum transfers to arbitrary weights with
a nonnegative class majorant. The original weights need not be nonnegative. -/
theorem sum_mul_le {α β : Type*} [DecidableEq β]
    (E : Finset α) (B : Finset β) (tag : α → β)
    (a w : α → ℝ) (P : β → ℝ) (K : ℝ)
    (htag : ∀ x ∈ E, tag x ∈ B)
    (ha : ∀ x ∈ E, 0 ≤ a x)
    (hP : ∀ b ∈ B, 0 ≤ P b)
    (hmajor : ∀ x ∈ E, w x ≤ P (tag x))
    (hfiber : ∀ b ∈ B, (∑ x ∈ E.filter (fun x => tag x = b), a x) ≤ K) :
    (∑ x ∈ E, w x * a x) ≤ K * (∑ b ∈ B, P b) := by
  classical
  calc
    _ ≤ ∑ x ∈ E, P (tag x) * a x :=
      Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right (hmajor x hx) (ha x hx))
    _ = ∑ b ∈ B, ∑ x ∈ E.filter (fun x => tag x = b), P (tag x) * a x :=
      (Finset.sum_fiberwise_of_maps_to htag _).symm
    _ = ∑ b ∈ B, P b * (∑ x ∈ E.filter (fun x => tag x = b), a x) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ ∑ b ∈ B, P b * K :=
      Finset.sum_le_sum (fun b hb => mul_le_mul_of_nonneg_left (hfiber b hb) (hP b hb))
    _ = K * (∑ b ∈ B, P b) := by rw [← Finset.sum_mul, mul_comm]

/-- Enlarge a finite collection of modulus/frequency pairs to the full
product, with frequency as the outer summation variable. -/
theorem sum_subset_product_le {α β : Type*}
    (E : Finset (α × β)) (Q : Finset α) (V : Finset β) (g : α → β → ℝ)
    (hE : E ⊆ Q ×ˢ V) (hg : ∀ q ∈ Q, ∀ v ∈ V, 0 ≤ g q v) :
    (∑ x ∈ E, g x.1 x.2) ≤ ∑ v ∈ V, ∑ q ∈ Q, g q v := by
  classical
  calc
    _ ≤ ∑ x ∈ Q ×ˢ V, g x.1 x.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hE
      intro x hx _
      exact hg x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2
    _ = ∑ q ∈ Q, ∑ v ∈ V, g q v := Finset.sum_product _ _ _
    _ = _ := Finset.sum_comm

end CubicTenVariables.FiniteWeightedClassSum
