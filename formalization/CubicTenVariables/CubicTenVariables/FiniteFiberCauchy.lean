import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite Cauchy--Schwarz after grouping a weighted sum by its actual
fibers. No estimate for individual fibers, surjectivity, or positivity
of the complex weights is assumed. -/

noncomputable section
namespace CubicTenVariables.FiniteFiberCauchy
open scoped BigOperators

/-- Exact grouping of a residue-dependent weight, for any finite map. -/
theorem weighted_sum_eq_fiber_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (π : α → β) (w : β → ℂ) (f : α → ℂ) :
    (∑ x, w (π x) * f x) =
      ∑ b, w b * ∑ x, if π x = b then f x else 0 := by
  classical
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- The squared weighted sum is bounded by the weight mass times the
sum of squared fiber sums. Empty fibers and arbitrary complex weights
are included. -/
theorem norm_weighted_sum_sq_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (π : α → β) (w : β → ℂ) (f : α → ℂ) :
    ‖∑ x, w (π x) * f x‖ ^ 2 ≤
      (∑ b, ‖w b‖ ^ 2) * ∑ b, ‖∑ x, if π x = b then f x else 0‖ ^ 2 := by
  classical
  rw [weighted_sum_eq_fiber_sum]
  calc
    _ ≤ (∑ b, ‖w b‖ * ‖∑ x, if π x = b then f x else 0‖)^2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _
      simpa only [norm_mul] using norm_sum_le Finset.univ
        (fun b => w b * ∑ x, if π x = b then f x else 0)
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun b => ‖w b‖) (fun b => ‖∑ x, if π x = b then f x else 0‖)

end CubicTenVariables.FiniteFiberCauchy
