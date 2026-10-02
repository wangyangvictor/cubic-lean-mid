import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Finite nonnegative mass decomposition into the four rank ranges
needed by the ten-variable singular-root estimate. -/

namespace CubicTenVariables.FiniteRankMass
open scoped BigOperators

/-- The last class is harmlessly bounded using the size of the entire
set. All hypotheses of this finite helper are supplied internally in its
cubic application. -/
theorem sum_le_four_rank_classes {α : Type*} (s : Finset α)
    (rank mass : α → ℕ) (b₀ b₂ b₃ b₄ : ℕ)
    (h₀ : ∀ x ∈ s, rank x ≤ 1 → mass x ≤ b₀)
    (h₂ : ∀ x ∈ s, rank x = 2 → mass x ≤ b₂)
    (h₃ : ∀ x ∈ s, rank x = 3 → mass x ≤ b₃)
    (h₄ : ∀ x ∈ s, 4 ≤ rank x → mass x ≤ b₄) :
    (∑ x ∈ s, mass x) ≤
      (s.filter (fun x => rank x ≤ 1)).card*b₀ +
      (s.filter (fun x => rank x = 2)).card*b₂ +
      (s.filter (fun x => rank x = 3)).card*b₃ + s.card*b₄ := by
  classical
  have hpoint : ∀ x ∈ s, mass x ≤
      (if rank x ≤ 1 then b₀ else 0) +
      (if rank x = 2 then b₂ else 0) +
      (if rank x = 3 then b₃ else 0) + b₄ := by
    intro x hx
    by_cases hr₀ : rank x ≤ 1
    · have hm := h₀ x hx hr₀
      split_ifs <;> omega
    by_cases hr₂ : rank x = 2
    · have hm := h₂ x hx hr₂
      split_ifs <;> omega
    by_cases hr₃ : rank x = 3
    · have hm := h₃ x hx hr₃
      split_ifs; omega
    · have hm := h₄ x hx (by omega)
      simpa only [if_neg hr₀, if_neg hr₂, if_neg hr₃, zero_add] using hm
  calc
    _ ≤ ∑ x ∈ s, ((if rank x ≤ 1 then b₀ else 0) +
        (if rank x = 2 then b₂ else 0) +
        (if rank x = 3 then b₃ else 0) + b₄) := Finset.sum_le_sum hpoint
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_filter,
        Finset.sum_const, smul_eq_mul]

end CubicTenVariables.FiniteRankMass
