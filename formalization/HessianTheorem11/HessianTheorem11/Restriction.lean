import Mathlib.LinearAlgebra.Matrix.Rank

/-!
The elementary part of the rational restriction argument in Corollary 28.1.

This file does not assume or prove the ten-variable Hessian theorem. It proves
that anisotropy survives an injective linear restriction and that a restricted
Hessian cannot have rank larger than its ambient Hessian. The actual Hessian
chain rule and passage to the generic point are separate obligations.
-/

namespace HessianTheorem11.Restriction

/-- A function has no nonzero vector in its zero fibre. -/
def ZeroFibreTrivial {V K : Type*} [Zero V] [Zero K] (F : V → K) : Prop :=
  ∀ v, F v = 0 → v = 0

/-- Anisotropy is inherited by every injective linear restriction. -/
theorem zeroFibreTrivial_comp_injective
    {K V W : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W]
    {F : V → K} (hF : ZeroFibreTrivial F) (B : W →ₗ[K] V)
    (hB : Function.Injective B) : ZeroFibreTrivial (F ∘ B) := by
  intro w hw
  apply hB
  simpa only [map_zero] using hF (B w) hw

/-- Matrix congruence by a rectangular restriction does not increase rank. -/
theorem rank_congruence_le
    {K m n : Type*} [CommRing K] [Fintype m] [Fintype n]
    (A : Matrix n n K) (B : Matrix n m K) :
    (B.transpose * A * B).rank ≤ A.rank := by
  exact (Matrix.rank_mul_le_left (B.transpose * A) B).trans
    (Matrix.rank_mul_le_right B.transpose A)

/-- A lower bound for the restricted matrix gives the ambient lower bound. -/
theorem rank_le_of_restriction
    {K m n : Type*} [CommRing K] [Fintype m] [Fintype n]
    (A : Matrix n n K) (B : Matrix n m K) {r : ℕ}
    (hr : r ≤ (B.transpose * A * B).rank) : r ≤ A.rank :=
  hr.trans (rank_congruence_le A B)

/-- An on-cubic rank witness for a restriction is an ambient witness once
the polynomial restriction and Hessian chain-rule identities are supplied. -/
theorem ambient_rank_witness_of_restriction
    {K m n : Type*} [CommRing K] [Fintype m] [Fintype n]
    (F : (n → K) → K) (f : (m → K) → K)
    (H : (n → K) → Matrix n n K) (h : (m → K) → Matrix m m K)
    (B : Matrix n m K)
    (hrestrict : ∀ z, f z = F (B.mulVec z))
    (hchain : ∀ z, h z = B.transpose * H (B.mulVec z) * B)
    {r : ℕ} (hwitness : ∃ z, f z = 0 ∧ r ≤ (h z).rank) :
    ∃ x, F x = 0 ∧ r ≤ (H x).rank := by
  obtain ⟨z, hz, hr⟩ := hwitness
  refine ⟨B.mulVec z, (hrestrict z).symm.trans hz, ?_⟩
  rw [hchain z] at hr
  exact rank_le_of_restriction (H (B.mulVec z)) B hr

end HessianTheorem11.Restriction
