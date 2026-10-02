import TranslatedDepthSeven.TangentPacketSpan
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Explicit height bounds for Cramer's rule

Fixed-dimensional elimination repeatedly solves an integral square linear
system.  The determinants in Cramer's rule give a common denominator and
integral numerators, all with an immediate factorial height bound.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Every Cramer numerator has the same factorial determinant bound as the
coefficient matrix, provided the right-hand side obeys the same entry bound. -/
theorem cramer_entry_natAbs_le_factorial_mul_pow
    {k M : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (b : Fin k → ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ M)
    (hb : ∀ i, (b i).natAbs ≤ M) (j : Fin k) :
    (A.cramer b j).natAbs ≤ k.factorial * M ^ k := by
  rw [Matrix.cramer_apply]
  apply TangentPacketSpan.det_natAbs_le_factorial_mul_pow
  intro i j'
  rw [Matrix.updateCol_apply]
  split_ifs
  · exact hb i
  · exact hA i j'

/-- Cramer's rule supplies one explicit nonzero common denominator and
bounded integral numerators for a nonsingular integral square system. -/
theorem exists_bounded_integral_cramer_solution
    {k M : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (b : Fin k → ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ M)
    (hb : ∀ i, (b i).natAbs ≤ M)
    (hdet : A.det ≠ 0) :
    ∃ d : ℤ, ∃ c : Fin k → ℤ,
      d ≠ 0 ∧
      A.mulVec c = d • b ∧
      d.natAbs ≤ k.factorial * M ^ k ∧
      ∀ i, (c i).natAbs ≤ k.factorial * M ^ k := by
  refine ⟨A.det, A.cramer b, hdet, Matrix.mulVec_cramer A b, ?_, ?_⟩
  · exact TangentPacketSpan.det_natAbs_le_factorial_mul_pow A hA
  · exact cramer_entry_natAbs_le_factorial_mul_pow A b hA hb

end

end TranslatedDepthSeven
