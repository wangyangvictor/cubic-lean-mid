import CubicTenVariables.IntegralLinearNormalization
import CubicTenVariables.IntegralCoordinateBoxes

/-! Integral equation transport through the actual normalization matrix.
The original ideal is used before reducing modulo any integer. -/
noncomputable section
namespace CubicTenVariables.IntegralNormalizationEvaluation
open MvPolynomial IntegralLinearNormalization
variable {n s : ℕ}

theorem eval_transformed_relation (A : Matrix (Fin n) (Fin n) ℤ)
    (β : Fin s ↪ Fin n) (j : Fin n) (P : Polynomial (MvPolynomial (Fin s) ℤ))
    (x : Fin n → ℤ) :
    eval (A.mulVec x) (P.eval₂ (MvPolynomial.rename β).toRingHom (X j)) =
      eval x (relation A β j P) := by
  have hl : eval (A.mulVec x) (P.eval₂ (MvPolynomial.rename β).toRingHom (X j)) =
      P.eval₂ (eval (fun i => A.mulVec x (β i))) (A.mulVec x j) := by
    rw [Polynomial.hom_eval₂,eval_X]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro i
      change eval (A.mulVec x) (MvPolynomial.rename β (X i)) = _
      rw [MvPolynomial.eval_rename,eval_X,eval_X]
      rfl
  rw [hl]
  simpa using (eval₂_relation (K := ℤ) A β j P x).symm

/-- Every normalized relation retains original-ideal divisibility for all q,
including divisors of denominators or the coordinate determinant. -/
theorem certificate_divisibility {J : Ideal (MvPolynomial (Fin n) ℤ)} {r : ℕ}
    (D : Certificate J r) (x : Fin n → ℤ) (q : ℕ)
    (hx : ∀ f ∈ J, (q : ℤ) ∣ eval x f) (j : Fin n) :
    (q : ℤ) ∣ eval (D.matrix.mulVec x)
      ((D.polynomial j).eval₂ (MvPolynomial.rename D.base).toRingHom (X j)) := by
  rw [eval_transformed_relation]
  exact hx _ (D.relation_mem j)

theorem certificate_coefficient {J : Ideal (MvPolynomial (Fin n) ℤ)} {r : ℕ}
    (D : Certificate J r) (j : Fin n) :
    (D.polynomial j).coeff (D.polynomial j).natDegree = C (D.leading : ℤ) :=
  D.leadingCoeff_eq j

end CubicTenVariables.IntegralNormalizationEvaluation
