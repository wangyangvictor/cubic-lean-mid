import HessianTheorem11.PolynomialRestriction

/-! Exact elementary rational-zero formulation of main.tex, Theorem 1.1.
No nonsingularity, local-solubility, rank, or geometry hypothesis is added.
The zero polynomial is included in the stronger elementary formulation. -/
namespace CubicTenVariables
open MvPolynomial

/-- An actual nonzero rational vector at which the given polynomial vanishes. -/
def HasRationalZero {n : ℕ} (F : MvPolynomial (Fin n) ℚ) : Prop :=
  ∃ x : Fin n → ℚ, x ≠ 0 ∧ eval x F = 0

/-- An actual nonzero integer vector at which the given polynomial vanishes. -/
def HasIntegerZero {n : ℕ} (F : MvPolynomial (Fin n) ℤ) : Prop :=
  ∃ x : Fin n → ℤ, x ≠ 0 ∧ eval x F = 0

/-- The main elementary Diophantine claim, in its stronger form allowing F=0. -/
def MainTheorem : Prop :=
  ∀ (n : ℕ), 10 ≤ n → ∀ F : MvPolynomial (Fin n) ℚ,
    F.IsHomogeneous 3 → HasRationalZero F

/-- The exact ten-variable rational case. -/
def TenVariableTheorem : Prop :=
  ∀ F : MvPolynomial (Fin 10) ℚ, F.IsHomogeneous 3 → HasRationalZero F

/-- The ten-variable case in integral coefficients and integral solutions. -/
def IntegerTenVariableTheorem : Prop :=
  ∀ F : MvPolynomial (Fin 10) ℤ, F.IsHomogeneous 3 → HasIntegerZero F

/-- The elementary nonzero-form formulation of the source's hypersurface theorem. -/
def HypersurfaceTheorem : Prop :=
  ∀ (n : ℕ), 10 ≤ n → ∀ F : MvPolynomial (Fin n) ℚ,
    F ≠ 0 → F.IsHomogeneous 3 → HasRationalZero F

end CubicTenVariables
