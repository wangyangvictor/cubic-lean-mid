import CubicTenVariables.ArithmeticReduction
import CubicTenVariables.SymmetricPresentation

/-! Exact normalization to the integral symmetric tensor convention in the
analytic literature. Multiplying a cubic by six changes neither existence
of a nonzero zero nor the final main theorem. -/

namespace CubicTenVariables
open MvPolynomial HessianTheorem11

/-- The ten-variable problem in the ordered symmetric tensor convention.
This is a target proposition, not an assumed theorem. -/
def SymmetricTenVariableTheorem : Prop :=
  ∀ T : SymmetricIntegerCubicTensor 10, HasIntegerZero T.polynomial

theorem integerTen_iff_symmetricTen :
    IntegerTenVariableTheorem ↔ SymmetricTenVariableTheorem := by
  constructor
  · intro h T
    exact h T.polynomial T.polynomial_homogeneous
  · intro h F hF
    exact (symmetricTensorOfCubic_hasIntegerZero_iff F hF).mp
      (h (symmetricTensorOfCubic F))

theorem main_iff_symmetricTen : MainTheorem ↔ SymmetricTenVariableTheorem :=
  main_iff_integerTen.trans integerTen_iff_symmetricTen

theorem main_of_symmetric_anisotropic_contradiction
    (h : ∀ T : SymmetricIntegerCubicTensor 10,
      Anisotropic (map (Int.castRingHom ℚ) T.polynomial) → False) : MainTheorem := by
  apply main_iff_symmetricTen.mpr
  intro T
  apply (hasRationalZero_map_iff T.polynomial_homogeneous).mp
  apply (hasRationalZero_iff_not_anisotropic _).mpr
  exact h T

end CubicTenVariables
