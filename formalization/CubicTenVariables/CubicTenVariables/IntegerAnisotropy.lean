import CubicTenVariables.Denominators
import HessianTheorem11.Geometry

/-! Rational anisotropy of an integral homogeneous cubic without an
integral zero. This is a proved denominator-clearing bridge. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial HessianTheorem11

/-- The exact anisotropic rational cubic in the contradiction branch.
Homogeneity permits clearing every putative rational zero to an integer zero. -/
def anisotropicCubicOfNoIntegerZero {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (hzero : ¬ HasIntegerZero F) : AnisotropicCubic n where
  polynomial := map (Int.castRingHom ℚ) F
  homogeneous := hF.map _
  anisotropic := by
    intro x hx
    by_contra hne
    exact hzero (hasIntegerZero_of_hasRationalZero hF ⟨x, hne, hx⟩)

end CubicTenVariables
