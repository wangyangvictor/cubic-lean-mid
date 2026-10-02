import CubicTenVariables.FixedLeadingHypersurfaceCountInduction
import CubicTenVariables.GenericFixedLeadingFormIntegralShear

/-! For one fixed leading equation, the proved generic Bertini construction
and explicit integrality openness provide every integral shear needed by
the counting induction. No saturated family-of-sections input is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FixedLeadingHypersurfaceCountFromSurface

open FixedLeadingFormGoodSurfaceCountReduction FixedLeadingHypersurfaceCountInduction

theorem all_dimensions
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hsurface : FixedIntegralLeadingSurfaceBounds d ε) :
    ∀ n : ℕ, 3 ≤ n → FixedRationalLeadingHypersurfaceBounds n d ε := by
  apply all_dimensions_of_integral_shears hsurface
  intro n hn k hk hirr
  exact GenericFixedLeadingFormIntegralShear.exists_integral_shear_absIrreducible
    integralityOpen hn hd k hk hirr

end CubicTenVariables.FixedLeadingHypersurfaceCountFromSurface
