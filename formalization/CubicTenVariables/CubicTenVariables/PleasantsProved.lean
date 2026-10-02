import CubicTenVariables.PadicCubicLocalZero
import CubicTenVariables.PadicCubicOrder

/-! The original literal Pleasants input is proved in full. All primes,
all dimensions, and the original order-at-least-ten hypothesis are kept.
The proof combines local cubic existence with exact variable elimination. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PleasantsProved

/-- Full inhabitant of the existing input proposition, without any
unproved local-existence or geometric premise. -/
theorem proved : Literature.Pleasants1971Theorem2Qp := by
  intro p hp n F hF horder
  exact PadicCubicOrder.nonsingular_zero_of_nonzero_zero
    (fun m G hG hm => PadicCubicLocalZero.exists_zero G hG hm) F hF horder

end CubicTenVariables.PleasantsProved
