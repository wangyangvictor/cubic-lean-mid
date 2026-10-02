import CubicTenVariables.DominatingComponentSelection
import CubicTenVariables.TerminalIncidenceFamily

/-! Actual large dominating components of the terminal incidence, selected
from large singular-section fibers on a dense parameter set. The input is
the literal fiber lower bound, not existence of the desired component. -/

noncomputable section
namespace CubicTenVariables.TerminalComponentSelection
open MvPolynomial HessianTheorem11
open TerminalSectionIncidence TerminalFiberCoordinates TerminalIncidenceFamily

/-- Large section fibers on a dense set supply an actual large dominating
irreducible component of the literal closed incidence over the base. -/
theorem exists_large_incidence_component {n z k : ℕ}
    (F : GeometricPolynomial n) (Z A : Set (GeometricPoint n))
    (hZ : AlgebraicallyClosedSet Z) (hiZ : GeometricallyIrreducible Z)
    (hz : affineDimension Z = (z : Dimension)) (hA : geometricClosure A = Z)
    (hk : 0 < k) (hlarge : ∀ v ∈ A,
      (k : Dimension) ≤ affineDimension (sectionSingularFiber F v)) :
    ∃ Y, IsIrreducibleComponent (incidenceOver F Z) Y ∧
      geometricClosure (polynomialMap (normalProjection n) '' Y) = Z ∧
      ((z + k : ℕ) : Dimension) ≤ affineDimension Y := by
  apply DominatingComponentSelection.exists_large_dominating_component
    (normalProjection n) (incidenceOver F Z) (closed_incidenceOver F Z hZ)
    Z A hZ hiZ (normal_image_subset F Z) hz hA hk
  intro v hv
  have hvZ : v ∈ Z := hA ▸ subset_geometricClosure A hv
  rw [incidence_fiber_dimension F Z v hvZ]
  exact hlarge v hv

end CubicTenVariables.TerminalComponentSelection
