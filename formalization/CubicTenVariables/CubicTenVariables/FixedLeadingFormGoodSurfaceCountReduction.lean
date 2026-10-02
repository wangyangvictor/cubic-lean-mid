import CubicTenVariables.FiniteLeadingFormSurfaceCountAssembly
import CubicTenVariables.FixedLeadingFormIntegralShear
import TranslatedDepthSeven.IntegralHomogeneousIdealModel

/-!
# The remaining fixed-leading-form surface estimate

For the actual saturated-boundary family, the four-variable estimate reduces
to a literal three-variable counting statement.  Its constant may depend on
one fixed integral leading form, but must work for every lower-order part
and every nonzero rational leading scalar.  This statement is an explicit
remaining obligation, not a proved estimate or an imported literature axiom.

The integral slicing direction is constructed from geometric-integrality
openness; the remaining Bertini argument and the integer specialization are
internal.  Clearing denominators does not impose integrality on the varying
leading scalar.  The intended counting application has degree at least four.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace CubicTenVariables.FixedLeadingFormGoodSurfaceCountReduction

open MvPolynomial TranslatedDepthSeven Published
open HessianTheorem11.PolynomialRestriction
open FiniteLeadingFormSurfaceCountAssembly FixedLeadingFormIntegralShear
open GoodSurfaceFibreSimultaneousBoundaryProjection
open GoodSurfaceFibreAffineFourStaticProjection

/-- The still-open numerical surface statement, with the required constant
chosen before the varying polynomial and its leading scalar. -/
def FixedIntegralLeadingSurfaceBounds (d : ℕ) (epsilon : ℝ) : Prop :=
  ∀ k : MvPolynomial (Fin 3) ℤ,
    k.IsHomogeneous d → IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k) →
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
        IsTopHomogeneousPart g (MvPolynomial.C c * map (Int.castRingHom ℚ) k) d →
        ∀ B : ℝ, 1 ≤ B →
          ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤ C * B ^ (1 + epsilon)

/-- Denominator clearing turns a fixed rational leading form into a fixed
integral one; the varying scalar is divided by the fixed denominator. -/
theorem rational_surface_bound_of_integral_surface_bounds
    {d : ℕ} {epsilon : ℝ}
    (hsurface : FixedIntegralLeadingSurfaceBounds d epsilon)
    (k : MvPolynomial (Fin 3) ℚ) (hhom : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
        IsTopHomogeneousPart g (MvPolynomial.C c * k) d →
        ∀ B : ℝ, 1 ≤ B →
          ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤ C * B ^ (1 + epsilon) := by
  let D : ℚ := mvPolynomialRationalCommonDenominator k
  have hD : D ≠ 0 := by
    dsimp only [D]
    exact_mod_cast (mvPolynomialRationalCommonDenominator_pos k).ne'
  have hclear : IsAbsolutelyIrreducible
      (map (Int.castRingHom ℚ) (clearRationalMvPolynomial k)) := by
    rw [map_clearRationalMvPolynomial]
    exact hirr.const_mul D hD
  obtain ⟨C, hC, hcount⟩ := hsurface (clearRationalMvPolynomial k)
    (clearRationalMvPolynomial_isHomogeneous hhom) hclear
  refine ⟨C, hC, ?_⟩
  intro g c hc htop B hB
  have heq : MvPolynomial.C (c / D) *
      map (Int.castRingHom ℚ) (clearRationalMvPolynomial k) = MvPolynomial.C c * k := by
    rw [map_clearRationalMvPolynomial, ← mul_assoc, ← map_mul]
    change MvPolynomial.C (c / D * D) * k = _
    rw [div_mul_cancel₀ c hD]
  exact hcount g (c / D) (div_ne_zero hc hD) (by rw [heq]; exact htop) B hB

/-- Once the surface estimate is supplied, integrality openness suffices to
construct the sheared surface estimate required by the finite-menu assembly. -/
theorem exists_sheared_surface_bound
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 2 ≤ d) {epsilon : ℝ}
    (hsurface : FixedIntegralLeadingSurfaceBounds d epsilon)
    (H : MvPolynomial (Fin 4) ℚ) (hhom : H.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible H) :
    ∃ (a : Fin 3 → ℤ) (C : ℝ), 0 < C ∧
      rationalSpecializeFirstCoordinate 0
        (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) H) ≠ 0 ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
        IsTopHomogeneousPart g
          (MvPolynomial.C c * rationalSpecializeFirstCoordinate 0
            (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) H)) d →
        ∀ B : ℝ, 1 ≤ B →
          ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤ C * B ^ (1 + epsilon) := by
  obtain ⟨a, ha⟩ := exists_integral_shear_absIrreducible integralityOpen hd H hhom hirr
  have hslice : (rationalSpecializeFirstCoordinate 0
      (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) H)).IsHomogeneous d := by
    rw [← restrict_graphFrame_eq_shear_slice]
    exact homogeneous_restrict _ _ hhom
  obtain ⟨C, hC, hcount⟩ := rational_surface_bound_of_integral_surface_bounds
    hsurface _ hslice ha
  exact ⟨a, C, hC, ha.ne_zero, hcount⟩

/-- One fixed saturated boundary gives a single constant for all actual
dynamic projection equations.  All numerical counting still enters through
`hsurface`; the shear is no longer an additional existential hypothesis. -/
theorem fixed_saturatedBoundary_dynamic_count
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    {d : ℕ} (hd : 2 ≤ d) {epsilon : ℝ}
    (hsurface : FixedIntegralLeadingSurfaceBounds d epsilon)
    (boundary : Ideal (MvPolynomial (Fin 10) ℚ))
    (hprime : boundary.IsPrime)
    (hgeometric : GeometricallyPrimeMvPolynomialIdeal boundary) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : Ideal (MvPolynomial (Fin 10) ℚ))
        (_hIB : projectiveBoundaryIdeal (affineIdealProjectiveClosure J) ≤ boundary)
        (w : SimultaneousSourceSaturatedBoundaryMenuProjection J boundary d)
        (base : IntVector 4) (m : ℕ), 0 < m →
        ∀ B : ℝ, 1 ≤ B →
          ((affineHypersurfaceIntegerPoints
            (integralAffineTransform base m
              (affineChartProjectionEquation w.sourceEquation)) B).card : ℝ) ≤
                C * B ^ (2 + epsilon) := by
  exact fixed_saturatedBoundary_dynamic_count_of_surface_bounds d epsilon
    boundary hprime hgeometric
    (fun H hhom hirr => exists_sheared_surface_bound integralityOpen hd hsurface H hhom hirr)

end CubicTenVariables.FixedLeadingFormGoodSurfaceCountReduction
