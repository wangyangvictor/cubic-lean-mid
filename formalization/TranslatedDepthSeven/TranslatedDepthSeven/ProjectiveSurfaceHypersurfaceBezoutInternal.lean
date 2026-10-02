import TranslatedDepthSeven.ProjectiveSurfaceHypersurfaceBezoutFromLowerDimension
import TranslatedDepthSeven.FiniteEquationComponentDimensionInternal

/-!
# The surface hypersurface degree input from Hilbert and real degree mass

The lower dimension of every rational component follows internally from
the finite-equation dimension theorem with the single equation G. All
remaining steps are the checked Hilbert/component-degree and real-chart
arguments. No separate Bezout or component-dimension hypothesis remains.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- The exact previously assumed surface-hypersurface affine-chart degree
statement follows from the Hilbert certification and real cone component
degree mass already present in the argument. -/
theorem projectiveSurfaceAffineHypersurfaceBezout_of_hilbert_and_realConeMass
    (hHilbertQ : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass) :
    StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout := by
  classical
  intro N d a I G hIprime hIhom _hX hIprojective hGhom hGnot
  apply projectiveSurfaceAffineHypersurfaceBezout_of_component_dimension_lower_bound
    hHilbertQ hRealMass I G hIprime hIhom hIprojective hGhom hGnot
  intro P hP
  letI : I.IsPrime := hIprime
  obtain ⟨r, hr, hdimension⟩ :=
    finiteEquation_minimalComponent_dimension_lower ℚ
      (MvPolynomial (Fin (N + 1)) ℚ) I P ({G} : Finset _)
      (by simpa only [Finset.coe_singleton] using
        (mem_finiteMinimalPrimes_iff (I ⊔ Ideal.span ({G} : Set _)) P).mp hP)
      (n := 3) (by simpa using hIprojective.1)
  have hrLower : 2 ≤ r := by
    simp only [Finset.card_singleton] at hdimension
    omega
  rw [hr]
  exact_mod_cast hrLower

end

end TranslatedDepthSeven
