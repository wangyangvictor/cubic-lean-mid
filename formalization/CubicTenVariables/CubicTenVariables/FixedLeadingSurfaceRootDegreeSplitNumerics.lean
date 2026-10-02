import CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplit

/-!
# Degree-mass numerics for the Salberger root split

The non-Galois-stable error is quadratic in the actual component degree.
It must therefore be summed using the total geometric degree mass, rather
than bounding every component by the largest degree and multiplying by the
number of components.  The latter would lose an unnecessary third power of
the root auxiliary degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceRootDegreeSplitNumerics

open MvPolynomial TranslatedDepthSeven
open FixedLeadingSurfacePersistentRootDegreeSplit
open scoped BigOperators

local instance rootDegreeSplitNumericsPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Active persistent labels form a subset of the literal minimal-prime
options, so their total degree is at most the full Bezout degree mass. -/
theorem sum_rootOptionDegree_active_le_minimalPrimeDegreeMass
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (G₀ : MvPolynomial (Fin 4) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ) :
    let active := activeQbarPersistentRootComponentOptions
      sourceEquations G₀ cell
    (∑ o ∈ active, rootOptionDegree degree o) ≤
      ∑ Q ∈ finiteEquationMinimalPrimes
        (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q := by
  classical
  dsimp only
  let components := finiteEquationComponentOptions
    (qbarSurfaceCutEquationFamily sourceEquations G₀)
  have hsubset : activeQbarPersistentRootComponentOptions
      sourceEquations G₀ cell ⊆ components := by
    intro o ho
    exact (mem_activeQbarPersistentRootComponentOptions_iff
      sourceEquations G₀ cell o).mp ho |>.1
  have hle : (∑ o ∈ activeQbarPersistentRootComponentOptions
      sourceEquations G₀ cell, rootOptionDegree degree o) ≤
      ∑ o ∈ components, rootOptionDegree degree o :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro _ _ _
      exact Nat.zero_le _)
  calc
    (∑ o ∈ activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell, rootOptionDegree degree o) ≤
        ∑ o ∈ components, rootOptionDegree degree o := hle
    _ = ∑ Q ∈ finiteEquationMinimalPrimes
          (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q := by
      simp [components, finiteEquationComponentOptions, rootOptionDegree,
        Finset.sum_image]

end CubicTenVariables.FixedLeadingSurfaceRootDegreeSplitNumerics
