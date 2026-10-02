import CubicTenVariables.CubicSurfaceAmplificationFromZeta
import CubicTenVariables.CubicSurfacePointCountOfAmplification
import CubicTenVariables.CubicSurfacePointCountReduced

/-!
The isolated-conjugate cubic-surface remainder from concrete zeta-factor
literature. Potential goodness and amplification supply all geometrically
singular nonconical cases; no singularity classification or descent of a
two-, three-, or four-point configuration is required here. The actual
finite-extension zeta-factor statement remains an explicit argument.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.CubicSurfacePointCountFromZeta

open Literature CubicSurfacePointCountReduced

/-- Concrete all-extension zeta-factor data supplies the residual surface
input. The internally proved count covers all geometric singularities, so
the residual finiteness and singular-cardinality hypotheses are unused. -/
theorem proved (zeta : CubicSurfaceZetaFactorBounds) :
    IsolatedConjugateCubicSurfacePointCount := by
  refine ⟨23328, by norm_num, ?_⟩
  intro K _ _ F hF h2 h3 hI hNC _hfin hs _hrat _hcard
  exact CubicSurfacePointCountOfAmplification.singular_affine_bound
    (CubicSurfaceAmplificationFromZeta.proved zeta) F hF h2 h3 hI hNC hs

end CubicTenVariables.CubicSurfacePointCountFromZeta
