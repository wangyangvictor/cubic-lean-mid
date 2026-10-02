import CubicTenVariables.Theorem11ReducedFixedLeadingIsolatedConjugate
import CubicTenVariables.FixedLeadingHypersurfaceCountInternalCurves
import CubicTenVariables.CubicSurfacePointCountFromZeta

/-! The ten-variable theorem with five displayed literature premises.
The fixed-leading count uses internal primitive-direction and projected-curve
proofs. Singular cubic-surface counting is deduced from literal all-extension
zeta factors by the proved amplification argument. -/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.Theorem11ReducedZetaInternalCurves

theorem main
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (weil : Literature.SmoothCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    (zeta : Literature.CubicSurfaceZetaFactorBounds) :
    MainTheorem := by
  exact Theorem11ReducedFixedLeadingIsolatedConjugate.main_from_counts
    microlocal weil dichotomy
    (FixedLeadingHypersurfaceCountInternalCurves.proved curveWeil)
    (CubicSurfacePointCountFromZeta.proved zeta)

end CubicTenVariables.Theorem11ReducedZetaInternalCurves
