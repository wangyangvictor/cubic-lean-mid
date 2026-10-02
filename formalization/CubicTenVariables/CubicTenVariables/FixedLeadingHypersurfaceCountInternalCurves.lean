import CubicTenVariables.FixedLeadingSurfaceNormalizedRegularCountInternalCurves
import CubicTenVariables.FixedLeadingHypersurfaceCountFromSurface
import CubicTenVariables.ConeComponentFixedLeadingCount
import CubicTenVariables.HomogeneousHypersurfaceIntegralityOpenProved

/-! Higher-dimensional propagation of the fixed-leading surface estimate
with both primitive directions and bounded-degree projected curves counted
internally. The affine plane-curve Weil bound is the displayed input. -/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.FixedLeadingHypersurfaceCountInternalCurves

theorem proved
    (curveWeil : Literature.AffinePlaneCurveWeil) :
    ConeComponentFixedLeadingCount.HighDegreeFixedLeadingCounts := by
  intro n d hn hd epsilon hepsilon
  exact FixedLeadingHypersurfaceCountFromSurface.all_dimensions
    HomogeneousHypersurfaceIntegralityOpenProved.proved (by omega : 2 ≤ d)
    (FixedLeadingSurfaceNormalizedRegularCountInternalCurves.fixed_integral_leading_surface_bounds
      curveWeil hd epsilon hepsilon) n hn

end CubicTenVariables.FixedLeadingHypersurfaceCountInternalCurves
