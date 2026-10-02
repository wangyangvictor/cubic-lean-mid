import CubicTenVariables.RationalTerminalBound
import CubicTenVariables.GeometryTen

/-! The ten-variable rational terminal dimension bound, with its ambient
singular-dimension application condition proved internally. -/

noncomputable section
namespace CubicTenVariables.TerminalTenBound
open HessianTheorem11 RationalConeClosure TerminalBadNormals

/-- In ten variables the rational closure of normals whose literal
section-singularity fiber has affine dimension at least five is at most
one-dimensional. No singular-dimension or family hypothesis is supplied. -/
theorem rational_fourth_stratum_dimension_le_one (F : AnisotropicCubic 10) :
    affineDimension (rationalConeClosure (badNormals (geometricPolynomial F.polynomial) 4)) ≤ 1 := by
  have hs : singularDimension F.polynomial ≤ ((4+1 : ℕ) : Dimension) := by
    simpa using Geometry.singularDimension_le_five F
  simpa using RationalTerminalBound.rational_badNormals_dimension_le F (by norm_num : 1 ≤ 4) hs

/-- For t at least five, the same rational closure has dimension at most
zero. This includes the origin adjoined by the source construction. -/
theorem rational_higher_stratum_dimension_le_zero (F : AnisotropicCubic 10)
    (t : ℕ) (ht : 5 ≤ t) :
    affineDimension (rationalConeClosure (badNormals (geometricPolynomial F.polynomial) t)) ≤ 0 := by
  have hs : singularDimension F.polynomial ≤ ((t+1 : ℕ) : Dimension) :=
    (Geometry.singularDimension_le_five F).trans (by exact_mod_cast (by omega : 5 ≤ t+1))
  have hb := RationalTerminalBound.rational_badNormals_dimension_le F (by omega) hs
  have hn : 10 - (3 * (t+2) + 1) / 2 = 0 := by omega
  simpa only [hn, Nat.cast_zero] using hb

end CubicTenVariables.TerminalTenBound
