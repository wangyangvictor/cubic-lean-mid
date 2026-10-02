import CubicTenVariables.MicrolocalPartitionCounts
import CubicTenVariables.MicrolocalPromotionCoverSurfaceSlicing

/-!
# The actual microlocal table counted by surface slicing

This is the surface-slicing analogue of `table_part_bound`.  It connects the
new residual-cover propagation theorem to the table object constructed from
the n=10 microlocal geometry.  The former Salberger premise is replaced by
surface-slicing data on the table's original components only.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace CubicTenVariables.MicrolocalPartitionCounts

open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData ProjectiveMicrolocalModels RationalConeClosure
open MicrolocalPromotedPartition ConeComponentProgressionCount
open ConeComponentSurfaceSlicingEndpoint

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Feed an actual high-level promotion table to the explicit surface-slicing
endpoint.  No slicing datum is requested for residual or incoming pieces. -/
theorem table_part_bound_of_surfaceSlicing
    {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (hgeo : Geometry F f)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (j : Fin 6) (hj : j.val = 3 ∨ j.val = 4)
    (T : MicrolocalPromotionTable.Table F f j.val)
    (slicing : ∀ i,
      HighComponentSurfaceSlicingData (8 - j.val)
        (PolynomialExponentialFamily.baseIdeal (T.G i)))
    (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U)
    (hopen : U j.val = T.open)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points (part f U j) u L m b).card : ℝ) ≤
        C * (2 + ‖u‖ + L + (m : ℝ)) ^ epsilon *
          (1 + L / (m : ℝ)) ^ (8 - j.val) :=
  MicrolocalPromotionCover.exists_part_bound_of_surfaceSlicing
    hgeo hAn j hj
      (fun i => PolynomialExponentialFamily.baseIdeal (T.G i))
      T.prime T.homogeneous T.cover_point
      (fun i => map (Int.castRingHom ℚ) (T.h i))
      (T.cases_for_high_levels hj) slicing U hU hopen epsilon hepsilon

end CubicTenVariables.MicrolocalPartitionCounts
