import HessianTheorem11.ReducedConcentration
import HessianTheorem11.ReducedHypersurfaceDimension
import HessianTheorem11.ReducedKernelBundle

/-! The entire old nine-field affine geometry interface is now constructed
from generic smoothness/rank alone. Neither KI nor AD is a premise. -/
noncomputable section
namespace HessianTheorem11.ReducedConcentrationFromRank

theorem concentrationGeometryInput (GR : GenericRankOpenInput) :
    ConcentrationGeometryInput := by
  let core : ReducedConcentration.ConcentrationCoreInput := {
    toGenericRankOpenInput := GR
    toKernelBundleInput := ReducedKernelBundle.kernelBundleInput GR }
  exact core.toConcentrationGeometryInput
    (ReducedHypersurfaceDimension.affineHypersurfaceDimensionInput GR)

end HessianTheorem11.ReducedConcentrationFromRank
