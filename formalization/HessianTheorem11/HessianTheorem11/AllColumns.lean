import HessianTheorem11.UnconditionalDimensionResults
import HessianTheorem11.UnconditionalRationalBoundary
import HessianTheorem11.UnconditionalFormOrbitOpen
import HessianTheorem11.UnconditionalFiberDimension
import HessianTheorem11.ReducedConcentrationFromRank
import HessianTheorem11.ReducedHypersurfaceDimension
import HessianTheorem11.ReducedGenericImageTangent
import HessianTheorem11.ReducedRelativeKempf
import HessianTheorem11.ReducedFormalSmoothArc
import HessianTheorem11.ReducedKernelAnnihilator
import HessianTheorem11.ReducedKernelTangent
import HessianTheorem11.ReducedRationalFlagDescent
import HessianTheorem11.ReducedOrdinaryBigCell
import HessianTheorem11.ReducedBigCell
import HessianTheorem11.IncidenceThirteen
import HessianTheorem11.SingularCompleted
import HessianTheorem11.ReducedConeInputs
import HessianTheorem11.ReducedLinearSections
import HessianTheorem11.ReducedGenericRank
import HessianTheorem11.ReducedDeterminantalTangent
import HessianTheorem11.ReducedFormalImplicit
import HessianTheorem11.ReducedIrreducibility

/-! The nine numerical entries of Theorem 1.1, for n = 11, 12 and 13.
No external mathematical theorem is retained as an input.
Each field is the exact target on the actual cubic, Hessian and affine loci. -/
namespace HessianTheorem11.Completed
open RationalDescent NonzeroLimitTransport

/-- All nine requested numerical conclusions, proved together without
external mathematical interfaces. -/
theorem theorem1_1_columns : Targets.Theorem11Columns := by
  let OP := UnconditionalFormOrbitOpen.formOrbitOpenMapInput
  let GR := UnconditionalGeneric.genericRankOpenInput
  let FD := UnconditionalFiberDimension.affineFiberDimensionInput
  let AD := ReducedHypersurfaceDimension.affineHypersurfaceDimensionInput GR
  let AG := ReducedConcentrationFromRank.concentrationGeometryInput GR
  let GI := ReducedGenericImageTangent.genericImageTangentInput AG.toGenericRankOpenInput
  let boundary := UnconditionalBoundary.rationalRelativeBoundaryInput
  let SA := ReducedFormalSmoothArc.formalSmoothArcInput AG.toGenericRankOpenInput
  let KB := ReducedKernelTangent.kernelBundleTangentImageInput AG
  let KA := ReducedKernelAnnihilator.kernelAnnihilatorGeometry AG.toKernelBundleInput
  let bigCell := ReducedBigCell.orbitBigCellInput
    ReducedOrdinaryBigCell.specialLinearBigCellInput OP
  let GP := ReducedInputs.genericConePointSelection AG.toGenericRankOpenInput
  let QC := ReducedInputs.finiteQuadraticConeCover
    AG.toAffineComponentsInput AG.toGenericRankOpenInput
  let DT := provedSymmetricDeterminantalTangent
  let DTQ := provedDeterminantalTangentOver ℚ
  let MR := ReducedGenericRank.genericMatrixRankInput
  let FI := ReducedFormalImplicit.formalImplicitFunctionInput GeometricField
  let LS := ReducedInputs.linearSectionDimension
    AG.toAffineComponentsInput AG.toGenericRankOpenInput AD
  let CI : CubicGeometricIrreducibility := Unconditional.cubicGeometricIrreducibility
  exact {
    incidence11 := I11 AG GP DT 
    incidence12 := I12 AG GP DT AD boundary bigCell MR DTQ CI FI 
    incidence13 := I13 (AG := AG) (GP := GP) (GI := GI) (MR := MR) (DT := DT)
      (AD := AD) (SA := SA) (boundary := boundary) (bigCell := bigCell)
      (DTQ := DTQ) (CI := CI) (FI := FI) 
    rank11 := R11 MR KA AD AG.toGenericRankOpenInput GP DT FD LS boundary bigCell
      DTQ CI FI 
    rank12 := R12 MR DT DTQ CI FI
    rank13 := R13 MR DT DTQ CI FI
    singular11 := S11 AG.toAffineComponentsInput GP AG.toGenericRankOpenInput DT KB SA AD
      AG.toKernelBundleInput MR KA FD LS boundary bigCell DTQ CI FI 
    singular12 := S12 AG.toAffineComponentsInput GP AG.toGenericRankOpenInput DT MR AD SA
      boundary bigCell DTQ CI FI 
    singular13 := S13 QC DT 
  }

end HessianTheorem11.Completed
