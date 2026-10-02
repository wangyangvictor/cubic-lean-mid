import HessianTheorem11.UnconditionalDimensionResults
import HessianTheorem11.UnconditionalRationalBoundary
import HessianTheorem11.UnconditionalFormOrbitOpen
import HessianTheorem11.UnconditionalFiberDimension
import HessianTheorem11.UnconditionalCutDimension
import HessianTheorem11.ReducedConcentrationFromRank
import HessianTheorem11.ReducedHypersurfaceDimension
import HessianTheorem11.ReducedProjectiveDimension
import HessianTheorem11.ReducedRelativeKempf
import HessianTheorem11.ReducedFormalSmoothArc
import HessianTheorem11.ReducedKernelAnnihilator
import HessianTheorem11.ReducedKernelTangent
import HessianTheorem11.ReducedRationalFlagDescent
import HessianTheorem11.ReducedOrdinaryBigCell
import HessianTheorem11.ReducedBigCell
import HessianTheorem11.BibleTargets
import HessianTheorem11.BibleConeCoordinates
import HessianTheorem11.BibleHyperplaneSections
import HessianTheorem11.ReducedConeInputs
import HessianTheorem11.ReducedLinearSections
import HessianTheorem11.ReducedGenericRank
import HessianTheorem11.ReducedDeterminantalTangent
import HessianTheorem11.ReducedFormalImplicit
import HessianTheorem11.ReducedIrreducibility

/-! All of Theorem I.1.1, with no external mathematical input package.
The rational homogeneous anisotropic cubic is the sole theorem parameter. -/

noncomputable section
namespace HessianTheorem11.BibleCompleted
open Module MvPolynomial RationalDescent NonzeroLimitTransport
  BibleTargets BibleHyperplanes BibleProjectiveGeometry BibleVertex BibleRestrictions

/-- Complete geometry of every anisotropic rational twelve-variable cubic,
including every geometric hyperplane and every rational linear restriction. -/
theorem theorem_I_1_1
    (F : AnisotropicCubic 12) : TheoremI11 F := by
  let OP := UnconditionalFormOrbitOpen.formOrbitOpenMapInput
  let HI := UnconditionalCutDimension.homogeneousCutDimensionInput
  let GR := UnconditionalGeneric.genericRankOpenInput
  let FD := UnconditionalFiberDimension.affineFiberDimensionInput
  let AD := ReducedHypersurfaceDimension.affineHypersurfaceDimensionInput GR
  let AP := ReducedProjectiveDimension.affineProjectiveDimensionInput GR
  let AG := ReducedConcentrationFromRank.concentrationGeometryInput GR
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
  have hs := Completed.S12 AG.toAffineComponentsInput GP AG.toGenericRankOpenInput DT MR AD SA
    boundary bigCell DTQ CI FI  F
  have hs' : affineDimension (singularCone (geometricPolynomial F.polynomial)) ≤ 6 := hs
  have hrest := theorem_I_1_1_iv AG GP DT KB SA AD MR KA FD LS boundary bigCell DTQ CI FI
     QC F
  refine {
    geometricallyIntegral := BibleCore.geometric_coordinateRing_isDomain CI DTQ F (by norm_num)
    notProjectiveCone := anisotropic_not_projectiveCone F
    hessianInjective := geometric_hessian_injective F
    determinantNonzero := geometric_hessianDeterminantPolynomial_ne_zero DTQ F
    rankOneLocus := BibleLowRank.anisotropic_on_cubic_rank_one_eq_origin DT  F (by norm_num)
    rankTwoDimension := BibleLowRank.anisotropic_on_cubic_rank_two_dimension_le
      AG.toAffineComponentsInput GP DT  F (by norm_num)
    incidenceDimension := BibleCore.incidenceDimension_twelve_le_fifteen AG GP DT  F
    singularDimension := hs
    genericRank := BibleCore.rank_eight_via_incidence AG GP DT AD DTQ CI  F
    incidenceLowerBound := BibleCore.incidenceDimension_twelve_lower_bound
      AG.toGenericRankOpenInput AG.toKernelBundleInput AD CI DTQ F
    geometricSectionsIntegral := ?_
    geometricSectionsSingular := ?_
    rationalSectionsSingular := ?_
    sectionVertexDimension := ?_
    vertexDefinedOver := ?_
    restrictionsAnisotropic := fun M hm => (hrest.1 M hm).1
    restrictionsSingular := fun M hm => (hrest.1 M hm).2.1
    restrictionsSingularStrong := fun M hm => (hrest.1 M (by omega)).2.2 hm
    singularLinearSpaces := hrest.2 }
  · intro B hB
    have hi := section_irreducible HI AG.toGenericRankOpenInput B hB _
      (geometric_homogeneous F.homogeneous) hs' (by norm_num)
    refine ⟨hi, ?_⟩
    letI : (Ideal.span {sectionPolynomial F B}).IsPrime :=
      (Ideal.span_singleton_prime hi.ne_zero).mpr hi.prime
    infer_instance
  · intro B hB
    apply projectiveDimension_le AP _ (singularCone_closed _)
      (singularCone_cone _ (PolynomialRestriction.homogeneous_restrict B _
        (geometric_homogeneous F.homogeneous)))
    exact section_singular_dimension_le HI B hB _ (geometric_homogeneous F.homogeneous) hs'
  · intro B hB
    change projectiveDimension (singularCone
      (geometricPolynomial (PolynomialRestriction.restrict B F.polynomial))) ≤ 4
    apply projectiveDimension_le AP _ (singularCone_closed _)
      (singularCone_cone _ (geometric_homogeneous
        (PolynomialRestriction.homogeneous_restrict B F.polynomial F.homogeneous)))
    exact restriction_singularDimension_eleven AG GP DT KB SA AD MR KA FD LS boundary bigCell
      DTQ CI FI  F B hB
  · intro B hB
    exact BibleHyperplanes.section_vertex_dimension_twelve AG.toAffineComponentsInput GP DT AG.toGenericRankOpenInput
       AP F B hB
  · intro K L _ _ _ _ p hp
    exact affineVertex_baseChange p hp

end HessianTheorem11.BibleCompleted
