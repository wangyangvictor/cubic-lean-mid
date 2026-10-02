import HessianTheorem11.UnconditionalResults
import HessianTheorem11.UnconditionalGenericRank
import HessianTheorem11.ReducedConcentrationFromRank
import HessianTheorem11.ReducedConeInputs
import HessianTheorem11.ReducedProjectiveDimension
import HessianTheorem11.BibleHyperplaneSections

/-! Further exact source conclusions after proving generic rank and rational
weight descent. No external mathematical interface is a hypothesis. -/
noncomputable section
namespace HessianTheorem11.Unconditional
open Module MvPolynomial BibleTargets BibleProjectiveGeometry BibleRestrictions

theorem genericRankOpen : GenericRankOpenInput :=
  UnconditionalGeneric.genericRankOpenInput

theorem concentrationGeometry : ConcentrationGeometryInput :=
  ReducedConcentrationFromRank.concentrationGeometryInput genericRankOpen

theorem genericConePointSelection : GenericConePointSelectionInput :=
  ReducedInputs.genericConePointSelection genericRankOpen

theorem finiteQuadraticConeCover : FiniteQuadraticConeCoverInput :=
  ReducedInputs.finiteQuadraticConeCover concentrationGeometry.toAffineComponentsInput genericRankOpen

theorem hypersurfaceDimension : AffineHypersurfaceDimensionInput :=
  ReducedHypersurfaceDimension.affineHypersurfaceDimensionInput genericRankOpen

theorem projectiveDimensionInput : AffineProjectiveDimensionInput :=
  ReducedProjectiveDimension.affineProjectiveDimensionInput genericRankOpen

/-- The exact eleven-variable incidence bound. -/
theorem I11 : Targets.I11 :=
  Completed.I11 concentrationGeometry genericConePointSelection provedSymmetricDeterminantalTangent

/-- The exact thirteen-variable affine singular-dimension bound. -/
theorem S13 : Targets.S13 :=
  Completed.S13 finiteQuadraticConeCover provedSymmetricDeterminantalTangent

/-- The rank-at-most-two locus on the actual cubic has affine dimension at most two. -/
theorem B06 (F : AnisotropicCubic 12) :
    affineDimension {x ∈ cubicLocus F.polynomial |
      (hessian (geometricPolynomial F.polynomial) x).rank ≤ 2} ≤ 2 :=
  BibleLowRank.anisotropic_on_cubic_rank_two_dimension_le
    concentrationGeometry.toAffineComponentsInput genericConePointSelection
    provedSymmetricDeterminantalTangent F (by norm_num)

/-- The source Theorem I.1.1 incidence bound, with no external input. -/
theorem B07 (F : AnisotropicCubic 12) : incidenceDimension F.polynomial ≤ 15 :=
  BibleCore.incidenceDimension_twelve_le_fifteen concentrationGeometry genericConePointSelection
    provedSymmetricDeterminantalTangent F

/-- The exact actual-incidence lower bound in terms of generic full Hessian rank. -/
theorem B10 (F : AnisotropicCubic 12) :
    ((11 + (12 - genericHessianRank F.polynomial) : ℕ) : Dimension) ≤
      incidenceDimension F.polynomial :=
  BibleCore.incidenceDimension_twelve_lower_bound genericRankOpen
    concentrationGeometry.toKernelBundleInput hypersurfaceDimension
    cubicGeometricIrreducibility (provedDeterminantalTangentOver ℚ) F

/-- Both actual affine and projective vertex bounds for every geometric section. -/
theorem B14 (F : AnisotropicCubic 12)
    (B : Matrix (Fin 12) (Fin 11) GeometricField) (hB : Function.Injective B.mulVec) :
    finrank GeometricField (sectionVertex F B) ≤ 2 ∧
      projectiveDimension (sectionVertex F B : Set (GeometricPoint 11)) ≤ 1 :=
  BibleHyperplanes.section_vertex_dimension_twelve concentrationGeometry.toAffineComponentsInput
    genericConePointSelection provedSymmetricDeterminantalTangent genericRankOpen
    projectiveDimensionInput F B hB

/-- The general radial singular bound for every actual rational subspace restriction. -/
theorem B17 (F : AnisotropicCubic 12) (M : Submodule ℚ (Fin 12 → ℚ))
    (hm : 4 ≤ finrank ℚ M) :
    singularDimension (subspaceCubic F M).polynomial ≤
      ((2 * finrank ℚ M - 3) / 3 : ℕ) :=
  (BibleRestrictions.subspace_anisotropic_and_singularDimension finiteQuadraticConeCover
    provedSymmetricDeterminantalTangent F M hm).2

end HessianTheorem11.Unconditional
