import HessianTheorem11.UnconditionalCubicIrreducibility
import HessianTheorem11.Completed
import HessianTheorem11.BibleTargets
import HessianTheorem11.ReducedGenericRank
import HessianTheorem11.ReducedFormalImplicit

/-! Exact source results whose vertical proofs require no external mathematical
interface. Homogeneity and rational anisotropy are the actual cubic data.
The remaining source results are deliberately not asserted here. -/
noncomputable section
namespace HessianTheorem11.Unconditional
open MvPolynomial Module BibleVertex BibleRestrictions

theorem cubicGeometricIrreducibility : CubicGeometricIrreducibility := by
  intro n F hn
  exact UnconditionalIrreducibility.anisotropic_geometric_irreducible F hn

/-- The exact n=12 generic full Hessian-rank bound, with no AG/GIT input. -/
theorem R12 : Targets.R12 :=
  Completed.R12 ReducedGenericRank.genericMatrixRankInput
    provedSymmetricDeterminantalTangent (provedDeterminantalTangentOver ℚ)
    cubicGeometricIrreducibility (ReducedFormalImplicit.formalImplicitFunctionInput GeometricField)

/-- The exact n=13 generic full Hessian-rank bound, with no AG/GIT input. -/
theorem R13 : Targets.R13 :=
  Completed.R13 ReducedGenericRank.genericMatrixRankInput
    provedSymmetricDeterminantalTangent (provedDeterminantalTangentOver ℚ)
    cubicGeometricIrreducibility (ReducedFormalImplicit.formalImplicitFunctionInput GeometricField)

/-- Theorem I.1.1, geometric integrality. -/
theorem B01 (F : AnisotropicCubic 12) : IsDomain (cubicCoordinateRing F.polynomial) :=
  cubicCoordinateRing_isDomain F.polynomial (cubicGeometricIrreducibility F (by norm_num))

/-- Theorem I.1.1, not a projective cone. -/
theorem B02 (F : AnisotropicCubic 12) :
    ¬ IsProjectiveCone (geometricPolynomial F.polynomial) :=
  anisotropic_not_projectiveCone F

/-- Theorem I.1.1, injectivity of the actual Hessian pencil. -/
theorem B03 (F : AnisotropicCubic 12) :
    Function.Injective (hessian (geometricPolynomial F.polynomial)) :=
  geometric_hessian_injective F

/-- Theorem I.1.1, nonzero Hessian determinant polynomial. -/
theorem B04 (F : AnisotropicCubic 12) :
    hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0 :=
  geometric_hessianDeterminantPolynomial_ne_zero (provedDeterminantalTangentOver ℚ) F

/-- Theorem I.1.1, its stated generic rank bound (the proved bound is stronger). -/
theorem B09 (F : AnisotropicCubic 12) : 8 ≤ genericHessianRank F.polynomial := by
  have h := R12 F
  exact (by norm_num : 8 ≤ 10).trans h

/-- Theorem I.1.1, full maximal-vertex base change, over arbitrary fields of
characteristic zero exactly as in the target. -/
theorem B15 (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 11) K) (hp : p.IsHomogeneous 3) :
    affineVertex (map (algebraMap K L) p) (hp.map _) =
      Submodule.span L ((fun v : Fin 11 → K => fun i => algebraMap K L (v i)) ''
        (affineVertex p hp : Set (Fin 11 → K))) :=
  affineVertex_baseChange p hp

/-- Theorem I.1.1, anisotropy of every rational subspace restriction. -/
theorem B16 (F : AnisotropicCubic 12) (M : Submodule ℚ (Fin 12 → ℚ))
    (_hm : 4 ≤ finrank ℚ M) : Anisotropic (subspaceCubic F M).polynomial :=
  (subspaceCubic F M).anisotropic

/-- Theorem I.1.1, its exact rank-at-most-one locus on the cubic. -/
theorem B05 (F : AnisotropicCubic 12) :
    {x ∈ cubicLocus F.polynomial |
      (hessian (geometricPolynomial F.polynomial) x).rank ≤ 1} = {0} :=
  BibleLowRank.anisotropic_on_cubic_rank_one_eq_origin
    provedSymmetricDeterminantalTangent F (by norm_num)

/-- Theorem I.1.1, every actual vector subspace of the affine singular locus. -/
theorem B19 (F : AnisotropicCubic 12)
    (L : Submodule GeometricField (GeometricPoint 12))
    (hL : (L : Set (GeometricPoint 12)) ⊆ singularLocus F.polynomial) :
    3 * finrank GeometricField L ≤ 12 :=
  BibleRestrictions.singular_subspace_finrank_bound F (by norm_num) L hL

end HessianTheorem11.Unconditional
