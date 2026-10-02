import HessianTheorem11.PureCubeExclusion
import HessianTheorem11.RadialDefectLimit
import HessianTheorem11.SingularRadialEquality

/-! Excluding defect one for the actual thirteen-variable concentrated
base. The base is transported with the same invertible substitution as the
polynomial, so its dimension, rank bound and rank witness are preserved. -/
noncomputable section
set_option maxRecDepth 2048
namespace HessianTheorem11
open MvPolynomial Module NonzeroLimitTransport PolynomialRestriction

theorem incidence_thirteen_radial_defect_ne_one
    (MR : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField) (AD : AffineHypersurfaceDimensionInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 13)
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0)
    (C : IncidenceConcentration (geometricPolynomial F.polynomial))
    (hsize : C.baseDimension + C.nullity = 16)
    (x : GeometricPoint 13) (hx : x ∈ C.base)
    (hrank : (hessian (geometricPolynomial F.polynomial) x).rank = C.rank)
    (T : Submodule GeometricField (GeometricPoint 13))
    (hdimT : finrank GeometricField T = C.baseDimension)
    (E : SmoothRadialSupportData (geometricPolynomial F.polynomial) x T) :
    E.defect ≠ 1 := by
  classical
  intro hc
  let f := geometricPolynomial F.polynomial
  have hf : f.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  have he : (finrank GeometricField T : ℤ) - ((hessian f x).rank : ℤ) = 3 := by
    rw [hdimT, hrank]
    have h := C.rank_nullity
    omega
  obtain ⟨ht, hr, _⟩ := E.thirteen_defect_one_dimensions boundary bigCell F he hc
  have hbaseDim : C.baseDimension = 11 := by omega
  have hbaseRank : C.rank = 8 := by omega
  let M := HessianTheorem11.basisMatrix E.adapted.basis
  let w := smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices
  have hM : Function.Injective M.mulVec := basisMatrix_injective E.adapted.basis
  have hsum : ∑ i, w i = 0 := by
    change ∑ i, smoothRadialWeight E.adapted.radial
      E.adapted.tangentIndices E.adapted.kernelIndices i = 0
    rw [E.total_weight_eq, he, hc]
    norm_num
  obtain ⟨U, hUdet, hUupper, hUtransport⟩ := anisotropic_zeroWeightPart_transport boundary bigCell
    F (by decide) M hM w hsum E.support_nonnegative
  have hU : Function.Injective U.mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det U).mpr
    rw [hUdet]
    exact isUnit_one
  let N := M * U
  have hN : Function.Injective N.mulVec := by
    intro a b hab
    apply hU
    apply hM
    simpa only [N, Matrix.mulVec_mulVec] using hab
  let L := frameEquiv N hN
  let G := zeroWeightPart (restrict M f) w
  have hGeq : G = restrict N f := hUtransport.trans (PolynomialWeightTransport.restrict_restrict M U f)
  have hG : G.IsHomogeneous 3 := zeroWeightPart_homogeneous (homogeneous_restrict M f hf) w
  have hGdet : hessianDeterminantPolynomial G ≠ 0 := by
    rw [hGeq]
    exact SingularRadialEquality.restrict_hessianDeterminant_ne_zero f hdet N hN
  obtain ⟨c, hcL, hcT, hsplit⟩ := E.pure_cube_split_of_defect_one G hG
    (zeroWeightPart_weights (restrict M f) w) hc
  let Z := L.symm '' C.base
  let e := PolynomialCoordinateEquiv.ofLinearEquiv L.symm
  have heZ : e.forwardMap '' C.base = Z := by
    rw [PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap]
  have hZclosed : AlgebraicallyClosedSet Z := by
    rw [← heZ]
    exact (e.algebraicallyClosedSet_image_iff C.base).mpr C.closed
  have hZirred : GeometricallyIrreducible Z := by
    rw [← heZ]
    exact (e.geometricallyIrreducible_image_iff C.base).mpr C.irreducible
  have hZdim : affineDimension Z = 11 := by
    rw [← heZ, e.affineDimension_image, C.dimension_base, hbaseDim]
    norm_num
  have hGrank (y : GeometricPoint 13) : (hessian G y).rank = (hessian f (L y)).rank := by
    rw [hGeq]
    have hh := BasisHessianTransport.hessian_rank_restrict
      (SingularRadialEquality.matrixBasis N hN) f y
    simpa only [SingularRadialEquality.matrixBasis_matrix, frameEquiv_apply] using hh
  have hGzero : ∀ y ∈ Z, eval y G = 0 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hGeq, eval_restrict]
    change eval (L (L.symm z)) f = 0
    rw [L.apply_symm_apply]
    exact C.contained z hz
  have hGbound : ∀ y ∈ Z, (hessian G y).rank ≤ 8 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hGrank, L.apply_symm_apply]
    simpa only [hbaseRank] using C.maximal_rank z hz
  let y : GeometricPoint 13 := Pi.single E.adapted.radial 1
  have hy : L y = x := by
    change (M * U).mulVec y = x
    rw [← Matrix.mulVec_mulVec]
    have hfix := hUupper.fixes_minimum_column E.adapted.radial
      (E.minimum_weight _ (Or.inr rfl))
    rw [hfix]
    ext i
    rw [Matrix.mulVec_single_one]
    change E.adapted.basis E.adapted.radial i = x i
    rw [E.adapted.radial_eq]
  have hyZ : y ∈ Z := by
    refine ⟨x, hx, ?_⟩
    apply L.injective
    rw [L.apply_symm_apply, hy]
  have hyc : y c = 0 := by
    have hcr : c ≠ E.adapted.radial := by rintro rfl; exact hcT E.adapted.radial_mem_tangent
    simp [y, hcr, Pi.single_apply]
  exact pure_cube_rank_eight_base_impossible MR DT FI AD G hG hGdet c _ hsplit Z
    hZclosed hZirred hZdim hGzero hGbound ⟨y,hyZ,hyc,by rw [hGrank,hy]; exact hr⟩

end HessianTheorem11
