import CubicTenVariables.GaussGraph
import CubicTenVariables.GaussImageGeometry

/-! The normal projection of the actual affine Gauss graph has exactly
the actual gradient-image closure. This uses scalar stability of the
gradient image, proved using square roots in the geometric field. -/

noncomputable section
namespace CubicTenVariables.GaussGraph
open MvPolynomial HessianTheorem11
open ReducedKernelTangent TerminalFiberCoordinates AffineProductGeometry

theorem normal_parametrization_image {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) :
    polynomialMap (normalProjection n) ''
      (polynomialMap (parametrization F) '' source F) =
        gradient F '' polynomialHypersurface F := by
  ext v
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    rw [parametrization_normal]
    exact GaussImageGeometry.gradient_image_isAffineCone F hF
      (fiberProjection n 1 q 0) _ ⟨baseProjection n 1 q, hq, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨polynomialMap (parametrization F) (sourcePair x 1),
      ⟨sourcePair x 1, (sourcePair_mem F x 1).mpr hx, rfl⟩, ?_⟩
    simp

theorem normal_projection_closure {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) :
    geometricClosure (polynomialMap (normalProjection n) '' graph F) =
      GaussImageGeometry.gradientImage F := by
  apply Set.Subset.antisymm
  · apply geometricClosure_subset_closed _ (GaussImageGeometry.gradientImage_closed F)
    have h := polynomialMap_image_closure_subset (normalProjection n)
      (polynomialMap (parametrization F) '' source F)
    rw [normal_parametrization_image F hF] at h
    exact h
  · change geometricClosure (gradient F '' polynomialHypersurface F) ⊆ _
    apply geometricClosure_mono
    rw [← normal_parametrization_image F hF]
    exact Set.image_mono (subset_geometricClosure _)

theorem normal_projection_dimension {n : ℕ} (F : RationalPolynomial n)
    (hF : F.IsHomogeneous 3) (hi : Irreducible (geometricPolynomial F))
    (hn : 0 < n) :
    affineDimension (geometricClosure (polynomialMap (normalProjection n) ''
      graph (geometricPolynomial F))) =
        ((genericHessianRank F - 1 : ℕ) : Dimension) := by
  rw [normal_projection_closure _ (geometric_homogeneous hF)]
  exact GaussImageGeometry.gradient_image_dimension F hF hi hn

theorem anisotropic_normal_projection_dimension {n : ℕ} (F : AnisotropicCubic n)
    (hn : 4 ≤ n) :
    affineDimension (geometricClosure (polynomialMap (normalProjection n) ''
      graph (geometricPolynomial F.polynomial))) =
        ((genericHessianRank F.polynomial - 1 : ℕ) : Dimension) :=
  normal_projection_dimension F.polynomial F.homogeneous
    (Unconditional.cubicGeometricIrreducibility F hn) (by omega)

end CubicTenVariables.GaussGraph
