import CubicTenVariables.GaussTangentRank
import HessianTheorem11.UnconditionalDimensionResults
import HessianTheorem11.SingularNormalEquations
import HessianTheorem11.KernelSaturation

/-!
The actual gradient image of a geometric cubic cone is a cone. For an
irreducible rational cubic its closure has dimension r_X-1, where r_X
is the actual maximum Hessian rank on the cubic. The generic smooth,
map-rank and Hessian-rank locus is constructed by existing proved results;
no Gauss-image dimension formula is an input.
-/

noncomputable section
namespace CubicTenVariables.GaussImageGeometry
open MvPolynomial HessianTheorem11 Module

/-- Closure of the actual affine gradient image on the actual cubic. -/
def gradientImage {n : ℕ} (F : GeometricPolynomial n) : Set (GeometricPoint n) :=
  geometricClosure (gradient F '' polynomialHypersurface F)

theorem gradientImage_closed {n : ℕ} (F : GeometricPolynomial n) :
    AlgebraicallyClosedSet (gradientImage F) := algebraicallyClosedSet_geometricClosure _

theorem gradientImage_irreducible {n : ℕ} (F : GeometricPolynomial n)
    (hF : Irreducible F) : GeometricallyIrreducible (gradientImage F) := by
  apply (geometricallyIrreducible_closure_iff _).mpr
  exact (polynomialHypersurface_irreducible F hF).polynomialMap_image (fun i => pderiv i F)

/-- Square roots in the geometric field make the degree-two gradient
image stable under every scalar, before taking closure. -/
theorem gradient_image_isAffineCone {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) : IsAffineCone (gradient F '' polynomialHypersurface F) := by
  rintro a v ⟨x, hx, rfl⟩
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (by norm_num : 0 < (2 : ℕ))
  refine ⟨b • x, ?_, ?_⟩
  · change eval (b • x) F = 0
    rw [BibleLowRank.eval_cubic_smul F hF]
    change eval x F = 0 at hx
    rw [hx, mul_zero]
  · ext i
    change eval (b • x) (pderiv i F) = a * eval x (pderiv i F)
    rw [SingularNormalEquations.eval_quadratic_smul _ hF.pderiv, hb]

theorem gradientImage_isAffineCone {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) : IsAffineCone (gradientImage F) :=
  (gradient_image_isAffineCone F hF).closure

/-- The affine gradient-image dimension is the maximum Hessian rank on
the cubic minus one. All generic-open and tangent-space facts are proved. -/
theorem gradient_image_dimension {n : ℕ} (F : RationalPolynomial n)
    (hF : F.IsHomogeneous 3) (hirred : Irreducible (geometricPolynomial F))
    (hn : 0 < n) :
    affineDimension (gradientImage (geometricPolynomial F)) =
      ((genericHessianRank F - 1 : ℕ) : Dimension) := by
  let f := geometricPolynomial F
  let Y := cubicLocus F
  have hY : AlgebraicallyClosedSet Y := polynomialHypersurface_closed _
  have hiY : GeometricallyIrreducible Y := polynomialHypersurface_irreducible _ hirred
  obtain ⟨G⟩ := Unconditional.genericRankOpen.choose Y hY hiY
    (fun i => pderiv i f) (hessianLinearMap f (geometric_homogeneous hF))
  obtain ⟨x, hx⟩ := G.nonempty
  have hbase : G.baseDimension = n - 1 := by
    have he := G.dimension_base.symm.trans (Unconditional.hypersurfaceDimension.hypersurface
      f hirred)
    exact_mod_cast he
  have hgrad : gradient f x ≠ 0 := by
    intro hg
    have hdiff : polynomialDifferential f x = 0 := by
      apply LinearMap.ext
      intro v
      change polynomialDifferential f x v = 0
      have he : ∀ i, eval x (pderiv i f) = 0 := congrFun hg
      simp only [polynomialDifferential_apply, he, zero_mul, Finset.sum_const_zero]
    have ht : affineTangentSpace Y x = ⊤ := by
      rw [affineTangentSpace_cubicLocus_eq_ker F hirred x (G.subset hx), hdiff,
        LinearMap.ker_zero]
    have hs := G.smooth x hx
    rw [ht, finrank_top] at hs
    simp only [finrank_pi, Fintype.card_fin] at hs
    omega
  have hrank : (hessian f x).rank = genericHessianRank F := by
    apply le_antisymm (rank_le_genericHessianRank F (G.subset hx))
    apply csSup_le'
    rintro r ⟨y, hy, rfl⟩
    exact G.maximal_rank x hx y hy
  have ht := GaussTangentRank.hessian_affineTangent_rank_add_one F hF hirred
    x (G.subset hx) hgrad
  have hd := G.differential_rank x hx
  rw [polynomialMapDifferential_gradient] at hd
  change finrank GeometricField (LinearMap.range
    ((hessian f x).mulVecLin.domRestrict (affineTangentSpace Y x))) + 1 =
      (hessian f x).rank at ht
  rw [hd, hrank] at ht
  have he : G.imageDimension = genericHessianRank F - 1 := by omega
  change affineDimension (geometricClosure (polynomialMap (fun i => pderiv i f) '' Y)) = _
  rw [G.dimension_image, he]

/-- The anisotropic source condition supplies geometric irreducibility
internally, so this application has no absolute-irreducibility input. -/
theorem anisotropic_gradient_image_dimension {n : ℕ} (F : AnisotropicCubic n)
    (hn : 4 ≤ n) :
    affineDimension (gradientImage (geometricPolynomial F.polynomial)) =
      ((genericHessianRank F.polynomial - 1 : ℕ) : Dimension) :=
  gradient_image_dimension F.polynomial F.homogeneous
    (Unconditional.cubicGeometricIrreducibility F hn) (by omega)

end CubicTenVariables.GaussImageGeometry
