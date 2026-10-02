import HessianTheorem11.TangentBundleGeometry
import HessianTheorem11.AffineHypersurfaceDimension
import HessianTheorem11.RankClosure
import HessianTheorem11.CubicDivisorPoint

/-! Actual containment and dimension saturation of the tangent union of
a singular component whose tangent spaces equal the Hessian kernels.
The local normal-map ranks remain explicit hypotheses of this reduction. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

theorem singular_kernelBundle_image_subset_cubic
    (SA : FormalSmoothArcInput) {n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z O : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hO : O ⊆ Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (hsmooth : ∀ x ∈ O,
      affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (hT : ∀ x ∈ O, affineTangentSpace Z x = LinearMap.ker (hessian F x).mulVecLin) :
    pairRight '' kernelBundle (hessianLinearMap F hF) O ⊆ polynomialHypersurface F := by
  rintro _ ⟨p, hp, rfl⟩
  apply SingularFormalArc.eval_tangent_eq_zero SA F hF Z hZ hirred hsing
    (pairLeft p) (hO hp.1) (hsmooth _ hp.1)
  rw [hT _ hp.1]
  exact hp.2

theorem singular_kernelBundle_imageClosure_eq_cubic
    (KB : KernelBundleTangentImageInput) (SA : FormalSmoothArcInput)
    (AD : AffineHypersurfaceDimensionInput) {n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (hFi : Irreducible F)
    (Z O : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hO : RelativelyOpenSet Z O)
    (hOZ : O ⊆ Z) (hdense : geometricClosure O = Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (hsmooth : ∀ x ∈ O,
      affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (hT : ∀ x ∈ O, affineTangentSpace Z x = LinearMap.ker (hessian F x).mulVecLin)
    (ell : ℕ) (hell : ∀ y ∈ O,
      finrank GeometricField (LinearMap.ker (hessian F y).mulVecLin) = ell)
    (x : GeometricPoint n) (hx : x ∈ O)
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x)
    (hlarge : n - 1 ≤ finrank GeometricField (affineTangentSpace Z x) +
      finrank GeometricField (LinearMap.range
        ((hessian F v).mulVecLin.domRestrict (affineTangentSpace Z x)))) :
    geometricClosure (pairRight '' kernelBundle (hessianLinearMap F hF) O) =
      polynomialHypersurface F := by
  apply equal_hypersurface_of_dimension_ge AD F hFi _
    (algebraicallyClosedSet_geometricClosure _)
  · exact geometricClosure_subset_closed
      (singular_kernelBundle_image_subset_cubic SA F hF Z O hZ hirred hOZ hsing hsmooth hT)
      (polynomialHypersurface_closed F)
  · have hb := tangent_union_dimension_lower_bound KB SA F hF Z O hZ hirred hO hdense
      hsing ell hell x hx (hOZ hx) (hsmooth x hx) (hT x hx) v hv
    apply le_trans ?_ hb
    exact_mod_cast hlarge

/-- A rank bound on all actual tangent vectors extends to the whole cubic
once the actual tangent union has dimension at least `n-1`. This concludes
in the rank of the Hessian over the actual function field of `(F)`. -/
theorem generic_rank_le_of_singular_tangent_union
    (KB : KernelBundleTangentImageInput) (SA : FormalSmoothArcInput)
    (AD : AffineHypersurfaceDimensionInput) (KI : KernelBundleInput)
    (MR : GenericMatrixRankInput) {n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (hFi : Irreducible F)
    (Z O : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hO : RelativelyOpenSet Z O)
    (hOZ : O ⊆ Z) (hdense : geometricClosure O = Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (hsmooth : ∀ x ∈ O,
      affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (hT : ∀ x ∈ O, affineTangentSpace Z x = LinearMap.ker (hessian F x).mulVecLin)
    (ell : ℕ) (hell : ∀ y ∈ O,
      finrank GeometricField (LinearMap.ker (hessian F y).mulVecLin) = ell)
    (x : GeometricPoint n) (hx : x ∈ O)
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x)
    (hlarge : n - 1 ≤ finrank GeometricField (affineTangentSpace Z x) +
      finrank GeometricField (LinearMap.range
        ((hessian F v).mulVecLin.domRestrict (affineTangentSpace Z x))))
    (r : ℕ) (hrank : ∀ y ∈ O, ∀ w ∈ affineTangentSpace Z y, (hessian F w).rank ≤ r) :
    geometricCubicGenericRank F ≤ r := by
  have heq := singular_kernelBundle_imageClosure_eq_cubic KB SA AD F hF hFi Z O hZ hirred
    hO hOZ hdense hsing hsmooth hT ell hell x hx v hv hlarge
  have hb := KI.closure_irreducible (hessianLinearMap F hF) Z O hZ hirred hO hdense ell hell
  have hb' := (geometricallyIrreducible_closure_iff _).mp hb
  have hp := hb'.polynomialMap_image (pairRightPolynomials n n)
  rw [polynomialMap_pairRightPolynomials] at hp
  have hbound := polynomialMatrix_rank_le_on_closure MR
    (pairRight '' kernelBundle (hessianLinearMap F hF) O) hp (hessianPolynomial F) r
    (by
      rintro _ ⟨p, hp, rfl⟩
      apply hrank _ hp.1
      rw [hT _ hp.1]
      exact hp.2)
  rw [heq] at hbound
  let I : Ideal (GeometricPolynomial n) := Ideal.span {F}
  letI : I.IsPrime := (Ideal.span_singleton_prime hFi.ne_zero).mpr hFi.prime
  obtain ⟨y, hy, hyr⟩ := genericMatrixRank_attained MR I (hessianPolynomial F)
  change (evaluatedMatrix (hessianPolynomial F) y).rank = geometricCubicGenericRank F at hyr
  rw [← hyr]
  apply hbound y
  rw [polynomialHypersurface_eq_zeroLocus]
  exact hy

end HessianTheorem11
