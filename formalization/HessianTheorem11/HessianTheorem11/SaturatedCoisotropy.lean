import HessianTheorem11.GradientCoisotropy
import HessianTheorem11.KernelQuadraticDominance
import HessianTheorem11.QuadraticLineImage

/-! Codimension-three dominance and coisotropy for the actual saturated
incidence base. Generic image-tangent equality is kept as the precise point
property needed from generic smoothness. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

theorem thirteen_kernel_gradient_conormal_dominance_codimension_three
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : GeometricPoint 13) (hx : eval x F = 0)
    (T : Submodule GeometricField (GeometricPoint 13)) (hxT : x ∈ T)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hann : T ≤ kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin))
    (hdT : finrank GeometricField T = 10)
    (hnullity : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 6) :
    geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13))) =
      ((coordinatePairing (K := GeometricField) (n := 13)).orthogonal T : Set (GeometricPoint 13)) := by
  have he := kernelGradientSpan_eq_conormal_of_thirteen F hF hsemi x hx T hxT hxL hann
    (by rw [hdT, hnullity])
  have hd : finrank GeometricField
      (kernelGradientSpan F (LinearMap.ker (hessian F x).mulVecLin)) = 3 := by
    rw [he, LinearMap.BilinForm.finrank_orthogonal coordinatePairing_nondegenerate
      coordinatePairing_reflexive, hdT]
    simp
  rw [thirteen_kernel_gradient_imageClosure_eq_span_of_nullity_six GR AD F hF hsemi x hx
    hxL hnullity hd, he]

theorem thirteen_saturated_codimension_three_coisotropic
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (Z : Set (GeometricPoint 13)) (hzero : ∀ y ∈ Z, eval y F = 0)
    (x : GeometricPoint 13) (hx : x ∈ Z)
    (hxT : x ∈ affineTangentSpace Z x)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hann : affineTangentSpace Z x ≤
      kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin))
    (hdT : finrank GeometricField (affineTangentSpace Z x) = 10)
    (hnullity : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 6)
    (hsaturation : (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13)) ⊆ Z)
    (himageTangent : affineTangentSpace (geometricClosure (gradient F '' Z)) (gradient F x) =
      LinearMap.range ((hessian F x).mulVecLin.domRestrict (affineTangentSpace Z x))) :
    (coordinatePairing (K := GeometricField) (n := 13)).orthogonal (affineTangentSpace Z x) ≤
      LinearMap.range ((hessian F x).mulVecLin.domRestrict (affineTangentSpace Z x)) := by
  apply gradient_coisotropic_of_conormal_contained_in_image F Z hzero x _ himageTangent
  rw [← thirteen_kernel_gradient_conormal_dominance_codimension_three GR AD F hF hsemi x
    (hzero x hx) _ hxT hxL hann hdT hnullity]
  exact geometricClosure_mono (Set.image_mono hsaturation)

theorem thirteen_kernel_gradient_conormal_dominance_codimension_two
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : GeometricPoint 13) (hx : eval x F = 0)
    (T : Submodule GeometricField (GeometricPoint 13)) (hxT : x ∈ T)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hann : T ≤ kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin))
    (hdT : finrank GeometricField T = 11)
    (hnullity : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 5) :
    geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13))) =
      ((coordinatePairing (K := GeometricField) (n := 13)).orthogonal T : Set (GeometricPoint 13)) := by
  let L := LinearMap.ker (hessian F x).mulVecLin
  let B := submoduleCoordinateMatrix L
  let Q : Fin 13 → GeometricPolynomial (finrank GeometricField L) :=
    fun i => PolynomialRestriction.restrict B (pderiv i F)
  have hQ : ∀ i, (Q i).IsHomogeneous 2 := fun i =>
    PolynomialRestriction.homogeneous_restrict B _ hF.pderiv
  have himage : polynomialMap Q '' Set.univ = gradient F '' (L : Set (GeometricPoint 13)) :=
    polynomialMap_restrict_submodule_image (fun i => pderiv i F) L
  have he := kernelGradientSpan_eq_conormal_of_thirteen F hF hsemi x hx T hxT hxL hann
    (by rw [hdT, hnullity])
  have hd : finrank GeometricField (Submodule.span GeometricField
      (polynomialMap Q '' Set.univ)) = 2 := by
    rw [himage]
    change finrank GeometricField (kernelGradientSpan F L) = 2
    rw [he, LinearMap.BilinForm.finrank_orthogonal coordinatePairing_nondegenerate
      coordinatePairing_reflexive, hdT]
    simp
  have hclosure := quadratic_imageClosure_eq_span_of_span_finrank_two GR AD Q hQ hd
  rw [himage] at hclosure
  change geometricClosure (gradient F '' (L : Set (GeometricPoint 13))) = _
  rw [hclosure]
  exact congrArg (fun S : Submodule GeometricField (GeometricPoint 13) =>
    (S : Set (GeometricPoint 13))) he

theorem thirteen_saturated_codimension_two_coisotropic
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (Z : Set (GeometricPoint 13)) (hzero : ∀ y ∈ Z, eval y F = 0)
    (x : GeometricPoint 13) (hx : x ∈ Z)
    (hxT : x ∈ affineTangentSpace Z x)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hann : affineTangentSpace Z x ≤
      kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin))
    (hdT : finrank GeometricField (affineTangentSpace Z x) = 11)
    (hnullity : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 5)
    (hsaturation : (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13)) ⊆ Z)
    (himageTangent : affineTangentSpace (geometricClosure (gradient F '' Z)) (gradient F x) =
      LinearMap.range ((hessian F x).mulVecLin.domRestrict (affineTangentSpace Z x))) :
    (coordinatePairing (K := GeometricField) (n := 13)).orthogonal (affineTangentSpace Z x) ≤
      LinearMap.range ((hessian F x).mulVecLin.domRestrict (affineTangentSpace Z x)) := by
  apply gradient_coisotropic_of_conormal_contained_in_image F Z hzero x _ himageTangent
  rw [← thirteen_kernel_gradient_conormal_dominance_codimension_two GR AD F hF hsemi x
    (hzero x hx) _ hxT hxL hann hdT hnullity]
  exact geometricClosure_mono (Set.image_mono hsaturation)

end HessianTheorem11
