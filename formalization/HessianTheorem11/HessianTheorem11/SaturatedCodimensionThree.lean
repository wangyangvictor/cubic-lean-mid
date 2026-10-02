import HessianTheorem11.SaturatedOneDimensionalMiddle
import HessianTheorem11.SaturatedWeight

/-! The codimension-three case of the saturated thirteen-variable
incidence configuration is impossible. -/
noncomputable section
namespace HessianTheorem11
open Module MvPolynomial

theorem CoisotropicBasis.Data.codimension_three_saturated_impossible
    {F : GeometricPolynomial 13} {x : GeometricPoint 13}
    {T : Submodule GeometricField (GeometricPoint 13)} {m d q : ℕ}
    (D : CoisotropicBasis.Data (hessianBilinear F x) T x m d q)
    (GR : GenericRankOpenInput) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (hT : finrank GeometricField T = 10)
    (hnullity : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 6)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hdom : geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13))) =
      ((coordinatePairing (K := GeometricField) (n := 13)).orthogonal T : Set (GeometricPoint 13)))
    (Z : Set (GeometricPoint 13))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hsat : ∀ t : GeometricField, ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin,
      x+t • a ∈ Z) : False := by
  obtain ⟨rfl,rfl,rfl⟩ := D.thirteen_codimension_three_middle_one hT hnullity
  have hs := D.cubic_saturated_schur_identities GR hF hker hann hdom Z hmax hsat
  have hC : ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin, D.isotropicGramAt a = 0 :=
    fun a ha => (hs a ha).1
  have hE : ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin, D.mixedGramAt a = 0 :=
    fun a ha => D.mixedGram_zero_of_moment_zero a ((hs a ha).2 0)
  have hh := D.loweredRadialWeight_sum_nonnegative hF hsemi hker hann hC hE
  norm_num at hh

theorem thirteen_saturated_codimension_three_impossible
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (Z : Set (GeometricPoint 13)) (hzero : ∀ y ∈ Z, eval y F = 0)
    (x : GeometricPoint 13) (hx : x ∈ Z) (hgrad : gradient F x ≠ 0)
    (hxT : x ∈ affineTangentSpace Z x)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ affineTangentSpace Z x)
    (hann : affineTangentSpace Z x ≤
      kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin))
    (hT : finrank GeometricField (affineTangentSpace Z x) = 10)
    (hnullity : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 6)
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hsat : ∀ s : GeometricField, ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin,
      s • x+a ∈ Z)
    (himageTangent : affineTangentSpace (geometricClosure (gradient F '' Z)) (gradient F x) =
      LinearMap.range ((hessian F x).mulVecLin.domRestrict (affineTangentSpace Z x))) : False := by
  have hxL := self_notMem_hessian_ker_of_gradient_ne_zero hF x hgrad
  have hdom := thirteen_kernel_gradient_conormal_dominance_codimension_three GR AD F hF hsemi x
    (hzero x hx) _ hxT hxL hann hT hnullity
  have hKZ : (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13)) ⊆ Z := by
    intro a ha
    simpa using hsat 0 a ha
  have hco := thirteen_saturated_codimension_three_coisotropic GR AD F hF hsemi Z hzero x hx
    hxT hxL hann hT hnullity hKZ himageTangent
  obtain ⟨m,d,q,⟨D⟩⟩ := exists_cubic_coisotropic_basis F hF x hgrad _ hker
    (gradient_mem_conormal_of_cubic_zero F Z hzero x) hco
  apply D.codimension_three_saturated_impossible GR hF hsemi hT hnullity hker
    (fun t ht u hu v hv => hann ht u hu v hv) hdom Z hmax
  intro t a ha
  simpa using hsat 1 (t • a) (Submodule.smul_mem _ t ha)

end HessianTheorem11
