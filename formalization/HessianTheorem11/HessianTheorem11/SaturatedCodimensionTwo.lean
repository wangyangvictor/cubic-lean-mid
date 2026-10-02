import HessianTheorem11.FourInvariantExclusion
import HessianTheorem11.ScalarAlternativeExclusion
import HessianTheorem11.SaturatedFourMoments
import HessianTheorem11.ResolventAlternative

/-! The final saturated codimension-two incidence configuration is impossible.
Every operator, moment, coordinate basis and exceptional subspace is constructed
from the original cubic. -/
noncomputable section
namespace HessianTheorem11
open Module MvPolynomial NonzeroLimitTransport

theorem thirteen_saturated_codimension_two_impossible
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (SA : FormalSmoothArcInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 13)
    (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (Z : Set (GeometricPoint 13)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z)
    (hzero : ∀ y ∈ Z, eval y (geometricPolynomial F.polynomial) = 0)
    (x : GeometricPoint 13) (hx : x ∈ Z)
    (hdim : affineDimension Z =
      (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (hgrad : gradient (geometricPolynomial F.polynomial) x ≠ 0)
    (hxT : x ∈ affineTangentSpace Z x)
    (hker : LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin ≤
      affineTangentSpace Z x)
    (hann : affineTangentSpace Z x ≤ kernelQuadraticAnnihilator
      (geometricPolynomial F.polynomial)
      (LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin))
    (hT : finrank GeometricField (affineTangentSpace Z x) = 11)
    (hnullity : finrank GeometricField
      (LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin) = 5)
    (hmax : ∀ y ∈ Z, (hessian (geometricPolynomial F.polynomial) y).rank ≤
      (hessian (geometricPolynomial F.polynomial) x).rank)
    (hsat : ∀ s : GeometricField,
      ∀ a ∈ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      s • x+a ∈ Z)
    (himageTangent : affineTangentSpace
      (geometricClosure (gradient (geometricPolynomial F.polynomial) '' Z))
      (gradient (geometricPolynomial F.polynomial) x) =
      LinearMap.range ((hessian (geometricPolynomial F.polynomial) x).mulVecLin.domRestrict
        (affineTangentSpace Z x))) : False := by
  let P := geometricPolynomial F.polynomial
  have hP : P.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  have hxL := self_notMem_hessian_ker_of_gradient_ne_zero hP x hgrad
  have hdom := thirteen_kernel_gradient_conormal_dominance_codimension_two GR AD P hP hsemi x
    (hzero x hx) _ hxT hxL hann hT hnullity
  have hKZ : (LinearMap.ker (hessian P x).mulVecLin : Set (GeometricPoint 13)) ⊆ Z := by
    intro a ha
    simpa using hsat 0 a ha
  have hco := thirteen_saturated_codimension_two_coisotropic GR AD P hP hsemi Z hzero x hx
    hxT hxL hann hT hnullity hKZ himageTangent
  obtain ⟨m,d,q,⟨D⟩⟩ := exists_cubic_coisotropic_basis P hP x hgrad _ hker
    (gradient_mem_conormal_of_cubic_zero P Z hzero x) hco
  obtain ⟨rfl,rfl,rfl⟩ := D.thirteen_codimension_two_middle_four hT hnullity
  have hann' : ∀t∈affineTangentSpace Z x,
      ∀u∈LinearMap.ker (hessian P x).mulVecLin,
      ∀v∈LinearMap.ker (hessian P x).mulVecLin,polarization P t u v=0 :=
    fun t ht u hu v hv => hann ht u hu v hv
  have hsat' : ∀t : GeometricField,∀a∈LinearMap.ker (hessian P x).mulVecLin,x+t • a∈Z := by
    intro t a ha
    simpa using hsat 1 (t • a) (Submodule.smul_mem _ t ha)
  have hC : ∀a∈LinearMap.ker (hessian P x).mulVecLin,D.isotropicGramAt a=0 :=
    fun a ha => (D.cubic_saturated_schur_identities GR hP hker hann' hdom Z hmax hsat' a ha).1
  obtain ⟨η,hη⟩ := exists_ne D.radial
  have hm := D.four_moments GR hP hker hann' hdom Z hmax hsat' η
  rcases ResolventAlternative.four_dimensional_alternative D.fourBeta D.fourBeta_symm
      D.fourBeta_nondegenerate (by simp) (D.fourE hP η) (D.fourM hP)
      (D.fourM_selfAdjoint hP) hm with hi|hs
  · obtain ⟨W,hW,_,heW,hMW⟩ := hi
    exact thirteen_four_invariant_subspace_impossible boundary bigCell F D hker hann' hC
      η hη W hW heW hMW
  · obtain ⟨he,α,hα⟩ := hs
    exact D.four_scalar_alternative_impossible GR SA hP hsemi hker hann' Z hZ hirred hx
      rfl hdim hmax hdom hC η hη he α hα

end HessianTheorem11
