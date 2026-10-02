import HessianTheorem11.SingularRadial
import HessianTheorem11.TextbookGeometry
import HessianTheorem11.SingularAssembly

/-! Applying the two general textbook AG inputs to the actual singular locus.
The only additional hypothesis here is geometric weight semistability. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

theorem singular_equation_zeroSet {n : ℕ} (F : RationalPolynomial n) :
    finiteEquationZeroSet (fun i => pderiv i (geometricPolynomial F)) = singularLocus F := by
  ext x
  simp only [finiteEquationZeroSet, singularLocus, gradient, Set.mem_setOf_eq,
    funext_iff, Pi.zero_apply]

def singularComponentCover (AG : FiniteQuadraticConeCoverInput)
    {n : ℕ} (F : RationalPolynomial n) (hF : F.IsHomogeneous 3) :
    HomogeneousConeComponentCover (fun i => pderiv i (geometricPolynomial F))
      (hessianLinearMap (geometricPolynomial F) (geometric_homogeneous hF)) :=
  AG.chooseCover _ (fun _ => (geometric_homogeneous hF).pderiv) _

theorem singularComponentCover_radial
    (AG : FiniteQuadraticConeCoverInput) (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ} (F : RationalPolynomial n) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable (geometricPolynomial F))
    (i : Fin (singularComponentCover AG F hF).count) :
    let C := singularComponentCover AG F hF
    C.component i ⊆ {0} ∨
      (affineDimension (C.component i) =
        (finrank GeometricField (affineTangentSpace (C.component i) (C.point i)) : Dimension) ∧
      finrank GeometricField (affineTangentSpace (C.component i) (C.point i)) + 3 ≤
        2 * (hessian (geometricPolynomial F) (C.point i)).rank) := by
  classical
  let C := singularComponentCover AG F hF
  change C.component i ⊆ {0} ∨ _
  by_cases ho : C.component i ⊆ {0}
  · exact Or.inl ho
  right
  obtain ⟨hx, hmem, hdim, hrad, _⟩ := C.nonorigin_point_properties i ho
  refine ⟨hdim, ?_⟩
  have hs : ∀ y ∈ C.component i, gradient (geometricPolynomial F) y = 0 := by
    intro y hy
    have hz := C.component_subset i hy
    rwa [singular_equation_zeroSet] at hz
  apply singular_radial_of_tensor_vanishing (geometricPolynomial F)
    (geometric_homogeneous hF) hsemi (C.point i) hx
    (affineTangentSpace (C.component i) (C.point i)) hrad
    (affineTangentSpace_le_hessian_ker _ _ hs _)
  intro t ht u hu v hv
  have hp := C.tangent_kernel_pairing DT (hessian_symmetric (geometricPolynomial F))
    i ho t ht u hu v hv
  rw [polarization_swap_first, polarization_swap_last (geometric_homogeneous hF)]
  exact hp

theorem singularDimension_thirteen_le_seven_of_semistable
    (AG : FiniteQuadraticConeCoverInput) (DT : SymmetricDeterminantalTangentInput)
    (F : RationalPolynomial 13) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable (geometricPolynomial F)) : singularDimension F ≤ 7 := by
  let C := singularComponentCover AG F hF
  apply singularDimension_thirteen_le_seven_of_radial_component_inputs F
    C.component C.point
  · rw [← singular_equation_zeroSet]
    exact C.covers
  · exact singularComponentCover_radial AG DT F hF hsemi

end HessianTheorem11
