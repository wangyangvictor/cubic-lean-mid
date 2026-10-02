import HessianTheorem11.GradedCubicRank
import HessianTheorem11.QuadraticCoordinateTransport
import HessianTheorem11.SingularPositiveNormalForm
import HessianTheorem11.SingularNormalPairing

/-! The twelve-variable equality limit is the actual graded cubic in
five normal and six nonradial tangent coordinates. All coordinate,
homogeneity, irreducibility and Hessian determinant premises are derived.
The remaining local premises are its quadratic identity and independence. -/
noncomputable section
set_option maxRecDepth 2048
namespace HessianTheorem11.SingularRadialNormalForm
open MvPolynomial Module Matrix SingularNormalEquations
open SingularPositiveNormalForm
variable {F : GeometricPolynomial 12} {x : GeometricPoint 12}
variable {T : Submodule GeometricField (GeometricPoint 12)}

/-- There is no complementary kernel block in twelve variables. -/
theorem EqualityData.twelve_indices_eq (D : EqualityData 5 F x T) :
    D.flag.tangentIndices = D.flag.kernelIndices := by
  classical
  have hfull : D.flag.tangentIndices ∪ D.flag.kernelIndicesᶜ = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa only [Fintype.card_fin] using D.twelve_active_of_rank_five
  apply Finset.Subset.antisymm D.flag.indices_nested
  intro i hi
  have hu : i ∈ D.flag.tangentIndices ∪ D.flag.kernelIndicesᶜ := by rw [hfull]; simp
  exact (Finset.mem_union.mp hu).resolve_right (fun hh => Finset.mem_compl.mp hh hi)

theorem EqualityData.twelve_tangent_card (D : EqualityData 5 F x T) :
    D.flag.tangentIndices.card = 7 := by
  have hh := D.weight_sum
  rw [sum_singularRadialWeight, ← D.twelve_indices_eq] at hh
  omega

theorem EqualityData.twelve_normal_card (D : EqualityData 5 F x T) :
    D.flag.tangentIndicesᶜ.card = 5 := by
  rw [Finset.card_compl, Fintype.card_fin, D.twelve_tangent_card]

theorem EqualityData.twelve_nonradial_card (D : EqualityData 5 F x T) :
    (D.flag.tangentIndices.erase D.flag.radial).card = 6 := by
  rw [Finset.card_erase_of_mem D.flag.radial_mem, D.twelve_tangent_card]

theorem EqualityData.twelve_coordinates (D : EqualityData 5 F x T) :
    Nonempty (GradedIndexCoordinates D.flag.tangentIndices D.flag.radial 5 6) :=
  GradedIndexCoordinates.exists_coordinates _ _ D.flag.radial_mem
    D.twelve_normal_card D.twelve_nonradial_card

theorem EqualityData.twelve_limit_weights (D : EqualityData 5 F x T) :
    ∀ d ∈ D.limit.support,
      monomialWeight (singularRadialWeight D.flag.radial D.flag.tangentIndices D.flag.tangentIndices) d = 0 := by
  have hh := NonzeroLimitTransport.zeroWeightPart_weights
    (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix D.flag.basis) F)
    (singularRadialWeight D.flag.radial D.flag.tangentIndices D.flag.kernelIndices)
  rw [← D.twelve_indices_eq] at hh
  unfold EqualityData.limit
  rw [← D.twelve_indices_eq]
  exact hh

/-- Every actual typed normal tuple reconstructs the same equality limit. -/
theorem EqualityData.twelve_limit_eq_graded (D : EqualityData 5 F x T) (hF : F.IsHomogeneous 3)
    (C : GradedIndexCoordinates D.flag.tangentIndices D.flag.radial 5 6)
    (q : MvPolynomial (↑D.flag.tangentIndicesᶜ : Type) GeometricField)
    (p : (↑D.flag.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) GeometricField)
    (hqe : rename (fun i : (↑D.flag.tangentIndicesᶜ : Type) => (i : Fin 12)) q =
      normalQuadratic D.limit D.flag.radial)
    (hpe : ∀ i, rename (fun j : (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) =>
      (j : Fin 12)) (p i) = normalMapComponent D.limit D.flag.radial D.flag.tangentIndices i) :
    rename C.equiv (GradedCubic.cubic (C.normalPolynomial q) (C.normalTuple p)) = D.limit := by
  rw [C.rename_cubic]
  simp_rw [hqe, hpe]
  rw [Finset.sum_coe_sort D.flag.tangentIndicesᶜ
    (fun i => X i * normalMapComponent D.limit D.flag.radial D.flag.tangentIndices i)]
  have he := exact_normal_form D.limit (D.limit_homogeneous hF) D.flag.radial
    D.flag.tangentIndices D.flag.tangentIndices D.flag.radial_mem (Finset.Subset.refl _)
    D.twelve_limit_weights
  rw [complementaryPart_eq_zero D.limit (D.limit_homogeneous hF) D.flag.radial
    D.flag.tangentIndices D.flag.radial_mem D.twelve_limit_weights, add_zero] at he
  exact he.symm

theorem EqualityData.twelve_normal_det (D : EqualityData 5 F x T)
    (q : MvPolynomial (↑D.flag.tangentIndicesᶜ : Type) GeometricField)
    (hqe : rename (fun i : (↑D.flag.tangentIndicesᶜ : Type) => (i : Fin 12)) q =
      normalQuadratic D.limit D.flag.radial) : (quadraticHessian q).det ≠ 0 := by
  classical
  apply QuadraticBlockRank.typed_normal_det_ne_zero D.flag.tangentIndices q
  rw [hqe, Fintype.card_coe, D.twelve_normal_card]
  exact D.normal_rank.ge

/-- All source-specific geometric premises except independence and the
formal-arc normal relation have been discharged from the equality data. -/
theorem EqualityData.twelve_impossible_of_normal_data
    (MR : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (D : EqualityData 5 F x T) (hF : F.IsHomogeneous 3)
    (q : MvPolynomial (↑D.flag.tangentIndicesᶜ : Type) GeometricField)
    (hq : q.IsHomogeneous 2)
    (p : (↑D.flag.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) GeometricField)
    (hp : ∀ i, (p i).IsHomogeneous 2)
    (hqe : rename (fun i : (↑D.flag.tangentIndicesᶜ : Type) => (i : Fin 12)) q =
      normalQuadratic D.limit D.flag.radial)
    (hpe : ∀ i, rename (fun j : (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) =>
      (j : Fin 12)) (p i) = normalMapComponent D.limit D.flag.radial D.flag.tangentIndices i)
    (hrel : TangentHessianRank.quadraticRelation (quadraticHessian q)⁻¹ p = 0)
    (hlin : LinearIndependent GeometricField p) : False := by
  classical
  obtain ⟨C⟩ := D.twelve_coordinates
  have he := D.twelve_limit_eq_graded hF C q p hqe hpe
  have hdq := D.twelve_normal_det q hqe
  have hdn := C.normalPolynomial_det_ne_zero q hdq
  apply GradedCubic.twelve_graded_cubic_impossible_of_independence MR DT FI GR AD
    C.equiv (C.normalPolynomial q) (C.normalPolynomial_homogeneous q hq)
    hdn
    (C.normalTuple p) (C.normalTuple_homogeneous p hp)
    (C.normalTuple_relation q p hrel) (C.normalTuple_independent p hlin)
  · rw [he]
    exact D.limit_irreducible
  · rw [he]
    exact D.limit_hessianDeterminant_ne_zero


theorem EqualityData.twelve_full_kernel (D : EqualityData 5 F x T) :
    T = LinearMap.ker (hessian F x).mulVecLin := by
  calc
    T = Submodule.span GeometricField
        (D.flag.basis '' (D.flag.tangentIndices : Set (Fin 12))) := D.flag.tangent_span.symm
    _ = Submodule.span GeometricField
        (D.flag.basis '' (D.flag.kernelIndices : Set (Fin 12))) := by rw [D.twelve_indices_eq]
    _ = _ := D.flag.kernel_span

theorem EqualityData.twelve_exists_typed_normal_data (D : EqualityData 5 F x T)
    (hF : F.IsHomogeneous 3) :
    ∃ q : MvPolynomial (↑D.flag.tangentIndicesᶜ : Type) GeometricField,
    ∃ p : (↑D.flag.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) GeometricField,
      q.IsHomogeneous 2 ∧ (∀ i, (p i).IsHomogeneous 2) ∧
      rename (fun i : (↑D.flag.tangentIndicesᶜ : Type) => (i : Fin 12)) q =
        normalQuadratic D.limit D.flag.radial ∧
      (∀ i, rename (fun j : (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) =>
        (j : Fin 12)) (p i) = normalMapComponent D.limit D.flag.radial D.flag.tangentIndices i) := by
  obtain ⟨q,p,R,hq,hp,_,hqe,hpe,_⟩ := exists_typed_normal_form D.limit (D.limit_homogeneous hF)
    D.flag.radial D.flag.tangentIndices D.flag.tangentIndices D.flag.radial_mem
    (Finset.Subset.refl _) D.twelve_limit_weights
  exact ⟨q,p,hq,hp,hqe,hpe⟩

/-- The formal-arc calculation supplies the normal relation for the
actual equality data; it is no longer an open premise. -/
theorem EqualityData.twelve_normal_relation
    (SA : FormalSmoothArcInput) (DT : SymmetricDeterminantalTangentInput)
    (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint 12)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hsing : ∀ z ∈ Z, gradient F z = 0)
    (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (D : EqualityData 5 F x (affineTangentSpace Z x))
    (q : MvPolynomial (↑D.flag.tangentIndicesᶜ : Type) GeometricField)
    (p : (↑D.flag.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) GeometricField)
    (hqe : rename (fun i : (↑D.flag.tangentIndicesᶜ : Type) => (i : Fin 12)) q =
      normalQuadratic D.limit D.flag.radial)
    (hpe : ∀ i, rename (fun j : (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) =>
      (j : Fin 12)) (p i) = normalMapComponent D.limit D.flag.radial D.flag.tangentIndices i) :
    TangentHessianRank.quadraticRelation (quadraticHessian q)⁻¹ p = 0 := by
  have he : D.limit = NonzeroLimitTransport.zeroWeightPart
      (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix D.flag.basis) F)
      (singularRadialWeight D.flag.radial D.flag.tangentIndices D.flag.tangentIndices) := by
    unfold EqualityData.limit
    rw [← D.twelve_indices_eq]
  apply SingularNormalPairing.typed_normal_quadratic_relation SA F hF Z hZ hirred hsing
    x hx hdim D.flag D.twelve_full_kernel
    (hessian_tangent_polarization_zero DT F hF Z x hx hmax) q p
  · rwa [← he]
  · rwa [← he]

/-- The sole remaining source-specific input at an actual exceptional
component is independence of its extracted normal tuple. -/
theorem EqualityData.twelve_impossible_of_independent_tuple
    (MR : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (SA : FormalSmoothArcInput) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint 12)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hsing : ∀ z ∈ Z, gradient F z = 0)
    (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (D : EqualityData 5 F x (affineTangentSpace Z x))
    (q : MvPolynomial (↑D.flag.tangentIndicesᶜ : Type) GeometricField) (hq : q.IsHomogeneous 2)
    (p : (↑D.flag.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) GeometricField)
    (hp : ∀ i, (p i).IsHomogeneous 2)
    (hqe : rename (fun i : (↑D.flag.tangentIndicesᶜ : Type) => (i : Fin 12)) q =
      normalQuadratic D.limit D.flag.radial)
    (hpe : ∀ i, rename (fun j : (↑(D.flag.tangentIndices.erase D.flag.radial) : Type) =>
      (j : Fin 12)) (p i) = normalMapComponent D.limit D.flag.radial D.flag.tangentIndices i)
    (hlin : LinearIndependent GeometricField p) : False := by
  exact D.twelve_impossible_of_normal_data MR DT FI GR AD hF q hq p hp hqe hpe
    (twelve_normal_relation SA DT hF Z hZ hirred hsing hx hdim hmax D q p hqe hpe) hlin

end HessianTheorem11.SingularRadialNormalForm
