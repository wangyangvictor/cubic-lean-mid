import TranslatedDepthSeven.BoundedSimultaneousPrimitiveCoordinateInternal
import TranslatedDepthSeven.FractionFieldCoordinateGenerationInternal
import TranslatedDepthSeven.HomogeneousNormalizationRankDegreeEqualityInternal
import TranslatedDepthSeven.PrimitiveMinpolyRankEqualityInternal

/-!
# One bounded primitive coordinate for two homogeneous normalizations

This packages the two-extension primitive-element theorem in the form used
by homogeneous linear projections.  Given two finite homogeneous
normalizations and two displayed families of quotient-ring elements which
generate the respective function fields, one bounded vector of natural
coefficients is primitive for both families.  The two minimal-polynomial
degrees are the respective projective degrees.
-/

namespace TranslatedDepthSeven
noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 600000

/-- A common bounded linear combination is primitive for two homogeneous
normalizations.  The displayed families may have different source rings,
but have the same finite index so that the coefficient vector is literal. -/
theorem exists_bounded_simultaneous_primitive_normalization_coordinate
    {N₁ N₂ r₁ r₂ d₁ d₂ dmax n : ℕ}
    (I₁ : Ideal (MvPolynomial (Fin (N₁ + 1)) ℚ))
    (hprime₁ : I₁.IsPrime)
    (hhom₁ : I₁.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N₁ + 1)) ℚ))
    (D₁ : HomogeneousLinearNormalizationData I₁)
    (hprojective₁ : HasProjectiveDimensionDegree I₁ r₁ d₁)
    (hdmax₁ : d₁ ≤ dmax)
    (I₂ : Ideal (MvPolynomial (Fin (N₂ + 1)) ℚ))
    (hprime₂ : I₂.IsPrime)
    (hhom₂ : I₂.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N₂ + 1)) ℚ))
    (D₂ : HomogeneousLinearNormalizationData I₂)
    (hprojective₂ : HasProjectiveDimensionDegree I₂ r₂ d₂)
    (hdmax₂ : d₂ ≤ dmax)
    (v₁ : Fin n → (MvPolynomial (Fin (N₁ + 1)) ℚ ⧸ I₁))
    (v₂ : Fin n → (MvPolynomial (Fin (N₂ + 1)) ℚ ⧸ I₂))
    (hgenerate₁ :
      let B₁ := MvPolynomial (Fin D₁.parameterCount) ℚ
      let A₁ := MvPolynomial (Fin (N₁ + 1)) ℚ ⧸ I₁
      letI : Algebra B₁ A₁ := D₁.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B₁ A₁ :=
        (faithfulSMul_iff_algebraMap_injective B₁ A₁).mpr D₁.hom_injective
      letI : Algebra (FractionRing B₁) (FractionRing A₁) :=
        FractionRing.liftAlgebra B₁ (FractionRing A₁)
      IntermediateField.adjoin (FractionRing B₁)
        (Set.range fun i ↦ algebraMap A₁ (FractionRing A₁) (v₁ i)) = ⊤)
    (hgenerate₂ :
      let B₂ := MvPolynomial (Fin D₂.parameterCount) ℚ
      let A₂ := MvPolynomial (Fin (N₂ + 1)) ℚ ⧸ I₂
      letI : Algebra B₂ A₂ := D₂.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B₂ A₂ :=
        (faithfulSMul_iff_algebraMap_injective B₂ A₂).mpr D₂.hom_injective
      letI : Algebra (FractionRing B₂) (FractionRing A₂) :=
        FractionRing.liftAlgebra B₂ (FractionRing A₂)
      IntermediateField.adjoin (FractionRing B₂)
        (Set.range fun i ↦ algebraMap A₂ (FractionRing A₂) (v₂ i)) = ⊤) :
    ∃ c : Fin n → ℕ, (∀ i, c i ≤ (2 * dmax * dmax + 1) ^ n) ∧
      let B₁ := MvPolynomial (Fin D₁.parameterCount) ℚ
      let A₁ := MvPolynomial (Fin (N₁ + 1)) ℚ ⧸ I₁
      let B₂ := MvPolynomial (Fin D₂.parameterCount) ℚ
      let A₂ := MvPolynomial (Fin (N₂ + 1)) ℚ ⧸ I₂
      letI : Algebra B₁ A₁ := D₁.hom.toRingHom.toAlgebra
      letI : Algebra B₂ A₂ := D₂.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B₁ A₁ :=
        (faithfulSMul_iff_algebraMap_injective B₁ A₁).mpr D₁.hom_injective
      letI : FaithfulSMul B₂ A₂ :=
        (faithfulSMul_iff_algebraMap_injective B₂ A₂).mpr D₂.hom_injective
      let w₁ : A₁ := ∑ i, (c i : ℚ) • v₁ i
      let w₂ : A₂ := ∑ i, (c i : ℚ) • v₂ i
      (minpoly B₁ w₁).natDegree = d₁ ∧
      (letI : Algebra (FractionRing B₁) (FractionRing A₁) :=
          FractionRing.liftAlgebra B₁ (FractionRing A₁)
       IntermediateField.adjoin (FractionRing B₁)
          ({algebraMap A₁ (FractionRing A₁) w₁} :
            Set (FractionRing A₁)) = ⊤) ∧
      (minpoly B₂ w₂).natDegree = d₂ ∧
      (letI : Algebra (FractionRing B₂) (FractionRing A₂) :=
          FractionRing.liftAlgebra B₂ (FractionRing A₂)
       IntermediateField.adjoin (FractionRing B₂)
          ({algebraMap A₂ (FractionRing A₂) w₂} :
            Set (FractionRing A₂)) = ⊤) := by
  classical
  letI : I₁.IsPrime := hprime₁
  letI : I₂.IsPrime := hprime₂
  let B₁ := MvPolynomial (Fin D₁.parameterCount) ℚ
  let A₁ := MvPolynomial (Fin (N₁ + 1)) ℚ ⧸ I₁
  let F₁ := FractionRing B₁
  let L₁ := FractionRing A₁
  letI : Algebra B₁ A₁ := D₁.hom.toRingHom.toAlgebra
  letI : IsScalarTower ℚ B₁ A₁ :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (D₁.hom.commutes k).symm
  letI : FaithfulSMul B₁ A₁ :=
    (faithfulSMul_iff_algebraMap_injective B₁ A₁).mpr D₁.hom_injective
  letI : Module.Finite B₁ A₁ := D₁.hom_finite
  letI : Algebra F₁ L₁ := FractionRing.liftAlgebra B₁ L₁
  letI : IsScalarTower B₁ F₁ L₁ :=
    FractionRing.isScalarTower_liftAlgebra B₁ L₁
  letI : IsScalarTower ℚ F₁ L₁ := inferInstance
  have hrank₁ : Module.finrank F₁ L₁ = d₁ := by
    rw [← localizedModule_finrank_eq_fractionRing_finrank
      (B := B₁) (A := A₁)]
    exact (homogeneousLinearNormalization_genericRank_eq_projectiveDegree
      I₁ hprime₁ hhom₁ D₁ hprojective₁).2
  letI : FiniteDimensional F₁ L₁ := FiniteDimensional.of_finrank_pos
    (by rw [hrank₁]; exact hprojective₁.2.1)
  let B₂ := MvPolynomial (Fin D₂.parameterCount) ℚ
  let A₂ := MvPolynomial (Fin (N₂ + 1)) ℚ ⧸ I₂
  let F₂ := FractionRing B₂
  let L₂ := FractionRing A₂
  letI : Algebra B₂ A₂ := D₂.hom.toRingHom.toAlgebra
  letI : IsScalarTower ℚ B₂ A₂ :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (D₂.hom.commutes k).symm
  letI : FaithfulSMul B₂ A₂ :=
    (faithfulSMul_iff_algebraMap_injective B₂ A₂).mpr D₂.hom_injective
  letI : Module.Finite B₂ A₂ := D₂.hom_finite
  letI : Algebra F₂ L₂ := FractionRing.liftAlgebra B₂ L₂
  letI : IsScalarTower B₂ F₂ L₂ :=
    FractionRing.isScalarTower_liftAlgebra B₂ L₂
  letI : IsScalarTower ℚ F₂ L₂ := inferInstance
  have hrank₂ : Module.finrank F₂ L₂ = d₂ := by
    rw [← localizedModule_finrank_eq_fractionRing_finrank
      (B := B₂) (A := A₂)]
    exact (homogeneousLinearNormalization_genericRank_eq_projectiveDegree
      I₂ hprime₂ hhom₂ D₂ hprojective₂).2
  letI : FiniteDimensional F₂ L₂ := FiniteDimensional.of_finrank_pos
    (by rw [hrank₂]; exact hprojective₂.2.1)
  let x₁ : Fin n → L₁ := fun i ↦ algebraMap A₁ L₁ (v₁ i)
  let x₂ : Fin n → L₂ := fun i ↦ algebraMap A₂ L₂ (v₂ i)
  obtain ⟨c, hc, hprimitive₁, hprimitive₂⟩ :=
    exists_bounded_nat_simultaneous_linearCombination_primitive_element
      F₁ F₂ dmax (hrank₁.le.trans hdmax₁) (hrank₂.le.trans hdmax₂)
      n x₁ x₂
  let w₁ : A₁ := ∑ i, (c i : ℚ) • v₁ i
  let w₂ : A₂ := ∑ i, (c i : ℚ) • v₂ i
  have hw₁ : algebraMap A₁ L₁ w₁ = ∑ i, (c i : F₁) • x₁ i := by
    simp [w₁, x₁, Algebra.smul_def]
  have hw₂ : algebraMap A₂ L₂ w₂ = ∑ i, (c i : F₂) • x₂ i := by
    simp [w₂, x₂, Algebra.smul_def]
  have hsingle₁ : IntermediateField.adjoin F₁
      ({algebraMap A₁ L₁ w₁} : Set L₁) = ⊤ := by
    rw [hw₁, hprimitive₁, show IntermediateField.adjoin F₁
      (Set.range x₁) = ⊤ from hgenerate₁]
  have hsingle₂ : IntermediateField.adjoin F₂
      ({algebraMap A₂ L₂ w₂} : Set L₂) = ⊤ := by
    rw [hw₂, hprimitive₂, show IntermediateField.adjoin F₂
      (Set.range x₂) = ⊤ from hgenerate₂]
  refine ⟨c, hc, ?_, hsingle₁, ?_, hsingle₂⟩
  · exact (minpoly_natDegree_eq_localized_rank_of_primitive
      (B := B₁) w₁ hsingle₁).trans
        (homogeneousLinearNormalization_genericRank_eq_projectiveDegree
          I₁ hprime₁ hhom₁ D₁ hprojective₁).2
  · exact (minpoly_natDegree_eq_localized_rank_of_primitive
      (B := B₂) w₂ hsingle₂).trans
        (homogeneousLinearNormalization_genericRank_eq_projectiveDegree
          I₂ hprime₂ hhom₂ D₂ hprojective₂).2

end
end TranslatedDepthSeven
