import TranslatedDepthSeven.BoundedPrimitiveCoordinateFamilyInternal
import TranslatedDepthSeven.FractionFieldCoordinateGenerationInternal
import TranslatedDepthSeven.HomogeneousNormalizationRankDegreeEqualityInternal
import TranslatedDepthSeven.PrimitiveMinpolyRankEqualityInternal

/-!
# A bounded integral primitive coordinate for an actual normalization

The original affine-cone coordinates generate its function field. A
degree-uniform natural linear combination of them is primitive over the
normalization field. Its minimal polynomial over the normalization ring
has degree exactly the projective degree of the original cone.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 500000

theorem exists_bounded_primitive_linearNormalization_coordinate
    {K : Type*} [Field K] [CharZero K] {N r d dmax : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) [I.IsPrime]
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K))
    (D : HomogeneousLinearNormalizationData I)
    (hprojective : HasProjectiveDimensionDegree I r d) (hdmax : d ≤ dmax) :
    let B := MvPolynomial (Fin D.parameterCount) K
    let A := MvPolynomial (Fin (N + 1)) K ⧸ I
    letI : Algebra B A := D.hom.toRingHom.toAlgebra
    letI : FaithfulSMul B A :=
      (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
    ∃ c : Fin (N + 1) → ℕ, (∀ i, c i ≤ (dmax * dmax + 1) ^ (N + 1)) ∧
      let w := ∑ i, MvPolynomial.C (c i : K) * MvPolynomial.X i
      (minpoly B (Ideal.Quotient.mk I w)).natDegree = d ∧
      (letI : Algebra (FractionRing B) (FractionRing A) :=
        FractionRing.liftAlgebra B (FractionRing A)
       IntermediateField.adjoin (FractionRing B)
        ({algebraMap A (FractionRing A) (Ideal.Quotient.mk I w)} :
          Set (FractionRing A)) = ⊤) := by
  classical
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  letI : IsScalarTower K B A :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (D.hom.commutes k).symm
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  letI : Module.Finite B A := D.hom_finite
  let F := FractionRing B
  let L := FractionRing A
  letI : Algebra F L := FractionRing.liftAlgebra B L
  letI : IsScalarTower B F L := FractionRing.isScalarTower_liftAlgebra B L
  letI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun k ↦ by
    rw [IsScalarTower.algebraMap_apply K B F,
      ← IsScalarTower.algebraMap_apply B F L,
      ← IsScalarTower.algebraMap_apply K B L]
  have hrank : Module.finrank F L = d := by
    rw [← localizedModule_finrank_eq_fractionRing_finrank (B := B) (A := A)]
    exact (homogeneousLinearNormalization_genericRank_eq_projectiveDegree
      I inferInstance hhom D hprojective).2
  letI : FiniteDimensional F L := FiniteDimensional.of_finrank_pos
    (by rw [hrank]; exact hprojective.2.1)
  let x : Fin (N + 1) → L := fun i ↦
    algebraMap A L (Ideal.Quotient.mk I (MvPolynomial.X i))
  obtain ⟨c, hc, hprimitive⟩ := exists_bounded_nat_linearCombination_primitive_element
    F dmax (hrank.le.trans hdmax) (N + 1) x
  have hgenerate : IntermediateField.adjoin F (Set.range x) = ⊤ :=
    adjoin_fractionField_affineQuotient_coordinates_eq_top I
  rw [hgenerate] at hprimitive
  let w : MvPolynomial (Fin (N + 1)) K :=
    ∑ i, MvPolynomial.C (c i : K) * MvPolynomial.X i
  have hw : algebraMap A L (Ideal.Quotient.mk I w) =
      ∑ i, (c i : F) • x i := by
    simp only [w, map_sum, map_mul, x, Algebra.smul_def]
    congr 1
    funext i
    congr 1
    simp only [map_natCast]
  have hprimitive' : IntermediateField.adjoin F
      ({algebraMap A L (Ideal.Quotient.mk I w)} : Set L) = ⊤ := by
    rw [hw]
    exact hprimitive
  refine ⟨c, hc, ?_, hprimitive'⟩
  exact (minpoly_natDegree_eq_localized_rank_of_primitive
    (B := B) (Ideal.Quotient.mk I w) hprimitive').trans
      (homogeneousLinearNormalization_genericRank_eq_projectiveDegree
        I inferInstance hhom D hprojective).2

end
end TranslatedDepthSeven
