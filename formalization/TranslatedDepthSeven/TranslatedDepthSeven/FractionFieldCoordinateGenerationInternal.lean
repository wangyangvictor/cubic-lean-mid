import TranslatedDepthSeven.MonicCoordinateModuleFinite
import TranslatedDepthSeven.PrimitiveAugmentedBirationality

/-!
# Coordinate generators of a fraction field

Algebra generators of a domain generate its fraction field as a field,
also after enlarging the coefficient field inside that fraction field.
This supplies the literal original coordinates in the bounded primitive
element construction for linear projections.
-/

namespace TranslatedDepthSeven
noncomputable section

set_option synthInstance.maxHeartbeats 300000

theorem adjoin_fractionField_coordinates_eq_top_of_algebra_generators
    {K A F L : Type*} [Field K] [CommRing A] [IsDomain A]
    [Field F] [Field L] [Algebra K A] [Algebra K F] [Algebra K L]
    [Algebra A L] [IsFractionRing A L] [IsScalarTower K A L]
    [Algebra F L] [IsScalarTower K F L]
    {ι : Type*} (x : ι → A)
    (hgenerate : Algebra.adjoin K (Set.range x) = ⊤) :
    IntermediateField.adjoin F (Set.range fun i ↦ algebraMap A L (x i)) = ⊤ := by
  classical
  let E := IntermediateField.adjoin F
    (Set.range fun i ↦ algebraMap A L (x i))
  let g : A →ₐ[K] L := IsScalarTower.toAlgHom K A L
  let S : Subalgebra K A := (E.toSubalgebra.restrictScalars K).comap g
  have htop : (⊤ : Subalgebra K A) ≤ S := by
    rw [← hgenerate]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
  have hA (a : A) : algebraMap A L a ∈ E := htop (by trivial)
  apply top_unique
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := A) z
  exact E.div_mem (hA a) (hA b)

theorem adjoin_fractionField_affineQuotient_coordinates_eq_top
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra F (FractionRing (MvPolynomial (Fin n) K ⧸ I))]
    [IsScalarTower K F (FractionRing (MvPolynomial (Fin n) K ⧸ I))] :
    IntermediateField.adjoin F (Set.range fun i ↦
      algebraMap (MvPolynomial (Fin n) K ⧸ I)
        (FractionRing (MvPolynomial (Fin n) K ⧸ I))
        (Ideal.Quotient.mk I (MvPolynomial.X i))) = ⊤ :=
  adjoin_fractionField_coordinates_eq_top_of_algebra_generators _
    (adjoin_affineQuotient_coordinates_eq_top K I)

end
end TranslatedDepthSeven
