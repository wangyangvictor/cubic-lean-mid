import TranslatedDepthSeven.PrimitiveAugmentedBirationality

/-!
# Primitive generation and the canonical fraction-field algebra

These elementary field lemmas keep the algebra structures in the final
projection predicate literal: the fraction-field algebra is the canonical
localization lift, rather than a separately chosen isomorphic structure.
-/

namespace TranslatedDepthSeven
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000

theorem adjoin_groundField_range_union_eq_top_of_fractionField_primitive
    {K B F L : Type*} [Field K] [CommRing B] [Field F] [Field L]
    [Algebra K B] [Algebra K L] [Algebra B F] [Algebra B L]
    [IsFractionRing B F] [IsScalarTower K B L]
    [Algebra F L] [IsScalarTower B F L]
    (x : L) (hprimitive : IntermediateField.adjoin F ({x} : Set L) = ⊤) :
    IntermediateField.adjoin K
      (((IsScalarTower.toAlgHom K B L).range : Set L) ∪ {x}) = ⊤ := by
  let E := IntermediateField.adjoin K
    (((IsScalarTower.toAlgHom K B L).range : Set L) ∪ {x})
  have hB (b : B) : algebraMap B L b ∈ E :=
    IntermediateField.subset_adjoin K _ (Or.inl ⟨b, rfl⟩)
  have hF (a : F) : algebraMap F L a ∈ E := by
    obtain ⟨b, c, _, rfl⟩ := IsFractionRing.div_surjective (A := B) a
    rw [map_div₀, ← IsScalarTower.algebraMap_apply B F L,
      ← IsScalarTower.algebraMap_apply B F L]
    exact E.div_mem (hB b) (hB c)
  have hle : (IntermediateField.adjoin F ({x} : Set L)).toSubfield ≤ E.toSubfield :=
    IntermediateField.adjoin_le_subfield F ({x} : Set L)
      (by rintro _ ⟨a, rfl⟩; exact hF a)
      (by rintro _ ⟨rfl⟩; exact IntermediateField.subset_adjoin K _ (Or.inr rfl))
  apply top_unique
  intro y _
  apply hle
  rw [hprimitive]
  trivial

theorem fractionRing_finrank_eq_one_of_adjoin_range_eq_top_canonical
    {K B A : Type*} [Field K] [CommRing B] [IsDomain B]
    [CommRing A] [IsDomain A] [Algebra K B] [Algebra K A]
    (g : B →ₐ[K] A) (hg : Function.Injective g)
    (hgenerate : IntermediateField.adjoin K
      (((IsScalarTower.toAlgHom K A (FractionRing A)).comp g).range :
        Set (FractionRing A)) = ⊤) :
    letI : Algebra B A := g.toRingHom.toAlgebra
    letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg
    letI : Algebra (FractionRing B) (FractionRing A) :=
      FractionRing.liftAlgebra B (FractionRing A)
    Module.finrank (FractionRing B) (FractionRing A) = 1 := by
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsScalarTower K B A :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (g.commutes k).symm
  letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg
  let F := FractionRing B
  let L := FractionRing A
  letI : Algebra F L := FractionRing.liftAlgebra B L
  letI : IsScalarTower B F L := FractionRing.isScalarTower_liftAlgebra B L
  letI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun k ↦ by
    rw [IsScalarTower.algebraMap_apply K B F,
      ← IsScalarTower.algebraMap_apply B F L,
      ← IsScalarTower.algebraMap_apply K B L]
  let f : F →ₐ[K] L := IsScalarTower.toAlgHom K F L
  let gL : B →ₐ[K] L := (IsScalarTower.toAlgHom K A L).comp g
  have hcomp : f.toRingHom.comp (algebraMap B F) = gL.toRingHom := by
    ext b
    exact (IsScalarTower.algebraMap_apply B F L b).symm.trans
      (IsScalarTower.algebraMap_apply B A L b)
  have hfield : f.fieldRange = ⊤ :=
    (IsFractionRing.algHom_fieldRange_eq_of_comp_eq (g := gL) (f := f) hcomp).trans hgenerate
  have hsurj : Function.Surjective f := (AlgHom.fieldRange_eq_top).mp hfield
  apply (finrank_eq_one_iff_of_nonzero' (1 : L) one_ne_zero).2
  intro z
  obtain ⟨a, rfl⟩ := hsurj z
  refine ⟨a, ?_⟩
  rw [Algebra.smul_def, mul_one]
  rfl

end
end TranslatedDepthSeven
