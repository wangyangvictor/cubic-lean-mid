import TranslatedDepthSeven.CanonicalPrimitiveBirationalityInternal
import TranslatedDepthSeven.GeometricNormalizationFibreDegreeInternal

/-!
# Reordering the target coordinates of a primitive projection

Precomposition by an automorphism of the target polynomial algebra
preserves finite generation, generation of the function field, and every
geometric fibre bound. This allows the first coordinate to remain X0.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem precomposed_augmentedLinearNormalizationHom_comp_inclusion
    {K τ : Type*} [Field K] {I : Ideal (MvPolynomial τ K)}
    (D : HomogeneousLinearNormalizationData I) (u : MvPolynomial τ K ⧸ I)
    (e : MvPolynomial (Fin (D.parameterCount + 1)) K ≃ₐ[K]
      MvPolynomial (Fin (D.parameterCount + 1)) K) :
    ((augmentedLinearNormalizationHom D u).comp e.toAlgHom).comp
      (e.symm.toAlgHom.comp (mvPolynomialSuccInclusion K D.parameterCount)) = D.hom := by
  apply AlgHom.ext
  intro f
  change augmentedLinearNormalizationHom D u
    (e (e.symm (mvPolynomialSuccInclusion K D.parameterCount f))) = D.hom f
  rw [e.apply_symm_apply]
  exact AlgHom.congr_fun (augmentedLinearNormalizationHom_comp_succInclusion D u) f

theorem precomposed_augmentedLinearNormalizationHom_finite
    {K τ : Type*} [Field K] {I : Ideal (MvPolynomial τ K)}
    (D : HomogeneousLinearNormalizationData I) (u : MvPolynomial τ K ⧸ I)
    (e : MvPolynomial (Fin (D.parameterCount + 1)) K ≃ₐ[K]
      MvPolynomial (Fin (D.parameterCount + 1)) K) :
    ((augmentedLinearNormalizationHom D u).comp e.toAlgHom).Finite := by
  apply AlgHom.Finite.of_comp_finite (f := e.symm.toAlgHom.comp
    (mvPolynomialSuccInclusion K D.parameterCount))
  rw [precomposed_augmentedLinearNormalizationHom_comp_inclusion]
  exact D.hom_finite

theorem precomposed_augmentedLinearNormalization_image_adjoin_eq_top
    {K τ : Type*} [Field K]
    {I : Ideal (MvPolynomial τ K)} (hI : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I) (u : MvPolynomial τ K ⧸ I)
    (e : MvPolynomial (Fin (D.parameterCount + 1)) K ≃ₐ[K]
      MvPolynomial (Fin (D.parameterCount + 1)) K)
    (hprimitive :
      let A := MvPolynomial τ K ⧸ I
      let L := FractionRing A
      IntermediateField.adjoin K
        ((((IsScalarTower.toAlgHom K A L).comp D.hom).range : Set L) ∪
          {algebraMap A L u}) = ⊤) :
    let A := MvPolynomial τ K ⧸ I
    let L := FractionRing A
    let h := (augmentedLinearNormalizationHom D u).comp e.toAlgHom
    IntermediateField.adjoin K
      (((IsScalarTower.toAlgHom K A L).comp (Ideal.kerLiftAlg h)).range : Set L) = ⊤ := by
  letI : I.IsPrime := hI
  let A := MvPolynomial τ K ⧸ I
  let L := FractionRing A
  let h := (augmentedLinearNormalizationHom D u).comp e.toAlgHom
  let J := RingHom.ker h
  let imageToL := (IsScalarTower.toAlgHom K A L).comp (Ideal.kerLiftAlg h)
  have hsubset :
      ((((IsScalarTower.toAlgHom K A L).comp D.hom).range : Set L) ∪
        {algebraMap A L u}) ⊆ (imageToL.range : Set L) := by
    intro z hz
    rcases hz with ⟨b, rfl⟩ | hz
    · refine ⟨Ideal.Quotient.mk J
        (e.symm (mvPolynomialSuccInclusion K D.parameterCount b)), ?_⟩
      change algebraMap A L (augmentedLinearNormalizationHom D u
        (e (e.symm (mvPolynomialSuccInclusion K D.parameterCount b)))) =
        algebraMap A L (D.hom b)
      rw [e.apply_symm_apply]
      exact congrArg (algebraMap A L)
        (AlgHom.congr_fun (augmentedLinearNormalizationHom_comp_succInclusion D u) b)
    · have hz' : z = algebraMap A L u := by simpa using hz
      subst z
      refine ⟨Ideal.Quotient.mk J (e.symm (X 0)), ?_⟩
      change algebraMap A L (augmentedLinearNormalizationHom D u (e (e.symm (X 0)))) = _
      rw [e.apply_symm_apply, augmentedLinearNormalizationHom_X_zero]
  apply top_unique
  rw [← hprimitive]
  exact IntermediateField.adjoin.mono K _ _ hsubset

end
end TranslatedDepthSeven
