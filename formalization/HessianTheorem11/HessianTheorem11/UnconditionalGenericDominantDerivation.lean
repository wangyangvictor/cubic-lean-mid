import HessianTheorem11.UnconditionalGenericFieldDerivation
import HessianTheorem11.UnconditionalGenericDimension

/-! Derivations along an inclusion of coordinate domains. Dominance is used
only as injectivity of the actual coordinate-ring homomorphism. -/
noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open Module

section Restriction
variable (K B A E F : Type*) [Field K] [CommRing B] [CommRing A]
  [Field E] [Field F] [CharZero E]
  [Algebra K B] [Algebra K A] [Algebra K E] [Algebra K F]
  [Algebra B A] [Algebra B E] [Algebra B F] [Algebra A F] [Algebra E F]
  [IsScalarTower K B A] [IsScalarTower K B E] [IsScalarTower K B F]
  [IsScalarTower K A F] [IsScalarTower K E F]
  [IsScalarTower B A F] [IsScalarTower B E F] [IsFractionRing B E]

def coordinateDerivationRestriction : Derivation K A F →ₗ[F] Derivation K B F where
  toFun d := d.compAlgebraMap B
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include E in
/-- A derivation on the smaller coordinate domain extends first to its
function field, then across the characteristic-zero field extension, and
finally restricts to the larger coordinate domain. -/
theorem coordinate_derivation_restriction_surjective :
    Function.Surjective (coordinateDerivationRestriction K B A F) := by
  intro d
  obtain ⟨e,he⟩ := (valued_fraction_derivation_restriction_bijective K B E F).2 d
  obtain ⟨f,hf⟩ := field_derivation_restriction_surjective K E F e
  refine ⟨f.compAlgebraMap A, ?_⟩
  apply Derivation.ext
  intro b
  have h₁ := Derivation.congr_fun he b
  have h₂ := Derivation.congr_fun hf (algebraMap B E b)
  change e (algebraMap B E b) = d b at h₁
  change f (algebraMap E F (algebraMap B E b)) = e (algebraMap B E b) at h₂
  change f (algebraMap A F (algebraMap B A b)) = d b
  rw [←IsScalarTower.algebraMap_apply B A F,
    IsScalarTower.algebraMap_apply B E F]
  exact h₂.trans h₁

end Restriction

/-- Extending the values of coordinate derivations does not change their
dimension: it is the actual Krull dimension of the smaller coordinate ring. -/
theorem coordinate_derivation_dimension (B F : Type*) [CommRing B] [IsDomain B]
    [Field F] [Algebra GeometricField B] [Algebra.FiniteType GeometricField B]
    [Algebra GeometricField F] [Algebra B F]
    [IsScalarTower GeometricField B F]
    [Algebra (FractionRing B) F]
    [IsScalarTower B (FractionRing B) F]
    [IsScalarTower GeometricField (FractionRing B) F] :
    ringKrullDim B = (finrank F (Derivation GeometricField B F) : Dimension) := by
  letI : FiniteDimensional (FractionRing B)
      (KaehlerDifferential GeometricField (FractionRing B)) := functionField_differentials_finite B
  rw [krull_dimension_eq_differential_finrank B,
    ← (valuedFractionDerivationEquiv GeometricField B (FractionRing B) F).finrank_eq,
    valued_field_derivation_finrank]

end HessianTheorem11.UnconditionalGeneric
