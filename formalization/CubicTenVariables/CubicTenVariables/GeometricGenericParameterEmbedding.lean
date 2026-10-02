import CubicTenVariables.Literature.GenericFiberGeometricIntegrality

/-! The literal generic parameter substitution is an injective coefficient
map from the integral parameter ring. This is an algebraic identity, with
no geometric-integrality or spreading premise. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GeometricGenericParameterEmbedding
open MvPolynomial HessianTheorem11 Literature

/-- The actual coefficient specialization used by the generic binary fiber. -/
def coefficientHom (σ : Type) :
    MvPolynomial σ ℤ →+* AlgebraicClosure (GeometricParameterField σ) :=
  eval₂Hom (Int.castRingHom _) (geometricGenericParameter σ)

/-- Generic substitution is coefficient extension followed by two canonical
field embeddings. In particular, it does not impose parameter equations. -/
theorem coefficientHom_eq (σ : Type) :
    coefficientHom σ =
      (algebraMap (GeometricParameterField σ)
        (AlgebraicClosure (GeometricParameterField σ))).comp
      ((algebraMap (MvPolynomial σ GeometricField) (GeometricParameterField σ)).comp
        (MvPolynomial.map (Int.castRingHom GeometricField))) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [coefficientHom]
  · intro i
    simp [coefficientHom, geometricGenericParameter]

/-- The integral parameter polynomial ring embeds in the field used by the
geometric generic fiber. No finiteness assumption on its variables is needed. -/
theorem coefficientHom_injective (σ : Type) :
    Function.Injective (coefficientHom σ) := by
  rw [coefficientHom_eq]
  exact (algebraMap (GeometricParameterField σ)
    (AlgebraicClosure (GeometricParameterField σ))).injective.comp
    ((IsFractionRing.injective (MvPolynomial σ GeometricField)
      (GeometricParameterField σ)).comp
      (MvPolynomial.map_injective _ Int.cast_injective))

end CubicTenVariables.GeometricGenericParameterEmbedding
