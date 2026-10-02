import CubicTenVariables.GenericNormalDerivations
import CubicTenVariables.CubicGeometricSingularDimension
import CubicTenVariables.CubicGenericSectionPointCount
import CubicTenVariables.GenericNormalAvoidance

/-! The concrete generic section of a fixed anisotropic integer cubic.
Rational anisotropy bounds the geometric gradient cone by dimension five.
Five generic normals avoid its nonzero points, and parameter differentiation
then proves rank six for the actual augmented Jacobian. This produces a
nonzero integer certificate and the fixed-equation finite-field estimate.
Coefficient embeddings and normal matrices are kept literal throughout.
The numerical estimate takes the smooth-cubic Weil bound as its sole
literature input. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.CubicGenericSmoothness
open MvPolynomial HessianTheorem11 Literature
open ProjectiveLinearSectionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev SectionField := GenericNormalDerivations.GenericField GeometricField 5 10

/-- The canonical geometric-base algebra map into the generic coefficient field. -/
def geometricParameterAlgHom :
    MvPolynomial (Fin 50) GeometricField →ₐ[GeometricField] SectionField :=
  IsScalarTower.toAlgHom GeometricField (MvPolynomial (Fin 50) GeometricField) SectionField

theorem geometricParameterAlgHom_injective : Function.Injective geometricParameterAlgHom := by
  let B := MvPolynomial (Fin 50) GeometricField
  let L := FractionRing B
  change Function.Injective (algebraMap B SectionField)
  rw [IsScalarTower.algebraMap_eq B L SectionField]
  exact (algebraMap L SectionField).injective.comp (IsFractionRing.injective B L)

/-- The fifty integral parameters embedded into the actual generic field. -/
def integerParameterMap : MvPolynomial (Fin 50) ℤ →+* SectionField :=
  geometricParameterAlgHom.toRingHom.comp (MvPolynomial.map (Int.castRingHom GeometricField))

theorem integerParameterMap_injective : Function.Injective integerParameterMap :=
  geometricParameterAlgHom_injective.comp
    (MvPolynomial.map_injective (Int.castRingHom GeometricField) Int.cast_injective)

theorem integerParameterMap_comp_C :
    integerParameterMap.comp C = Int.castRingHom SectionField := Subsingleton.elim _ _

theorem integer_genericNormal_eq :
    CubicGenericSmoothSectionCertificate.genericNormal.map integerParameterMap =
      GenericNormalDerivations.genericNormal GeometricField 5 10 := by
  ext r c
  simp only [CubicGenericSmoothSectionCertificate.genericNormal, Matrix.map,
    integerParameterMap, RingHom.comp_apply, MvPolynomial.map_X]
  rfl

theorem geometric_genericNormal_eq :
    (fun r : Fin 5 ↦ fun c : Fin 10 ↦
      geometricParameterAlgHom (X (finProdFinEquiv (r, c)))) =
      GenericNormalDerivations.genericNormal GeometricField 5 10 := rfl

theorem integer_polynomial_extension (F : MvPolynomial (Fin 10) ℤ) :
    map (integerParameterMap.comp C) F =
      map (algebraMap GeometricField SectionField)
        (map (Int.castRingHom GeometricField) F) := by
  rw [map_map]
  exact congrArg (fun ρ : ℤ →+* SectionField ↦ map ρ F) (Subsingleton.elim _ _)

theorem aeval_eq_zero_of_gradient {k E : Type*} [Field k] [Field E] [Algebra k E]
    (F : MvPolynomial (Fin 10) k) (x : Fin 10 → E)
    (hgrad : ∀ i, aeval x (pderiv i F) = 0)
    (f : MvPolynomial (Fin 10) k) (hf : f ∈ CubicGeometricSingularDimension.gradientIdeal F) :
    aeval x f = 0 := by
  have hker : CubicGeometricSingularDimension.gradientIdeal F ≤
      RingHom.ker (aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hgrad i
  exact hker hf

theorem integer_cubic_ne_zero_of_anisotropic
    (F : MvPolynomial (Fin 10) ℤ)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) : F ≠ 0 := by
  intro hzero
  have h := hA (Pi.single 0 1) (by simp [hzero])
  have hh := congrFun h 0
  simp at hh

/-- The actual generic section of the given integer cubic has augmented
Jacobian rank six at every nonzero common zero. All geometric inputs are
supplied by the proved gradient-cone dimension and generic-avoidance lemmas. -/
theorem generic_augmented_rank
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (x : Fin 10 → SectionField) (hx : x ≠ 0)
    (hzero : eval x (map (integerParameterMap.comp C) F) = 0)
    (hrows : (CubicGenericSmoothSectionCertificate.genericNormal.map
      integerParameterMap).mulVec x = 0) :
    (augmentedSectionJacobian (map (integerParameterMap.comp C) F)
      (CubicGenericSmoothSectionCertificate.genericNormal.map integerParameterMap) x).rank = 6 := by
  let Fbar := map (Int.castRingHom GeometricField) F
  have hzero' : aeval x Fbar = 0 := by
    simpa only [integer_polynomial_extension, eval_map, aeval_def] using hzero
  have hrows' : (GenericNormalDerivations.genericNormal GeometricField 5 10).mulVec x = 0 := by
    simpa only [integer_genericNormal_eq] using hrows
  have hgrad : ∃ i, aeval x (pderiv i Fbar) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    apply GenericNormalAvoidance.genericNormal_avoids_small_homogeneousCone
      geometricParameterAlgHom geometricParameterAlgHom_injective
      (CubicGeometricSingularDimension.gradientIdeal Fbar)
      (CubicGeometricSingularDimension.gradientIdeal_isHomogeneous Fbar (hF.map _))
      (CubicGeometricSingularDimension.geometric_gradient_quotient_dimension_le_five F hF hA)
      x (aeval_eq_zero_of_gradient Fbar x h)
    simpa only [geometric_genericNormal_eq] using hrows'
  have hrank := GenericNormalDerivations.generic_augmented_rank_of_gradient_ne_zero
    (m := 5) Fbar x hx hzero' hrows' hgrad
  simpa only [integer_polynomial_extension, integer_genericNormal_eq] using hrank

/-- One nonzero integer certificate works for every field and every normal
tuple where it remains nonzero. Its degree may depend on this fixed cubic. -/
theorem exists_nonzero_goodJacobian_certificate
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ Δ : MvPolynomial (Fin 50) ℤ, Δ ≠ 0 ∧
      ∀ (K : Type) [Field K] (γ : Fin 5 → Fin 10 → K),
        eval (ProjectiveLinearSectionVariance.normalTupleCoordinates γ)
          (map (Int.castRingHom K) Δ) ≠ 0 →
        CubicJacobianSectionReduction.GoodJacobianTuple (map (Int.castRingHom K) F) γ :=
  CubicGenericSmoothSectionCertificate.exists_nonzero_goodJacobian_certificate
    F integerParameterMap integerParameterMap_injective (generic_augmented_rank F hF hA)

/-- The fixed-cubic ambient estimate over all finite extensions of all
good prime fields, using only the numerical smooth-cubic Weil input. -/
theorem exists_uniform_bound
    (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ A →
      ∀ (E : Type) [Field E] [Fintype E] [CharP E p],
        |(affineZeroCount (map (Int.castRingHom E) F) : ℝ) -
            (Fintype.card E : ℝ) ^ 9| ≤
          15 * ((Fintype.card E : ℝ) - 1) *
            (Fintype.card E : ℝ) ^ ((13 : ℝ) / 2) :=
  CubicGenericSectionPointCount.exists_uniform_bound weil F
    (integer_cubic_ne_zero_of_anisotropic F hA) hF integerParameterMap
    integerParameterMap_injective (generic_augmented_rank F hF hA)

/-- Literal prime-field root count, including the origin. -/
theorem exists_prime_bound
    (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ p : ℕ, (hp : p.Prime) → ¬ p ∣ A →
      letI : Fact p.Prime := ⟨hp⟩
      |(Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0} : ℝ) -
          (p : ℝ) ^ 9| ≤ 15 * ((p : ℝ) - 1) * (p : ℝ) ^ ((13 : ℝ) / 2) :=
  CubicGenericSectionPointCount.exists_prime_bound weil F
    (integer_cubic_ne_zero_of_anisotropic F hA) hF integerParameterMap
    integerParameterMap_injective (generic_augmented_rank F hF hA)

end CubicTenVariables.CubicGenericSmoothness
