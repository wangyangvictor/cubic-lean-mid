import CubicTenVariables.PolynomialNormalizationSpecialization
import TranslatedDepthSeven.RelativeGenericComponentFiniteNormalization

/-! Retain the injective normalization map of a generic component when its
finite model descends to a principal base open. The existing construction
already supplies the exact generic parameter images; keeping those witnesses
allows injectivity to descend. The final prime-field consequence controls the
parameter count by the dimension of the actual specialized model. Equality
with the component closure on every special fiber is not asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace CubicTenVariables.RelativeInjectiveNormalization
open TranslatedDepthSeven Polynomial
universe u

/-- A generic minimal component has an explicit finite, injective normalization
over one principal localization. All model data precede the prime-field
specialization and its dimension threshold. -/
theorem exists_principalOpen_model
    {B K : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    {N : ℕ}
    (originalIdeal : Ideal (MvPolynomial (Fin N) B))
    (Q : Ideal (MvPolynomial (Fin N) K))
    (hQ : Q ∈
      (originalIdeal.map
        (MvPolynomial.map (algebraMap B K))).minimalPrimes) :
    ∃ componentCount : ℕ,
      ∃ componentGenerator : Fin componentCount → MvPolynomial (Fin N) B,
        Ideal.span (Set.range componentGenerator) ∈
            originalIdeal.minimalPrimes ∧
        (Ideal.span (Set.range componentGenerator)).map
            (MvPolynomial.map (algebraMap B K)) = Q ∧
        ∃ d ≤ N, ∃ Δ : B, ∃ hΔ : Δ ≠ 0,
          ∃ equations : Fin componentCount →
              MvPolynomial (Fin N) (Localization.Away Δ),
          ∃ parameters : Fin d →
              MvPolynomial (Fin N) (Localization.Away Δ),
          ∃ relations : Fin N →
              (MvPolynomial (Fin d) (Localization.Away Δ))[X],
            (∀ i, equations i = MvPolynomial.map
              (algebraMap B (Localization.Away Δ))
              (componentGenerator i)) ∧
            (∀ i, (relations i).Monic) ∧
            Ideal.map
                (MvPolynomial.map
                  (awayToFractionRing (R := B) (K := K) Δ hΔ))
                (finiteNormalizationModelIdeal equations parameters relations) =
              Q ∧
            Ideal.map (MvPolynomial.map
                (algebraMap B (Localization.Away Δ)))
                (Ideal.span (Set.range componentGenerator)) ≤
              finiteNormalizationModelIdeal equations parameters relations ∧
            Function.Injective (finiteNormalizationModelAlgHom
              equations parameters relations) ∧
            (finiteNormalizationModelAlgHom
              equations parameters relations).Finite ∧
            ∀ (p : ℕ) [Fact p.Prime] (ρ : Localization.Away Δ →+* ZMod p) (j : ℕ),
              ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸
                (finiteNormalizationModelIdeal equations parameters relations).map
                  (MvPolynomial.map ρ)) ≤ (j : WithBot ℕ∞) → d ≤ j := by
  classical
  obtain ⟨componentCount, componentGenerator,
      hcomponentMinimal, hcomponentGeneric⟩ :=
    genericFibre_minimalComponent_has_finite_base_model
      originalIdeal Q hQ
  have hQprime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
  letI : Q.IsPrime := hQprime
  obtain ⟨d, hdN, normalization, hnormalizationInjective,
      hnormalizationFinite⟩ :=
    exists_finite_injective_normalization_of_primeAffine Q
  have hparameterRepresentative : ∀ j : Fin d,
      ∃ qj : MvPolynomial (Fin N) K,
        Ideal.Quotient.mk Q qj = normalization (MvPolynomial.X j) := by
    intro j
    exact Ideal.Quotient.mk_surjective
      (normalization (MvPolynomial.X j))
  choose parameter hparameter using hparameterRepresentative
  have hnormalizationMap :
      (Ideal.Quotient.mkₐ K Q).comp
        (MvPolynomial.aeval parameter) = normalization := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa using hparameter j
  let A := MvPolynomial (Fin N) K ⧸ Q
  let R := MvPolynomial (Fin d) K
  letI : Algebra R A := normalization.toRingHom.toAlgebra
  letI : Module.Finite R A := hnormalizationFinite
  have hcoordinateIntegral : ∀ i : Fin N,
      IsIntegral R (Ideal.Quotient.mk Q (MvPolynomial.X i)) := by
    intro i
    exact hnormalizationFinite.to_isIntegral
      (Ideal.Quotient.mk Q (MvPolynomial.X i))
  change ∀ i : Fin N,
      ∃ p : R[X], p.Monic ∧
        p.eval₂ normalization.toRingHom
          (Ideal.Quotient.mk Q (MvPolynomial.X i)) = 0 at hcoordinateIntegral
  choose relation hrelationMonic hrelationZero using hcoordinateIntegral
  have hrelationInQ : ∀ i,
      normalizationCoordinateRelation parameter relation i ∈ Q := by
    intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hhomEval :=
      Polynomial.hom_eval₂ (relation i)
        (MvPolynomial.aeval parameter).toRingHom
        (Ideal.Quotient.mkₐ K Q).toRingHom (MvPolynomial.X i)
    have hmap :
        Ideal.Quotient.mk Q
            (normalizationCoordinateRelation parameter relation i) =
          (relation i).eval₂ normalization.toRingHom
            (Ideal.Quotient.mk Q (MvPolynomial.X i)) := by
      rw [normalizationCoordinateRelation]
      rw [← hnormalizationMap]
      exact hhomEval
    rw [hmap]
    exact hrelationZero i
  let genericEquations : Fin componentCount → MvPolynomial (Fin N) K :=
    fun i ↦ MvPolynomial.map (algebraMap B K) (componentGenerator i)
  have hgenericEquationsSpan :
      Ideal.span (Set.range genericEquations) = Q := by
    rw [← hcomponentGeneric, Ideal.map_span]
    congr 1
    simpa only [genericEquations] using
      (Set.range_comp
        (f := componentGenerator)
        (g := MvPolynomial.map (algebraMap B K)))
  obtain ⟨Δ, hΔ, equations, parameters, relations,
      hequationsGeneric, hparametersGeneric, hrelationsMonic,
      _hrelationsGeneric, hmodelGeneric, hfinite⟩ :=
    exists_vertical_finite_normalization_model (R := B) (K := K)
      genericEquations parameter relation hrelationMonic Q
      hgenericEquationsSpan hrelationInQ
  have hinjective : Function.Injective
      (finiteNormalizationModelAlgHom equations parameters relations) := by
    apply PolynomialNormalizationSpecialization.normalizationHom_injective_of_map_injective
      (finiteNormalizationModelIdeal equations parameters relations) parameters
      (awayToFractionRing (R := B) (K := K) Δ hΔ)
      (awayToFractionRing_injective Δ hΔ)
    have hp : (fun j => MvPolynomial.map
        (awayToFractionRing (R := B) (K := K) Δ hΔ) (parameters j)) = parameter :=
      funext hparametersGeneric
    rw [hmodelGeneric, hp]
    change Function.Injective ((Ideal.Quotient.mkₐ K Q).comp (MvPolynomial.aeval parameter))
    rw [hnormalizationMap]
    exact hnormalizationInjective
  have hequationsLocalized : ∀ i,
      equations i = MvPolynomial.map
        (algebraMap B (Localization.Away Δ))
        (componentGenerator i) := by
    intro i
    apply MvPolynomial.map_injective
      (awayToFractionRing (R := B) (K := K) Δ hΔ)
      (awayToFractionRing_injective Δ hΔ)
    rw [hequationsGeneric i]
    change MvPolynomial.map (algebraMap B K) (componentGenerator i) = _
    have hring :
        (awayToFractionRing (R := B) (K := K) Δ hΔ).comp
            (algebraMap B (Localization.Away Δ)) =
          algebraMap B K :=
      RingHom.ext fun b ↦ awayToFractionRing_algebraMap Δ hΔ b
    rw [MvPolynomial.map_map, hring]
  have hcomponent_le_model :
      Ideal.map (MvPolynomial.map
          (algebraMap B (Localization.Away Δ)))
          (Ideal.span (Set.range componentGenerator)) ≤
        finiteNormalizationModelIdeal equations parameters relations := by
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨f, ⟨i, rfl⟩, rfl⟩
    rw [← hequationsLocalized i]
    apply Ideal.subset_span
    exact Or.inl ⟨i, rfl⟩
  refine ⟨componentCount, componentGenerator, hcomponentMinimal,
    hcomponentGeneric, d, hdN, Δ, hΔ, equations, parameters, relations,
    hequationsLocalized, hrelationsMonic, hmodelGeneric,
    hcomponent_le_model, hinjective, hfinite, ?_⟩
  intro p _ ρ j hdim
  exact PolynomialNormalizationSpecialization.normalization_parameter_le_zmod
    (finiteNormalizationModelIdeal equations parameters relations) parameters
    hinjective hfinite.to_isIntegral ρ hdim


end CubicTenVariables.RelativeInjectiveNormalization
