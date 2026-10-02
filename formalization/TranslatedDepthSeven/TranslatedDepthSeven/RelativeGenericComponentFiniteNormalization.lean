import TranslatedDepthSeven.PrimeStratumGenericIdealSpreading
import TranslatedDepthSeven.VerticalFiniteNormalizationPackage
import TranslatedDepthSeven.PrimeAffineNoetherNormalization

/-!
# A finite-normalization model of a generic component on one base open

Let `B` be an integral Noetherian parameter ring, let `K` be its fraction
field, and let `Q` be a minimal component of the generic fibre of an affine
equation ideal.  This file proves the part of relative spreading which is
already forced by ordinary commutative algebra.

The contraction of `Q` has finitely many equations over `B`.  Noether
normalization of `Q` over `K`, together with monic equations for the ambient
coordinates, descends to one principal localization `B[1/Δ]`.  The
resulting displayed model has generic ideal exactly `Q` and is finite over a
polynomial algebra in at most the ambient number of variables.  Because the
finiteness is certified by literal monic relations, it survives every
further coefficient specialization.

This is intentionally not a reducedness or equidimensionality theorem for
the special fibres.  The model ideal contains the localized contraction of
`Q`, but equality can fail on exceptional fibres; deleting those fibres is a
separate spreading step.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

universe u v

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 4000000

/-- If a finitely generated model ideal and a component-closure ideal agree
over the fraction field, then one nonzero element of the parameter domain
removes every discrepancy between them.  The conclusion is stated for every
coefficient ring, not only for residue fields: whenever the chosen base
element becomes a unit, the two specialized ideals are literally equal.

This is the exact torsion-clearing step which turns a convenient generic
finite-normalization model into the canonical schematic closure on a dense
base principal open. -/
theorem exists_nonzero_base_open_model_eq_componentClosure
    {B K : Type u} {sigma : Type v}
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Fintype sigma]
    (componentClosure model : Ideal (MvPolynomial sigma B))
    (hcomponent_model : componentClosure ≤ model)
    (Q : Ideal (MvPolynomial sigma K))
    (hcomponentGeneric :
      componentClosure.map (MvPolynomial.map (algebraMap B K)) = Q)
    (hmodelGeneric :
      model.map (MvPolynomial.map (algebraMap B K)) = Q) :
    ∃ δ : B, δ ≠ 0 ∧
      (∀ x ∈ model,
        MvPolynomial.C (σ := sigma) δ * x ∈ componentClosure) ∧
      ∀ (L : Type*) [CommRing L] (ρ : B →+* L),
        IsUnit (ρ δ) →
          Ideal.map (MvPolynomial.map ρ) componentClosure =
            Ideal.map (MvPolynomial.map ρ) model := by
  have hgeneric : ∀ x ∈ model,
      MvPolynomial.map (algebraMap B K) (1 : MvPolynomial sigma B) *
          MvPolynomial.map (algebraMap B K) x ∈
        componentClosure.map (MvPolynomial.map (algebraMap B K)) := by
    intro x hx
    have hxmap : MvPolynomial.map (algebraMap B K) x ∈
        model.map (MvPolynomial.map (algebraMap B K)) :=
      Ideal.mem_map_of_mem _ hx
    rw [hmodelGeneric, ← hcomponentGeneric] at hxmap
    simpa only [map_one, one_mul] using hxmap
  obtain ⟨δ, hδ, hclear, _haway⟩ :=
    exists_nonzero_base_clearing_for_generic_chart
      componentClosure model (1 : MvPolynomial sigma B)
      hcomponent_model hgeneric
  refine ⟨δ, hδ, ?_, ?_⟩
  · simpa only [mul_one] using hclear
  · intro L _ ρ hρδ
    letI : Algebra (MvPolynomial sigma B) (MvPolynomial sigma L) :=
      (MvPolynomial.map ρ).toAlgebra
    have hconstant : IsUnit
        (algebraMap (MvPolynomial sigma B) (MvPolynomial sigma L)
          (MvPolynomial.C δ)) := by
      change IsUnit (MvPolynomial.map ρ (MvPolynomial.C δ))
      simpa only [MvPolynomial.map_C] using
        hρδ.map (MvPolynomial.C : L →+* MvPolynomial sigma L)
    have hone : IsUnit
        (algebraMap (MvPolynomial sigma B) (MvPolynomial sigma L)
          (1 : MvPolynomial sigma B)) := by
      simp
    simpa only [RingHom.coe_coe] using
      (map_eq_of_base_clearing_and_chart_units
        componentClosure model δ (1 : MvPolynomial sigma B)
        hcomponent_model hclear hconstant hone)

/-- A generic minimal component admits, over one dense principal open of an
integral Noetherian parameter base, a literal finite-normalization model.

The first two conclusions identify the canonical contraction of the generic
component.  The model equations over `B[1/Δ]` use exactly the localized
generators of that contraction.  The extra monic normalization relations
may only remove points in exceptional special fibres; generically they are
redundant, as expressed by the exact equality with `Q` after extension to
`K`.  The last conclusion says that the displayed finite morphism remains
finite after an arbitrary change of coefficients. -/
theorem genericMinimalComponent_has_principalOpen_finiteNormalizationModel
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
            (finiteNormalizationModelAlgHom
              equations parameters relations).Finite ∧
            ∀ (L : Type v), ∀ [CommRing L],
              ∀ ρ : Localization.Away Δ →+* L,
                (finiteNormalizationModelAlgHom
                  (fun i ↦ MvPolynomial.map ρ (equations i))
                  (fun j ↦ MvPolynomial.map ρ (parameters j))
                  (fun i ↦ (relations i).map (MvPolynomial.map ρ))).Finite := by
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
      hequationsGeneric, _hparametersGeneric, hrelationsMonic,
      _hrelationsGeneric, hmodelGeneric, hfinite⟩ :=
    exists_vertical_finite_normalization_model (R := B) (K := K)
      genericEquations parameter relation hrelationMonic Q
      hgenericEquationsSpan hrelationInQ
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
    hcomponent_le_model, hfinite, ?_⟩
  intro L _ ρ
  apply finite_finiteNormalizationModelAlgHom
  intro i
  exact (hrelationsMonic i).map (MvPolynomial.map ρ)

end

end TranslatedDepthSeven
