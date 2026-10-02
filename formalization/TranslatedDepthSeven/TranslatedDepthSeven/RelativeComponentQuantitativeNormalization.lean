import TranslatedDepthSeven.FiniteNormalizationModelProductBound

/-!
# Quantitative finite normalization of a component closure on one base open

Let a canonical component-closure ideal over an integral Noetherian base be
contained in a literal finite-normalization model, and suppose the two
ideals agree over the fraction field.  One nonzero base element clears their
finite discrepancy.  On the resulting principal open, every field
specialization of the component closure is therefore literally the
specialized monic model.

This gives a finite map to affine `d`-space in every such specialization.
The dimension of every scalar fibre of that map is bounded uniformly by the
product of the degrees of the original monic relations.  If the residue
field is finite, the total number of rational points is bounded by that
product times `(#L)^d`.

This is the strongest consequence supplied by the explicit monic model
alone.  It deliberately makes no assertion of injectivity after
specialization, constancy of dimension, reducedness, irreducibility,
flatness, or equidimensionality.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

universe u

/-- After shrinking the integral parameter base by one nonzero element, a
component closure which has the same generic ideal as an explicit monic
model inherits a quantitative finite normalization in every field fibre.

The first displayed membership is the literal torsion-clearing certificate.
The first universal conclusion gives module-finiteness, the valid Krull
dimension upper bound, and the fibre-rank bound.  The second universal
conclusion is its finite-field point-count consequence. -/
theorem exists_nonzero_base_open_quantitative_model_eq_componentClosure
    {S K : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [Field K] [Algebra S K] [IsFractionRing S K]
    {N d r : ℕ}
    (componentClosure : Ideal (MvPolynomial (Fin N) S))
    (f : Fin r → MvPolynomial (Fin N) S)
    (q : Fin d → MvPolynomial (Fin N) S)
    (p : Fin N → (MvPolynomial (Fin d) S)[X])
    (hmonic : ∀ i, (p i).Monic)
    (Q : Ideal (MvPolynomial (Fin N) K))
    (hcomponent_model : componentClosure ≤
      finiteNormalizationModelIdeal f q p)
    (hcomponentGeneric :
      componentClosure.map (MvPolynomial.map (algebraMap S K)) = Q)
    (hmodelGeneric :
      (finiteNormalizationModelIdeal f q p).map
        (MvPolynomial.map (algebraMap S K)) = Q) :
    ∃ delta : S, delta ≠ 0 ∧
      (∀ x ∈ finiteNormalizationModelIdeal f q p,
        MvPolynomial.C (σ := Fin N) delta * x ∈ componentClosure) ∧
      (∀ (L : Type u) [Field L] (rho : S →+* L),
        IsUnit (rho delta) →
        let I := componentClosure.map (MvPolynomial.map rho)
        ∃ g : MvPolynomial (Fin d) L →ₐ[L]
            (MvPolynomial (Fin N) L ⧸ I),
          g.Finite ∧
          ringKrullDim (MvPolynomial (Fin N) L ⧸ I) ≤
            ringKrullDim (MvPolynomial (Fin d) L) ∧
          ∀ phi : MvPolynomial (Fin d) L →ₐ[L] L,
            Module.finrank L
                (ringHomScalarFibre (MvPolynomial (Fin d) L) L
                  (MvPolynomial (Fin N) L ⧸ I)
                  phi.toRingHom g.toRingHom) ≤
              ∏ i, (p i).natDegree ∧
            Module.length L
                (ringHomScalarFibre (MvPolynomial (Fin d) L) L
                  (MvPolynomial (Fin N) L ⧸ I)
                  phi.toRingHom g.toRingHom) ≤
              (∏ i, (p i).natDegree : ℕ∞)) ∧
      (∀ (L : Type u) [Field L] [Finite L] (rho : S →+* L),
        IsUnit (rho delta) →
        Nat.card
            ((MvPolynomial (Fin N) L ⧸
              componentClosure.map (MvPolynomial.map rho)) →ₐ[L] L) ≤
          (∏ i, (p i).natDegree) * Nat.card L ^ d) := by
  obtain ⟨delta, hdelta, hclear, heq⟩ :=
    exists_nonzero_base_open_model_eq_componentClosure
      componentClosure (finiteNormalizationModelIdeal f q p)
      hcomponent_model Q hcomponentGeneric hmodelGeneric
  refine ⟨delta, hdelta, hclear, ?_, ?_⟩
  · intro L _ rho hrho
    let I := componentClosure.map (MvPolynomial.map rho)
    have hI : I = finiteNormalizationModelIdeal
        (fun i ↦ MvPolynomial.map rho (f i))
        (fun j ↦ MvPolynomial.map rho (q j))
        (fun i ↦ (p i).map (MvPolynomial.map rho)) := by
      change componentClosure.map (MvPolynomial.map rho) = _
      rw [heq L rho hrho]
      exact map_finiteNormalizationModelIdeal rho f q p
    exact specialized_ideal_eq_finiteNormalizationModel_quantitative
      L rho f q p hmonic I hI
  · intro L _ _ rho hrho
    let I := componentClosure.map (MvPolynomial.map rho)
    have hI : I = finiteNormalizationModelIdeal
        (fun i ↦ MvPolynomial.map rho (f i))
        (fun j ↦ MvPolynomial.map rho (q j))
        (fun i ↦ (p i).map (MvPolynomial.map rho)) := by
      change componentClosure.map (MvPolynomial.map rho) = _
      rw [heq L rho hrho]
      exact map_finiteNormalizationModelIdeal rho f q p
    exact specialized_ideal_eq_finiteNormalizationModel_points_le
      L rho f q p hmonic I hI

end

end TranslatedDepthSeven
