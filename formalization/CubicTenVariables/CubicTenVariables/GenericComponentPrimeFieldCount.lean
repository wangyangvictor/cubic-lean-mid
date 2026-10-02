import CubicTenVariables.FiniteNormalizationModelPointCount
import CubicTenVariables.RelativeInjectiveNormalization
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! A fixed generic component has a uniform prime-field point bound on one
nonempty base principal open. The proof retains the actual component
contraction, the original specialized ideal and its Krull dimension. It uses
the explicit monic normalization model and clears its discrepancy with the
component equations on one additional open. No point-count literature
premise, reducedness or special-fiber equidimensionality is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
noncomputable section
namespace CubicTenVariables.GenericComponentPrimeFieldCount
open TranslatedDepthSeven MvPolynomial

/-- Composition of coefficient extensions on ideals. -/
private theorem map_map_coefficients
    {B S L : Type} [CommRing B] [CommRing S] [CommRing L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) B)) (ρ : B →+* S) (τ : S →+* L) :
    (I.map (MvPolynomial.map ρ)).map (MvPolynomial.map τ) =
      I.map (MvPolynomial.map (τ.comp ρ)) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext fun f => MvPolynomial.map_map ρ τ f

/-- One nonzero base element and one positive constant work before the
prime, coefficient map and dimension threshold are chosen. -/
theorem exists_bound
    {B K : Type} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Field K] [Algebra B K] [IsFractionRing B K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) B))
    (Q : Ideal (MvPolynomial (Fin n) K))
    (hQ : Q ∈ (I.map (MvPolynomial.map (algebraMap B K))).minimalPrimes) :
    ∃ s : B, s ≠ 0 ∧ ∃ C : ℕ, 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime] (ρ : B →+* ZMod p), ρ s ≠ 0 → ∀ j : ℕ,
        ringKrullDim (MvPolynomial (Fin n) (ZMod p) ⧸
          I.map (MvPolynomial.map ρ)) ≤ (j : WithBot ℕ∞) →
        Nat.card {x : Fin n → ZMod p //
          ∀ f ∈ Q.comap (MvPolynomial.map (algebraMap B K)), eval₂Hom ρ x f = 0} ≤
            C * p ^ j := by
  classical
  obtain ⟨r, generators, hJminimal, hJgeneric, d, _hdn, Δ, hΔ,
      equations, parameters, relations, _hequations, hmonic, hmodelGeneric,
      hJmodel, _hinjective, _hfinite, hdimension⟩ :=
    RelativeInjectiveNormalization.exists_principalOpen_model I Q hQ
  let J : Ideal (MvPolynomial (Fin n) B) := Ideal.span (Set.range generators)
  let S := Localization.Away Δ
  let κ : S →+* K := awayToFractionRing (R := B) (K := K) Δ hΔ
  let M := finiteNormalizationModelIdeal equations parameters relations
  let J₀ := J.map (MvPolynomial.map (algebraMap B S))
  letI : Algebra S K := κ.toAlgebra
  letI : IsScalarTower B S K := IsScalarTower.of_algebraMap_eq fun b =>
    (awayToFractionRing_algebraMap Δ hΔ b).symm
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S
    (powers_le_nonZeroDivisors_of_noZeroDivisors hΔ)
  letI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers Δ) S K
  have hκcomp : κ.comp (algebraMap B S) = algebraMap B K :=
    RingHom.ext fun b => awayToFractionRing_algebraMap Δ hΔ b
  have hJ₀generic : J₀.map (MvPolynomial.map (algebraMap S K)) = Q := by
    change (J.map (MvPolynomial.map (algebraMap B S))).map (MvPolynomial.map κ) = Q
    rw [map_map_coefficients, hκcomp]
    exact hJgeneric
  obtain ⟨δ, hδ, _hclear, hequal⟩ :=
    exists_nonzero_base_open_model_eq_componentClosure
      J₀ M hJmodel Q hJ₀generic hmodelGeneric
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj Δ δ
  have hΔS : algebraMap B S Δ ≠ 0 :=
    (IsLocalization.Away.algebraMap_isUnit (S := S) Δ).ne_zero
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact mul_ne_zero hδ (pow_ne_zero k hΔS) ha
  obtain ⟨C, hC, hcount⟩ :=
    FiniteNormalizationModelPointCount.exists_prime_bound
      equations parameters relations hmonic
  refine ⟨Δ * a, mul_ne_zero hΔ ha0, C, hC, ?_⟩
  intro p _ ρ hs j hj
  have hρΔ : ρ Δ ≠ 0 := by
    intro h
    exact hs (by simp [map_mul, h])
  have hρa : ρ a ≠ 0 := by
    intro h
    exact hs (by simp [map_mul, h])
  let ρ' : S →+* ZMod p := IsLocalization.Away.lift Δ (isUnit_iff_ne_zero.mpr hρΔ)
  have hρ'comp : ρ'.comp (algebraMap B S) = ρ :=
    RingHom.ext fun b => IsLocalization.Away.lift_eq Δ (isUnit_iff_ne_zero.mpr hρΔ) b
  have hρ'δ : ρ' δ ≠ 0 := by
    intro h
    have hh := congrArg ρ' ha
    have ha' : ρ' (algebraMap B S a) = ρ a := DFunLike.congr_fun hρ'comp a
    rw [map_mul, map_pow, h, zero_mul, ha'] at hh
    exact hρa hh.symm
  have hmodels : J.map (MvPolynomial.map ρ) = M.map (MvPolynomial.map ρ') := by
    have hh := hequal (ZMod p) ρ' (isUnit_iff_ne_zero.mpr hρ'δ)
    change (J.map (MvPolynomial.map (algebraMap B S))).map (MvPolynomial.map ρ') = _ at hh
    rw [map_map_coefficients, hρ'comp] at hh
    exact hh
  have hIJ : I ≤ J := hJminimal.1.2
  have hIJmap : I.map (MvPolynomial.map ρ) ≤ J.map (MvPolynomial.map ρ) :=
    Ideal.map_mono hIJ
  have hmodeldim : ringKrullDim (MvPolynomial (Fin n) (ZMod p) ⧸
      M.map (MvPolynomial.map ρ')) ≤ (j : WithBot ℕ∞) := by
    rw [← hmodels]
    exact (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJmap)
      (Ideal.Quotient.factor_surjective hIJmap)).trans hj
  have hdj : d ≤ j := hdimension p ρ' j hmodeldim
  have hJQ : J ≤ Q.comap (MvPolynomial.map (algebraMap B K)) :=
    Ideal.map_le_iff_le_comap.mp (le_of_eq hJgeneric)
  let liftPoint :
      {x : Fin n → ZMod p //
        ∀ f ∈ Q.comap (MvPolynomial.map (algebraMap B K)), eval₂Hom ρ x f = 0} →
      {x : Fin n → ZMod p // ∀ f ∈ M, eval₂Hom ρ' x f = 0} := fun x =>
    ⟨x.1, by
      apply (FiniteNormalizationModelPointCount.vanishing_iff_zeroLocus_map M ρ' x.1).mpr
      rw [← hmodels]
      apply (FiniteNormalizationModelPointCount.vanishing_iff_zeroLocus_map J ρ x.1).mp
      exact fun f hf => x.2 f (hJQ hf)⟩
  have hinj : Function.Injective liftPoint := by
    intro x y h
    exact Subtype.ext (show x.1 = y.1 from congrArg (fun z => z.1) h)
  exact (Nat.card_le_card_of_injective liftPoint hinj).trans
    ((hcount p ρ').trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_right (Fact.out : p.Prime).one_le hdj)))

end CubicTenVariables.GenericComponentPrimeFieldCount
