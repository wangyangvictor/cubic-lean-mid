import TranslatedDepthSeven.FiniteNormalizationModelProductBound
import TranslatedDepthSeven.AffineZeroLocusQuotientPoints
import Mathlib.Data.ZMod.Basic

/-! Literal zero-set adapters for the proved product-of-monic-degrees point
bound. The coefficient map need not be injective, the model need not be
reduced or equidimensional, and the normalization map need not be injective.
The bound uses only the original monic relation degrees, before any field
or coefficient specialization is chosen. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteNormalizationModelPointCount
open TranslatedDepthSeven MvPolynomial Polynomial
open scoped BigOperators
universe u v

/-- Literal vanishing of an ideal over a coefficient map is precisely the
ordinary affine zero locus of its coefficient extension. -/
theorem vanishing_iff_zeroLocus_map
    {B : Type u} {K : Type v} [CommRing B] [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) B)) (ρ : B →+* K) (x : Fin n → K) :
    (∀ f ∈ I, eval₂Hom ρ x f = 0) ↔
      x ∈ affineIdealZeroLocus (I.map (MvPolynomial.map ρ)) := by
  rw [mem_affineIdealZeroLocus_iff_le_ker_aeval, Ideal.map_le_iff_le_comap]
  change (∀ f ∈ I, eval₂Hom ρ x f = 0) ↔
    ∀ f ∈ I, aeval x (MvPolynomial.map ρ f) = 0
  simp only [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map, MvPolynomial.coe_eval₂Hom]

/-- The literal coordinate-zero subtype and the quotient's rational points
have equal cardinality after an arbitrary coefficient specialization. -/
theorem natCard_vanishing_eq_quotient_points
    {B : Type u} {K : Type v} [CommRing B] [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) B)) (ρ : B →+* K) :
    Nat.card {x : Fin n → K // ∀ f ∈ I, eval₂Hom ρ x f = 0} =
      Nat.card ((MvPolynomial (Fin n) K ⧸ I.map (MvPolynomial.map ρ)) →ₐ[K] K) := by
  rw [← natCard_affineIdealZeroLocus_eq_quotientAlgHom]
  exact Nat.card_congr (Equiv.subtypeEquivRight (vanishing_iff_zeroLocus_map I ρ))

/-- Exact product-degree bound for the actual ideal-vanishing subtype of
the displayed finite-normalization model. -/
theorem points_le_prod
    {B : Type} [CommRing B] {n d r : ℕ}
    (equations : Fin r → MvPolynomial (Fin n) B)
    (parameters : Fin d → MvPolynomial (Fin n) B)
    (relations : Fin n → (MvPolynomial (Fin d) B)[X])
    (hmonic : ∀ i, (relations i).Monic)
    (K : Type) [Field K] [Finite K] (ρ : B →+* K) :
    Nat.card {x : Fin n → K //
      ∀ f ∈ finiteNormalizationModelIdeal equations parameters relations,
        eval₂Hom ρ x f = 0} ≤
      (∏ i, (relations i).natDegree) * Nat.card K ^ d := by
  rw [natCard_vanishing_eq_quotient_points]
  exact specialized_ideal_eq_finiteNormalizationModel_points_le K ρ
    equations parameters relations hmonic _
    (map_finiteNormalizationModelIdeal ρ equations parameters relations)

/-- One positive constant is chosen before all finite target fields and
coefficient maps. It is `max 1` of the product of the original degrees. -/
theorem exists_bound
    {B : Type} [CommRing B] {n d r : ℕ}
    (equations : Fin r → MvPolynomial (Fin n) B)
    (parameters : Fin d → MvPolynomial (Fin n) B)
    (relations : Fin n → (MvPolynomial (Fin d) B)[X])
    (hmonic : ∀ i, (relations i).Monic) :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ (K : Type) [Field K] [Finite K] (ρ : B →+* K),
      Nat.card {x : Fin n → K //
        ∀ f ∈ finiteNormalizationModelIdeal equations parameters relations,
          eval₂Hom ρ x f = 0} ≤ C * Nat.card K ^ d := by
  refine ⟨max 1 (∏ i, (relations i).natDegree), le_max_left _ _, ?_⟩
  intro K _ _ ρ
  exact (points_le_prod equations parameters relations hmonic K ρ).trans
    (Nat.mul_le_mul_right _ (le_max_right _ _))

/-- Prime-field form with the literal modulus power and no excluded primes. -/
theorem exists_prime_bound
    {B : Type} [CommRing B] {n d r : ℕ}
    (equations : Fin r → MvPolynomial (Fin n) B)
    (parameters : Fin d → MvPolynomial (Fin n) B)
    (relations : Fin n → (MvPolynomial (Fin d) B)[X])
    (hmonic : ∀ i, (relations i).Monic) :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime] (ρ : B →+* ZMod p),
      Nat.card {x : Fin n → ZMod p //
        ∀ f ∈ finiteNormalizationModelIdeal equations parameters relations,
          eval₂Hom ρ x f = 0} ≤ C * p ^ d := by
  obtain ⟨C, hC, hb⟩ := exists_bound equations parameters relations hmonic
  refine ⟨C, hC, ?_⟩
  intro p _ ρ
  simpa using hb (ZMod p) ρ

end CubicTenVariables.FiniteNormalizationModelPointCount
