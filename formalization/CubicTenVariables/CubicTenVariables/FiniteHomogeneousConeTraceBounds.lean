import CubicTenVariables.HomogeneousConeTraceRestriction

/-! Uniformity for a finite collection of actual rational cone models.
The equations may vary in number from cone to cone. One exceptional integer
and one bound constant precede all primes, characters, finite fields, and
cone indices. The same positive homogeneous opens support both the Fourier
and prime complete-sum bounds, avoid prescribed homogeneous equations,
and retain their actual closed residuals.
The only literature premises are those of the individual cone theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.FiniteHomogeneousConeTraceBounds

open MvPolynomial HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven FiniteFieldTraceCharacter PolynomialExponentialFamily
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Simultaneous literal trace bounds and complete-sum bounds on positive
homogeneous principal opens of any finite collection of the required cones,
with each open avoiding its prescribed equation `Q i`. -/
theorem exists_bounds_avoiding
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {k : ℕ} (t : Fin k → ℕ)
    (G : ∀ i : Fin k, Fin (t i) → ParameterPolynomial 10)
    (r d w : Fin k → ℕ)
    (hprime : ∀ i, (baseIdeal (G i)).IsPrime)
    (hgeometric : ∀ i, ((baseIdeal (G i)).map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : ∀ i, (baseIdeal (G i)).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : ∀ i, Published.HasProjectiveDimensionDegree (baseIdeal (G i)) (r i) (d i))
    (hsmall : ∀ i, r i + d i ≤ 8) (hweight : ∀ i, r i + 1 + w i + 1 = 18)
    (Q : Fin k → ParameterPolynomial 10) (e : Fin k → ℕ)
    (hQ : ∀ i, (Q i).IsHomogeneous (e i))
    (hQI : ∀ i, map (Int.castRingHom ℚ) (Q i) ∉ baseIdeal (G i)) :
    ∃ (h : Fin k → ParameterPolynomial 10) (j : Fin k → ℕ) (N C : ℕ),
      (∀ i, 0 < j i ∧ (h i).IsHomogeneous (j i) ∧
        map (Int.castRingHom ℚ) (h i) ∉ baseIdeal (G i) ∧
        Q i ∣ h i ∧
        (ConePrincipalOpen.residualIdeal (baseIdeal (G i))
          (map (Int.castRingHom ℚ) (h i))).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ) ∧
        ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
          ConePrincipalOpen.residualIdeal (baseIdeal (G i))
            (map (Int.castRingHom ℚ) (h i))) ≤ (r i : WithBot ℕ∞) ∧
        PrimeSpectrum.zeroLocus (ConePrincipalOpen.residualIdeal (baseIdeal (G i))
          (map (Int.castRingHom ℚ) (h i)) : Set (MvPolynomial (Fin 10) ℚ)) ⊂
            PrimeSpectrum.zeroLocus (baseIdeal (G i) : Set (MvPolynomial (Fin 10) ℚ))) ∧
      1 ≤ N ∧ 1 ≤ C ∧
      (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
        ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
        ∀ (K : Type) [Field K] [Fintype K] [CharP K p]
          (i : Fin k) (v : Fin 10 → K), v ∈ parameterPoints (G i) (h i) K →
          ‖normalizedFourierSum (primeTraceCharacter p K ψ)
            (map (Int.castRingHom K) F) v‖ ≤
              (C : ℝ) * (Fintype.card K : ℝ)^((w i : ℝ)/2)) ∧
      (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
        ∀ (i : Fin k) (v : Fin 10 → ℤ),
          (fun a => (v a : ZMod p)) ∈ parameterPoints (G i) (h i) (ZMod p) →
          ‖completeCubicSum F p v‖ ≤ (C : ℝ)*(p : ℝ)^((w i : ℝ)/2+1)) := by
  choose h j N C hj hh hnot hQdiv hN hC hbound using fun i =>
    HomogeneousConeTraceRestriction.exists_bound_avoiding degreeSpan smooth spread weil dichotomy
      F hF hAn (G i) (r i) (d i) (w i) (hprime i) (hgeometric i)
      (hhom i) (hdegree i) (hsmall i) (hweight i) (Q i) (e i) (hQ i) (hQI i)
  let C₀ : ℕ := 1 + ∑ i, C i
  have hCC (i : Fin k) : (C i : ℝ) ≤ (C₀ : ℝ) := by
    have hs : C i ≤ ∑ a, C a :=
      Finset.single_le_sum (fun a _ => Nat.zero_le (C a)) (Finset.mem_univ i)
    have hi : C i ≤ C₀ := by dsimp [C₀]; omega
    exact_mod_cast hi
  have hgood (p : ℕ) (hp : ¬ p ∣ ∏ i, N i) (i : Fin k) : ¬ p ∣ N i := by
    intro hi
    exact hp (hi.trans (Finset.dvd_prod_of_mem N (Finset.mem_univ i)))
  have hcommon : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ ∏ i, N i →
      ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p]
        (i : Fin k) (v : Fin 10 → K), v ∈ parameterPoints (G i) (h i) K →
        ‖normalizedFourierSum (primeTraceCharacter p K ψ)
          (map (Int.castRingHom K) F) v‖ ≤
            (C₀ : ℝ) * (Fintype.card K : ℝ)^((w i : ℝ)/2) := by
    intro p _ hp ψ hψ K _ _ _ i v hv
    exact (hbound i p (hgood p hp i) ψ hψ K v hv).trans
      (mul_le_mul_of_nonneg_right (hCC i) (Real.rpow_nonneg (by positivity) _))
  refine ⟨h, j, ∏ i, N i, C₀, ?_, Finset.one_le_prod' (fun i _ => hN i),
    by dsimp [C₀]; omega, hcommon, ?_⟩
  · intro i
    exact ⟨hj i, hh i, hnot i, hQdiv i,
      HomogeneousPrincipalOpen.residual_isHomogeneous _ (hhom i) _ (j i) ((hh i).map _),
      ConePrincipalOpen.residual_dimension_le _ (hprime i) _ (hnot i) (r i) (hdegree i).1,
      ConePrincipalOpen.residual_zeroLocus_ssubset _ (hprime i) _ (hnot i)⟩
  · intro p _ hpN i v hv
    have hb := hcommon p hpN ZMod.stdAddChar (PrimeSumAdapter.stdAddChar_ne_one p)
      (ZMod p) i (fun a => (v a : ZMod p)) hv
    rw [ZMod.card] at hb
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    rw [SmallDegreeConeTraceCharacters.completeCubicSum_eq_prime_mul_normalized
      (by omega : 1 ≤ 10), norm_mul, Complex.norm_natCast]
    calc
      (p : ℝ)*_ ≤ (p : ℝ)*((C₀ : ℝ)*(p : ℝ)^((w i : ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hb hp.le
      _ = (C₀ : ℝ)*(p : ℝ)^((w i : ℝ)/2+1) := by
        rw [Real.rpow_add hp, Real.rpow_one]
        ring

end CubicTenVariables.FiniteHomogeneousConeTraceBounds
