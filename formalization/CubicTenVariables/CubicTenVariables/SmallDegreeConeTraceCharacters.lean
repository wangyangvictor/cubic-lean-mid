import CubicTenVariables.SmallDegreeConeMomentDecay
import CubicTenVariables.FiniteFieldTraceCharacter

/-! The actual trace-extension character in the low-degree cone moment
limit. One nontrivial character of F_p supplies all extension characters;
their nontriviality is proved, not separately assumed. This is an arithmetic
adapter only and asserts no lisse-sheaf trace dichotomy. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.SmallDegreeConeTraceCharacters
open MvPolynomial Matrix HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven Filter FiniteFieldTraceCharacter SmallDegreeConeMomentDecay
open scoped BigOperators Classical Topology
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Extending a prime-field character to the prime field changes nothing. -/
theorem primeTraceCharacter_self (p : ℕ) [Fact p.Prime]
    (ψ : AddChar (ZMod p) ℂ) : primeTraceCharacter p (ZMod p) ψ = ψ := by
  ext x
  letI : Algebra (ZMod p) (ZMod p) := ZMod.algebra (ZMod p) p
  have hm : algebraMap (ZMod p) (ZMod p) = RingHom.id (ZMod p) := Subsingleton.elim _ _
  have ht := prime_trace_eq_sum_pow p 1 (ZMod p) (by simp) x
  have ht' :
      letI : Algebra (ZMod p) (ZMod p) := ZMod.algebra (ZMod p) p
      Algebra.trace (ZMod p) (ZMod p) x = x := by
    simpa only [hm, RingHom.id_apply, Finset.sum_range_one, pow_zero, pow_one] using ht
  change ψ _ = ψ x
  exact congrArg ψ ht'

/-- Orthogonality gives the exact qT normalization at every frequency,
including zero. The positive number of variables is necessary for q^(n-1). -/
theorem completeSum_eq_card_mul_normalized {K : Type*} [Field K] [Fintype K]
    {n : ℕ} (hn : 1 ≤ n) (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) K) (v : Fin n → K) :
    FiniteFieldFourier.completeSum ψ F v =
      (Fintype.card K : ℂ)*normalizedFourierSum ψ F v := by
  have h := FiniteFieldFourier.completeSum_add_linear_phase ψ hψ F v
  by_cases hv : v = 0
  · subst v
    have hs : (∑ x : Fin n → K, ψ (dotProduct (0 : Fin n → K) x)) =
        (Fintype.card K : ℂ)^n := by simp
    rw [hs] at h
    have hp : (Fintype.card K : ℂ)*(Fintype.card K : ℂ)^(n-1) =
        (Fintype.card K : ℂ)^n := by
      rw [← pow_succ']
      congr 1
      omega
    simp only [normalizedFourierSum, ite_true, mul_sub, hp]
    exact eq_sub_of_add_eq h
  · rw [FiniteFieldFourier.sum_linear_phase_eq_zero ψ hψ v hv, add_zero] at h
    simpa only [normalizedFourierSum, if_neg hv, sub_zero] using h

/-- The literal prime complete sum is p times the manuscript's T,
including frequencies that reduce to zero modulo p. -/
theorem completeCubicSum_eq_prime_mul_normalized {n : ℕ} (hn : 1 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ) :
    completeCubicSum F p v = (p : ℂ)*normalizedFourierSum
      (primeTraceCharacter p (ZMod p) ZMod.stdAddChar)
      (map (Int.castRingHom (ZMod p)) F) (fun i => (v i : ZMod p)) := by
  rw [primeTraceCharacter_self, PrimeSumAdapter.completeCubicSum_eq_finiteFieldCompleteSum]
  simpa only [ZMod.card] using completeSum_eq_card_mul_normalized hn
    (ZMod.stdAddChar : AddChar (ZMod p) ℂ) (PrimeSumAdapter.stdAddChar_ne_one p)
    (map (Int.castRingHom (ZMod p)) F) (fun i => (v i : ZMod p))

/-- The actual trace-character moment limit on every finite subset of
the reduced cone model. Only base-character nontriviality is assumed.
The exceptional integer is fixed before the prime, extension family and
character; no cardinality-one field is required at a=0. -/
theorem exists_decay
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {t : ℕ} (G : Fin t → MvPolynomial (Fin 10) ℤ) (r d : ℕ)
    (hprime : (modelIdeal G).IsPrime)
    (hgeometric : ((modelIdeal G).map (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : (modelIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree (modelIdeal G) r d)
    (hsmall : r+d ≤ 8) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
      ∀ (K : ℕ → Type) [∀ a, Field (K a)] [∀ a, Fintype (K a)] [∀ a, CharP (K a) p]
        (ψ : AddChar (ZMod p) ℂ) (U : ∀ a, Finset (Fin 10 → K a)),
        ψ ≠ 1 →
        (∀ a, 1 ≤ a → Fintype.card (K a) = p^a) →
        (∀ a, 1 ≤ a → ∀ v ∈ U a, ∀ i,
          eval v (map (Int.castRingHom (K a)) (G i)) = 0) →
        Tendsto (fun a =>
          (∑ v ∈ U a, ‖normalizedFourierSum (primeTraceCharacter p (K a) ψ)
            (map (Int.castRingHom (K a)) F) v‖^2) /
              (p : ℝ)^(a*18)) atTop (𝓝 0) := by
  obtain ⟨N,hN,hlimit⟩ := SmallDegreeConeMomentDecay.exists_decay
    degreeSpan smooth spread weil F hF hAn G r d hprime hgeometric hhom hdegree hsmall
  refine ⟨N,hN,?_⟩
  intro p _ hpN K _ _ _ ψ U hψ hcard hU
  exact hlimit p (Fact.out : p.Prime) hpN K
    (fun a => primeTraceCharacter p (K a) ψ) U hcard
    (fun a _ => family_nontrivial p K ψ hψ a) hU

end CubicTenVariables.SmallDegreeConeTraceCharacters
