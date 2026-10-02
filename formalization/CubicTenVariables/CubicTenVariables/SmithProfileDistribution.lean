import CubicTenVariables.HessianProfileLifts
import CubicTenVariables.SmithProfileFiberIteration

/-!
# Actual simultaneous Smith-profile distributions: the transition route

All base and transition estimates in the finite induction are discharged.
The bound counts genuine cubic roots modulo p^a with their entire actual
Hessian profile. A single constant precedes every prime, level and profile.
There is no literature premise in either endpoint of this module.
-/

noncomputable section
namespace CubicTenVariables.SmithProfileDistribution
open MvPolynomial HessianTheorem11 HessianProfileRoots
open OnCubicRankCountsTen TranslatedHessianLeadingGeometry
open scoped BigOperators

/-- The source's all-prime exponential-in-level transition estimate.
The label need not be monotone: impossible profiles simply give empty sets. -/
theorem exists_uniform_transition_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ (p : ℕ) [Fact p.Prime],
      ∀ (a : ℕ), 1 ≤ a → ∀ (c : ℕ → ℕ), c 0 ≤ 10 →
        (roots F p a c).card ≤ B^a*p^(deltaNat (c 0) +
          ∑ j ∈ Finset.range (a-1), tauNat (c j+c (j+1))) := by
  obtain ⟨A,hA1,hbase⟩ := exists_initial_bound F hF hA
  obtain ⟨C,hC1,hfiber⟩ := HessianProfileLifts.exists_uniform_fiber_bound F hF hA
  let B := max A C
  have hAB : A ≤ B := le_max_left _ _
  have hCB : C ≤ B := le_max_right _ _
  refine ⟨B,hA1.trans hAB,?_⟩
  intro p hp a ha c hc
  apply SmithProfileFiberIteration.card_le_profile_bound F p c B ?_ ?_ a ha
  · exact (hbase p c hc).trans (Nat.mul_le_mul_right _ hAB)
  · intro t ht y hy
    exact (hfiber p t ht c y hy).trans (Nat.mul_le_mul_right _ hCB)

/-- For sufficiently large primes the repeated constant is absorbed into
p^(epsilon*a). The prime threshold is chosen before every level and profile. -/
theorem exists_large_prime_transition_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 2 ≤ P ∧ ∀ (p : ℕ) [Fact p.Prime], P ≤ p →
      ∀ (a : ℕ), 1 ≤ a → ∀ (c : ℕ → ℕ), c 0 ≤ 10 →
        ((roots F p a c).card : ℝ) ≤
          (p : ℝ)^((deltaNat (c 0) +
            ∑ j ∈ Finset.range (a-1), tauNat (c j+c (j+1)) : ℕ) + ε*(a : ℝ)) := by
  obtain ⟨B,_,hB⟩ := exists_uniform_transition_bound F hF hA
  obtain ⟨P,hP,habsorb⟩ := ProfileConstantAbsorption.exists_threshold_mul_rpow B ε hε
  refine ⟨P,hP,?_⟩
  intro p hp hpP a ha c hc
  have hn := hB p a ha c hc
  have hreal : ((roots F p a c).card : ℝ) ≤
      (B : ℝ)^a * (p : ℝ)^(deltaNat (c 0) +
        ∑ j ∈ Finset.range (a-1), tauNat (c j+c (j+1))) := by exact_mod_cast hn
  apply hreal.trans
  simpa only [Real.rpow_natCast] using
    (habsorb p hpP a (deltaNat (c 0) +
      ∑ j ∈ Finset.range (a-1), tauNat (c j+c (j+1)) : ℕ))

end CubicTenVariables.SmithProfileDistribution
