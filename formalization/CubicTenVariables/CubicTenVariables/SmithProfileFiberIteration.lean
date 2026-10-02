import CubicTenVariables.HessianProfileRoots
import CubicTenVariables.TranslatedHessianLeadingGeometry
import CubicTenVariables.ProfileConstantAbsorption

/-!
# Iterating literal Hessian-profile root fibers

This finite induction is an assembly lemma: the initial count and each
one-step fiber estimate are explicit hypotheses. It does not itself prove
those geometric or arithmetic estimates. The sets being counted retain the
polynomial equation and every prescribed profile entry.
-/

noncomputable section
namespace CubicTenVariables.SmithProfileFiberIteration

open MvPolynomial HessianProfileRoots PrimePowerFibers
open scoped BigOperators

variable {n : ℕ}

/-- Iteration for arbitrary initial and transition exponents. -/
theorem card_le_of_fiber_bounds (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (c : ℕ → ℕ) (B δ : ℕ) (w : ℕ → ℕ)
    (hbase : (roots F p 1 c).card ≤ B*p^δ)
    (hfiber : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ roots F p t c,
      ((roots F p (t+1) c).filter fun z =>
        (fun i => reduction p (Nat.le_succ t) (z i)) = y).card ≤ B*p^(w (t-1)))
    (a : ℕ) (ha : 1 ≤ a) :
    (roots F p a c).card ≤ B^a*p^(δ + ∑ j ∈ Finset.range (a-1), w j) := by
  classical
  induction a, ha using Nat.le_induction with
  | base => simpa using hbase
  | succ a ha ih =>
      rw [card_roots_succ_eq_sum]
      have hsum : (∑ j ∈ Finset.range (a+1-1), w j) =
          (∑ j ∈ Finset.range (a-1), w j) + w (a-1) := by
        rw [show a+1-1 = (a-1)+1 by omega, Finset.sum_range_succ]
      calc
        (∑ y ∈ roots F p a c, ((roots F p (a+1) c).filter fun z =>
            (fun i => reduction p (Nat.le_succ a) (z i)) = y).card) ≤
            ∑ _y ∈ roots F p a c, B*p^(w (a-1)) :=
          Finset.sum_le_sum (fun y hy => hfiber a ha y hy)
        _ = (roots F p a c).card * (B*p^(w (a-1))) := by simp
        _ ≤ (B^a*p^(δ + ∑ j ∈ Finset.range (a-1), w j)) * (B*p^(w (a-1))) :=
          Nat.mul_le_mul_right _ ih
        _ = B^(a+1)*p^(δ + ∑ j ∈ Finset.range (a+1-1), w j) := by
          rw [hsum, ← Nat.add_assoc, pow_add, pow_succ]
          ring

/-- The source's initial-rank and adjacent-profile transition exponents.
All fiber premises concern the actual reduction map between actual roots. -/
theorem card_le_profile_bound (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (c : ℕ → ℕ) (B : ℕ)
    (hbase : (roots F p 1 c).card ≤ B*p^(OnCubicRankCountsTen.deltaNat (c 0)))
    (hfiber : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ roots F p t c,
      ((roots F p (t+1) c).filter fun z =>
        (fun i => reduction p (Nat.le_succ t) (z i)) = y).card ≤
          B*p^(TranslatedHessianLeadingGeometry.tauNat (c (t-1) + c t)))
    (a : ℕ) (ha : 1 ≤ a) :
    (roots F p a c).card ≤ B^a*p^(OnCubicRankCountsTen.deltaNat (c 0) +
      ∑ j ∈ Finset.range (a-1), TranslatedHessianLeadingGeometry.tauNat (c j + c (j+1))) := by
  apply card_le_of_fiber_bounds F p c B (OnCubicRankCountsTen.deltaNat (c 0))
    (fun j => TranslatedHessianLeadingGeometry.tauNat (c j + c (j+1))) hbase ?_ a ha
  intro t ht y hy
  simpa only [Nat.sub_add_cancel ht] using hfiber t ht y hy

/-- One threshold absorbs the repeated constant, uniformly before all primes,
polynomials, profiles, and lengths. The initial and transition estimates
remain explicit premises of this assembly lemma. -/
theorem exists_threshold_real_bound (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 2 ≤ P ∧ ∀ (p : ℕ) [Fact p.Prime], P ≤ p →
      ∀ (F : MvPolynomial (Fin n) ℤ) (c : ℕ → ℕ) (δ : ℕ) (w : ℕ → ℕ),
        (roots F p 1 c).card ≤ B*p^δ →
        (∀ t : ℕ, 1 ≤ t → ∀ y ∈ roots F p t c,
          ((roots F p (t+1) c).filter fun z =>
            (fun i => reduction p (Nat.le_succ t) (z i)) = y).card ≤ B*p^(w (t-1))) →
        ∀ a : ℕ, 1 ≤ a →
          ((roots F p a c).card : ℝ) ≤
            (p : ℝ)^((δ + ∑ j ∈ Finset.range (a-1), w j : ℕ) + ε*(a : ℝ)) := by
  obtain ⟨P, hP, hbound⟩ := ProfileConstantAbsorption.exists_threshold_mul_rpow B ε hε
  refine ⟨P, hP, ?_⟩
  intro p hp hpP F c δ w hbase hfiber a ha
  have hn := card_le_of_fiber_bounds F p c B δ w hbase hfiber a ha
  have hc : ((roots F p a c).card : ℝ) ≤
      (B : ℝ)^a * (p : ℝ)^(δ + ∑ j ∈ Finset.range (a-1), w j) := by
    exact_mod_cast hn
  apply hc.trans
  simpa only [Real.rpow_natCast] using
    (hbound p hpP a (δ + ∑ j ∈ Finset.range (a-1), w j : ℕ))

end CubicTenVariables.SmithProfileFiberIteration
