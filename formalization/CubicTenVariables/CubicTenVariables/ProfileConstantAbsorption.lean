import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absorbing a fixed transition constant into a prime epsilon factor

A single threshold is selected from the fixed constant and positive epsilon
before either the prime (indeed any sufficiently large natural number) or
profile length is chosen. All lengths, including zero, are covered.
-/

noncomputable section
namespace CubicTenVariables.ProfileConstantAbsorption

open Filter

/-- A fixed per-step natural constant is absorbed uniformly in the number of
steps. No primality assumption or lower bound on `B` is necessary. -/
theorem exists_threshold (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 2 ≤ P ∧ ∀ p : ℕ, P ≤ p → ∀ a : ℕ,
      (B : ℝ)^a ≤ (p : ℝ)^(ε * (a : ℝ)) := by
  have hlimit : Tendsto (fun p : ℕ => (p : ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨P, hP⟩ : ∃ P : ℕ, ∀ p : ℕ, P ≤ p → (B : ℝ) ≤ (p : ℝ)^ε :=
    eventually_atTop.mp (hlimit.eventually (eventually_ge_atTop (B : ℝ)))
  refine ⟨max 2 P, le_max_left _ _, ?_⟩
  intro p hp a
  rw [Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  exact pow_le_pow_left₀ (Nat.cast_nonneg B) (hP p ((le_max_right _ _).trans hp)) a

/-- The same threshold absorbs the transition factor next to any real power
of the modulus. The real exponent can be negative. -/
theorem exists_threshold_mul_rpow (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 2 ≤ P ∧ ∀ p : ℕ, P ≤ p → ∀ (a : ℕ) (b : ℝ),
      (B : ℝ)^a * (p : ℝ)^b ≤ (p : ℝ)^(b + ε * (a : ℝ)) := by
  obtain ⟨P, hP, hbound⟩ := exists_threshold B ε hε
  refine ⟨P, hP, ?_⟩
  intro p hp a b
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le (by omega : 0 < P) hp
  calc
    (B : ℝ)^a * (p : ℝ)^b ≤ (p : ℝ)^(ε * (a : ℝ)) * (p : ℝ)^b :=
      mul_le_mul_of_nonneg_right (hbound p hp a) (Real.rpow_nonneg hp0.le b)
    _ = (p : ℝ)^(b + ε * (a : ℝ)) := by rw [← Real.rpow_add hp0, add_comm]

/-- Source-shaped exponent bookkeeping for a fixed dimension contribution
and any real penalty. One threshold works for all lengths and penalties. -/
theorem exists_threshold_profile (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 2 ≤ P ∧ ∀ p : ℕ, P ≤ p → ∀ (a : ℕ) (D penalty : ℝ),
      (B : ℝ)^a * (p : ℝ)^(D * (a : ℝ) - penalty) ≤
        (p : ℝ)^((D + ε) * (a : ℝ) - penalty) := by
  obtain ⟨P, hP, hbound⟩ := exists_threshold_mul_rpow B ε hε
  refine ⟨P, hP, ?_⟩
  intro p hp a D penalty
  have he : D * (a : ℝ) - penalty + ε * (a : ℝ) =
      (D + ε) * (a : ℝ) - penalty := by ring
  simpa only [he] using hbound p hp a (D * (a : ℝ) - penalty)

end CubicTenVariables.ProfileConstantAbsorption
