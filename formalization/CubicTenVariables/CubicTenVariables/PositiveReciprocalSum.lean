import Mathlib.Analysis.PSeries

/-! Uniform finite reciprocal-sum bounds from convergent real power series. -/

noncomputable section
namespace CubicTenVariables.PositiveReciprocalSum
open scoped BigOperators

/-- A convergent real power bounds every finite partial sum. The possible
zero index contributes zero since the exponent is negative. -/
theorem exists_uniform_rpow_bound (s : ℝ) (hs : s < -1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : Finset ℕ, (∑ a ∈ A, (a : ℝ)^s) ≤ C := by
  have hsum := Real.summable_nat_rpow.mpr hs
  refine ⟨max 1 (∑' a : ℕ, (a : ℝ)^s), le_max_left _ _, ?_⟩
  intro A
  exact (Summable.sum_le_tsum A (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg a) s)
    hsum).trans (le_max_right _ _)

/-- Pulling out the small positive power turns a reciprocal into a
convergent power, provided the integer lies in the prescribed interval. -/
theorem reciprocal_le_scaled_rpow (δ X : ℝ) (hδ : 0 ≤ δ)
    (a : ℕ) (ha : 0 < a) (haX : (a : ℝ) ≤ X) :
    (a : ℝ)^(-1 : ℝ) ≤ X^δ * (a : ℝ)^(-1-δ) := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  calc
    _ = (a : ℝ)^δ * (a : ℝ)^(-1-δ) := by
      rw [← Real.rpow_add ha0]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow ha0.le haX hδ) (Real.rpow_nonneg ha0.le _)

/-- One constant, chosen before the real cutoff and the finite set,
bounds every positive reciprocal sum by an arbitrary positive power. -/
theorem exists_uniform_reciprocal_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ A : Finset ℕ,
      (∀ a ∈ A, 0 < a) → (∀ a ∈ A, (a : ℝ) ≤ X) →
      (∑ a ∈ A, (a : ℝ)^(-1 : ℝ)) ≤ C*X^δ := by
  obtain ⟨C,hC,hseries⟩ := exists_uniform_rpow_bound (-1-δ) (by linarith)
  refine ⟨C,hC,?_⟩
  intro X hX A hpos hcut
  calc
    _ ≤ ∑ a ∈ A, X^δ * (a : ℝ)^(-1-δ) :=
      Finset.sum_le_sum (fun a ha => reciprocal_le_scaled_rpow δ X hδ.le a (hpos a ha) (hcut a ha))
    _ = X^δ * (∑ a ∈ A, (a : ℝ)^(-1-δ)) := (Finset.mul_sum ..).symm
    _ ≤ X^δ*C := mul_le_mul_of_nonneg_left (hseries A)
      (Real.rpow_nonneg (zero_le_one.trans hX) _)
    _ = _ := mul_comm _ _

/-- The same result with ordinary field reciprocals. -/
theorem exists_uniform_inverse_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ A : Finset ℕ,
      (∀ a ∈ A, 0 < a) → (∀ a ∈ A, (a : ℝ) ≤ X) →
      (∑ a ∈ A, (a : ℝ)⁻¹) ≤ C*X^δ := by
  simpa only [Real.rpow_neg_one] using exists_uniform_reciprocal_bound δ hδ

/-- The three-halves series has a fixed bound for all finite subsets. -/
theorem exists_uniform_three_halves_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : Finset ℕ,
      (∑ a ∈ A, (a : ℝ)^(-(3 : ℝ)/2)) ≤ C :=
  exists_uniform_rpow_bound _ (by norm_num)

end CubicTenVariables.PositiveReciprocalSum
