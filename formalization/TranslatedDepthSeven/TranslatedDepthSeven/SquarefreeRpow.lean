import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TranslatedDepthSeven.SquarefreeResidueCount

/-!
# Real powers of a square-free prime product

This file proves the finite-product identity used when Salberger's
several-prime condition is specialized to a square-free modulus.  The result
is elementary but is kept explicit because the exponent is a real number,
not a natural power.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Real powers distribute over a finite product of natural numbers. -/
theorem finset_prod_natCast_rpow (P : Finset ℕ) (α : ℝ) :
    ∏ p ∈ P, (p : ℝ) ^ α = ((∏ p ∈ P, p : ℕ) : ℝ) ^ α := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg p)
          (Nat.cast_nonneg (∏ q ∈ P, q)), ih]

/-- The several-prime product written directly with the reservoir notation. -/
theorem finset_prod_natCast_rpow_eq_primeProduct
    (P : Finset ℕ) (α : ℝ) :
    ∏ p ∈ P, (p : ℝ) ^ α = (primeProduct P : ℝ) ^ α := by
  simpa only [primeProduct] using finset_prod_natCast_rpow P α

/-- Subtype-indexed form, matching an enumeration by the prime divisors of
the square-free reservoir modulus. -/
theorem primeSubtype_prod_natCast_rpow_eq_primeProduct
    (P : Finset ℕ) (α : ℝ) :
    (∏ p : P, ((p : ℕ) : ℝ) ^ α) = (primeProduct P : ℝ) ^ α := by
  calc
    (∏ p : P, ((p : ℕ) : ℝ) ^ α) =
        ∏ p ∈ P, (p : ℝ) ^ α := by
      simpa only using
        (Finset.prod_coe_sort P (fun p : ℕ ↦ (p : ℝ) ^ α))
    _ = (primeProduct P : ℝ) ^ α :=
      finset_prod_natCast_rpow_eq_primeProduct P α

end

end TranslatedDepthSeven
