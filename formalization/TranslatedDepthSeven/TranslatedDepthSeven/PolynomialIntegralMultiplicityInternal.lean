import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Integral multiplicity of an eventually integer-valued polynomial

The top forward difference equals degree-factorial times the leading
coefficient. It is an integer linear combination of consecutive values.
Thus integrality only on a tail of the natural numbers suffices. No
geometric or Hilbert-polynomial input is used here.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000

/-- Eventual integer values force factorial times the leading coefficient
to be an integer, including for constant and zero polynomials. -/
theorem exists_int_leadingCoeff_mul_factorial_of_eventually_integral
    (P : Polynomial ℚ)
    (hP : ∃ N : ℕ, ∀ n ≥ N, ∃ z : ℤ, P.eval (n : ℚ) = (z : ℚ)) :
    ∃ z : ℤ, P.leadingCoeff * (P.natDegree.factorial : ℚ) = (z : ℚ) := by
  classical
  obtain ⟨N, hN⟩ := hP
  choose z hz using fun k : ℕ ↦ hN (N + k) (Nat.le_add_right N k)
  have htop : P.leadingCoeff * (P.natDegree.factorial : ℚ) =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        (((-1 : ℤ) ^ (P.natDegree - k) * (P.natDegree.choose k : ℤ) : ℤ) : ℚ) *
          P.eval ((N + k : ℕ) : ℚ) := by
    have h := congrFun P.fwdDiff_iter_degree_eq_factorial (N : ℚ)
    rw [fwdDiff_iter_eq_sum_shift] at h
    simpa [nsmul_eq_mul, zsmul_eq_mul, mul_comm] using h.symm
  refine ⟨∑ k ∈ Finset.range (P.natDegree + 1),
    (-1 : ℤ) ^ (P.natDegree - k) * (P.natDegree.choose k : ℤ) * z k, ?_⟩
  rw [htop]
  simp only [hz, Int.cast_sum, Int.cast_mul]

/-- With positive leading coefficient, the resulting integral multiplicity
is a positive natural number, in the exact Hilbert-certificate convention. -/
theorem exists_positive_nat_multiplicity_of_eventually_integral
    (P : Polynomial ℚ) (hpositive : 0 < P.leadingCoeff)
    (hP : ∃ N : ℕ, ∀ n ≥ N, ∃ z : ℤ, P.eval (n : ℚ) = (z : ℚ)) :
    ∃ d : ℕ, 0 < d ∧ P.leadingCoeff = (d : ℚ) / (P.natDegree.factorial : ℚ) := by
  obtain ⟨z, hz⟩ := exists_int_leadingCoeff_mul_factorial_of_eventually_integral P hP
  have hzpos : 0 < z := by
    have hq : (0 : ℚ) < (z : ℚ) := by
      rw [← hz]
      exact mul_pos hpositive (by positivity)
    exact_mod_cast hq
  have hcast : (z.toNat : ℚ) = (z : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt hzpos)
  refine ⟨z.toNat, by omega, ?_⟩
  apply (eq_div_iff (by positivity : (P.natDegree.factorial : ℚ) ≠ 0)).mpr
  exact hz.trans hcast.symm

end

end TranslatedDepthSeven
