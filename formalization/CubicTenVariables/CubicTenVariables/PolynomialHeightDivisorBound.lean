import CubicTenVariables.PolynomialDivisorBound

/-! Divisor counts for the positive exceptional integers already constructed
by the P and Q partitions. Only their proved polynomial height bound is
needed; no choice of a particular defining polynomial is required. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PolynomialHeightDivisorBound

/-- One constant absorbs the divisor count of every positive integer
with the stated polynomial height bound, uniformly in the height. -/
theorem exists_bound (C : ℝ) (hC : 1 ≤ C) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ H : ℝ, 1 ≤ H → ∀ Δ : ℕ, 1 ≤ Δ →
      (Δ : ℝ) ≤ C*H^d → (Δ.divisors.card : ℝ) ≤ A*H^ε := by
  let η : ℝ := ε/((d : ℝ)+1)
  have hden : 0 < (d : ℝ)+1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨A,hA,hdiv⟩ := PolynomialDivisorBound.exists_divisor_bound η hη
  have hCη : 1 ≤ C^η := Real.one_le_rpow hC hη.le
  have hM : 1 ≤ A*C^η := by nlinarith
  refine ⟨A*C^η,hM,?_⟩
  intro H hH Δ hΔ hheight
  have hΔ0 : (Δ : ℤ) ≠ 0 := by exact_mod_cast (by omega : Δ ≠ 0)
  have hc : (Δ.divisors.card : ℝ) ≤ A*(Δ : ℝ)^η := by
    simpa only [Int.natAbs_natCast,Int.cast_natCast,abs_of_nonneg (show (0 : ℝ) ≤ Δ from Nat.cast_nonneg Δ)] using
      hdiv (Δ : ℤ) hΔ0
  have he : (d : ℝ)*η ≤ ε := by
    have heq : ((d : ℝ)+1)*η = ε := by dsimp [η]; field_simp
    nlinarith
  calc
    _ ≤ A*(Δ : ℝ)^η := hc
    _ ≤ A*(C*H^d)^η := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg Δ) hheight hη.le) (by linarith)
    _ = A*C^η*H^((d : ℝ)*η) := by
      rw [Real.mul_rpow (by linarith : 0 ≤ C) (by positivity),
        ← Real.rpow_natCast_mul (by linarith : 0 ≤ H)]
      ring
    _ ≤ A*C^η*H^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hH he) (by positivity)

/-- Two independently chosen P/Q certificates are absorbed with the
same height exponent, including certificates equal to one. -/
theorem exists_product_bound (C : ℝ) (hC : 1 ≤ C) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ H : ℝ, 1 ≤ H → ∀ Δ Θ : ℕ,
      1 ≤ Δ → 1 ≤ Θ → (Δ : ℝ) ≤ C*H^d → (Θ : ℝ) ≤ C*H^d →
      (Δ.divisors.card : ℝ)*(Θ.divisors.card : ℝ) ≤ A*H^ε := by
  obtain ⟨A,hA,hbound⟩ := exists_bound C hC d (ε/2) (by linarith)
  refine ⟨A^2,one_le_pow₀ hA,?_⟩
  intro H hH Δ Θ hΔ hΘ hΔH hΘH
  have hprod : H^(ε/2)*H^(ε/2) = H^ε := by
    rw [← Real.rpow_add (by linarith : 0 < H)]
    congr 1
    ring
  calc
    _ ≤ (A*H^(ε/2))*(A*H^(ε/2)) := mul_le_mul
      (hbound H hH Δ hΔ hΔH) (hbound H hH Θ hΘ hΘH)
      (Nat.cast_nonneg _) (by positivity)
    _ = A^2*(H^(ε/2)*H^(ε/2)) := by ring
    _ = A^2*H^ε := by rw [hprod]

end CubicTenVariables.PolynomialHeightDivisorBound
