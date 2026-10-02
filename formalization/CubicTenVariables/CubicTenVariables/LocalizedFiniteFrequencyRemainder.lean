import CubicTenVariables.FiniteFrequencyRemainder
import CubicTenVariables.LocalizedFrequencyComparison

/-! The finite localization remainder for the literal restricted complete
sums. Their true lcm normalization cancels the entire inner residue count,
leaving the same q bound and decay constant as in the unrestricted case. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedFiniteFrequencyRemainder
open MvPolynomial DyadicFrequencyError LocalSupremumWindow
open scoped BigOperators

/-- The true lcm normalization cancels ten inner powers, leaving q. -/
theorem weighted_modulus_le (F : MvPolynomial (Fin 10) ℤ)
    (q W : ℕ) (hq : 1 ≤ q) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (B : ℝ) :
    ((Nat.lcm q W : ℝ)^10)⁻¹ *
      (∑ v ∈ frequencies 10 B, ‖localizedCompleteCubicSum F q W Ω v‖) ≤
      ((frequencies 10 B).card : ℝ)*(q : ℝ) := by
  have hq0 : 0 < q := Nat.zero_lt_one.trans_le hq
  have hℓ0 : (0 : ℝ) < Nat.lcm q W := by exact_mod_cast Nat.lcm_pos hq0 hW
  calc
    _ ≤ ((Nat.lcm q W : ℝ)^10)⁻¹ *
        (∑ _v ∈ frequencies 10 B, (q : ℝ)*(Nat.lcm q W : ℝ)^10) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun v _ =>
        LocalizedFrequencyComparison.trivial_bound F q W hq0 hW Ω v
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; field_simp

/-- Summation uses the original q-dyadic family, not an lcm-dyadic family. -/
theorem weighted_complete_sum_le (F : MvPolynomial (Fin 10) ℤ)
    (W : ℕ) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (P R B : ℝ) (m : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hRP : 2*R ≤ P^2) (hB0 : 0 ≤ B) (hB : B ≤ P^m) :
    (∑ q ∈ moduli R, ((Nat.lcm q W : ℝ)^10)⁻¹ *
      ∑ v ∈ frequencies 10 B, ‖localizedCompleteCubicSum F q W Ω v‖) ≤
      (2*7^10 : ℝ)*P^(10*m+4) := by
  have hc := FiniteFrequencyRemainder.frequency_card_le P B m hP hB0 hB
  have hs : (∑ q ∈ moduli R, (q : ℝ)) ≤ 2*P^4 := by
    apply (DyadicFrequencyTruncation.sum_moduli_le R (P^2) (sq_nonneg P) hRP).trans
    have hP2 : 1 ≤ P^2 := one_le_pow₀ hP
    nlinarith [sq_nonneg (P^2-1)]
  calc
    _ ≤ ∑ q ∈ moduli R, ((frequencies 10 B).card : ℝ)*(q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : (1 : ℝ) ≤ q := hR.trans ((mem_moduli R q).mp hq).1.le
      exact weighted_modulus_le F q W (by exact_mod_cast hq1) hW Ω B
    _ = ((frequencies 10 B).card : ℝ)*(∑ q ∈ moduli R, (q : ℝ)) :=
      (Finset.mul_sum ..).symm
    _ ≤ ((7:ℝ)^10*P^(10*m))*(2*P^4) :=
      mul_le_mul hc hs (Finset.sum_nonneg fun q _ => Nat.cast_nonneg q) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The finite remainder has the same constant uniformly in W and Ω. -/
theorem bound (F : MvPolynomial (Fin 10) ℤ)
    (W : ℕ) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (P R φ B : ℝ) (m A : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hRP : 2*R ≤ P^2) (hB0 : 0 ≤ B) (hB : B ≤ P^m) :
    (4*φ*P^(-((A+10*m+4 : ℕ) : ℝ)))*
      (∑ q ∈ moduli R, ((Nat.lcm q W : ℝ)^10)⁻¹ *
        ∑ v ∈ frequencies 10 B, ‖localizedCompleteCubicSum F q W Ω v‖) ≤
      (8*7^10 : ℝ)*P^(-(A : ℝ)) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hcancel : P^(-((A+10*m+4 : ℕ) : ℝ))*P^(10*m+4)=P^(-(A : ℝ)) := by
    rw [← Real.rpow_natCast P (10*m+4),← Real.rpow_add hP0]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (4*φ*P^(-((A+10*m+4 : ℕ) : ℝ)))*((2*7^10 : ℝ)*P^(10*m+4)) :=
      mul_le_mul_of_nonneg_left
        (weighted_complete_sum_le F W hW Ω P R B m hP hR hRP hB0 hB) (by positivity)
    _ ≤ (4*1*P^(-((A+10*m+4 : ℕ) : ℝ)))*((2*7^10 : ℝ)*P^(10*m+4)) := by
      gcongr
    _ = (8*7^10 : ℝ)*(P^(-((A+10*m+4 : ℕ) : ℝ))*P^(10*m+4)) := by ring
    _ = _ := by rw [hcancel]

end CubicTenVariables.LocalizedFiniteFrequencyRemainder
