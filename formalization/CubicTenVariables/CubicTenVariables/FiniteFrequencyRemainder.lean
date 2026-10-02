import CubicTenVariables.DyadicFrequencyTruncation

/-! Summation of the localization remainder over the actual dyadic moduli
and nonzero finite frequency cutoff. The bound is elementary and holds for
every integral polynomial, without an oscillatory or arithmetic input. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.FiniteFrequencyRemainder
open MvPolynomial DyadicFrequencyError LocalSupremumWindow LocalSupremumNumerics
open scoped BigOperators

theorem frequency_card_le (P B : ℝ) (m : ℕ) (hP : 1 ≤ P)
    (hB0 : 0 ≤ B) (hB : B ≤ P^m) :
    ((frequencies 10 B).card : ℝ) ≤ (7:ℝ)^10*P^(10*m) := by
  have hPm : 1 ≤ P^m := one_le_pow₀ hP
  have hc := card_le_shifted_real_box (frequencies 10 B) (fun _ => 0) B hB0
    (fun a ha i => by simpa only [sub_zero] using ((mem_frequencies B a).mp ha).2 i)
  calc
    _ ≤ (4*B+3)^10 := hc
    _ ≤ (7*P^m)^10 := pow_le_pow_left₀ (by positivity) (by linarith) 10
    _ = _ := by rw [mul_pow,← pow_mul]; congr 2; omega

/-- The q^-10 weight cancels ten of the eleven trivial powers of q. -/
theorem weighted_modulus_le (F : MvPolynomial (Fin 10) ℤ)
    (q : ℕ) (hq : 1 ≤ q) (B : ℝ) :
    ((q : ℝ)^10)⁻¹*(∑ v ∈ frequencies 10 B, ‖completeCubicSum F q v‖) ≤
      ((frequencies 10 B).card : ℝ)*(q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  calc
    _ ≤ ((q : ℝ)^10)⁻¹*(∑ _v ∈ frequencies 10 B, (q : ℝ)^11) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun v _ => CompleteSumFrequencyTail.trivial_bound F q hq v
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; field_simp

theorem weighted_complete_sum_le (F : MvPolynomial (Fin 10) ℤ)
    (P R B : ℝ) (m : ℕ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hRP : 2*R ≤ P^2) (hB0 : 0 ≤ B) (hB : B ≤ P^m) :
    (∑ q ∈ moduli R, ((q : ℝ)^10)⁻¹*
      ∑ v ∈ frequencies 10 B, ‖completeCubicSum F q v‖) ≤
      (2*7^10 : ℝ)*P^(10*m+4) := by
  have hc := frequency_card_le P B m hP hB0 hB
  have hs : (∑ q ∈ moduli R, (q : ℝ)) ≤ 2*P^4 := by
    apply (DyadicFrequencyTruncation.sum_moduli_le R (P^2) (sq_nonneg P) hRP).trans
    have hP2 : 1 ≤ P^2 := one_le_pow₀ hP
    nlinarith [sq_nonneg (P^2-1)]
  calc
    _ ≤ ∑ q ∈ moduli R, ((frequencies 10 B).card : ℝ)*(q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : (1 : ℝ) ≤ q := hR.trans ((mem_moduli R q).mp hq).1.le
      exact weighted_modulus_le F q (by exact_mod_cast hq1) B
    _ = ((frequencies 10 B).card : ℝ)*(∑ q ∈ moduli R, (q : ℝ)) :=
      (Finset.mul_sum ..).symm
    _ ≤ ((7:ℝ)^10*P^(10*m))*(2*P^4) :=
      mul_le_mul hc hs (Finset.sum_nonneg fun q _ => Nat.cast_nonneg q) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The retained localization order A+10m+4 absorbs every finite frequency
and modulus before leaving the prescribed decay P^-A. -/
theorem bound (F : MvPolynomial (Fin 10) ℤ) (P R φ B : ℝ) (m A : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hRP : 2*R ≤ P^2) (hB0 : 0 ≤ B) (hB : B ≤ P^m) :
    (4*φ*P^(-((A+10*m+4 : ℕ) : ℝ)))*
      (∑ q ∈ moduli R, ((q : ℝ)^10)⁻¹*
        ∑ v ∈ frequencies 10 B, ‖completeCubicSum F q v‖) ≤
      (8*7^10 : ℝ)*P^(-(A : ℝ)) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hcancel : P^(-((A+10*m+4 : ℕ) : ℝ))*P^(10*m+4)=P^(-(A : ℝ)) := by
    rw [← Real.rpow_natCast P (10*m+4),← Real.rpow_add hP0]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (4*φ*P^(-((A+10*m+4 : ℕ) : ℝ)))*((2*7^10 : ℝ)*P^(10*m+4)) :=
      mul_le_mul_of_nonneg_left (weighted_complete_sum_le F P R B m hP hR hRP hB0 hB)
        (by positivity)
    _ ≤ (4*1*P^(-((A+10*m+4 : ℕ) : ℝ)))*((2*7^10 : ℝ)*P^(10*m+4)) := by
      gcongr
    _ = (8*7^10 : ℝ)*(P^(-((A+10*m+4 : ℕ) : ℝ))*P^(10*m+4)) := by ring
    _ = _ := by rw [hcancel]

/-- A fixed polynomial-size cutoff sufficient for all finite remainders.
The inequality even allows nonpositive eta; the application has eta>0. -/
theorem cutoff_le_fifth_power (P R φ η : ℝ) (hP : 1 ≤ P) (hR0 : 0 ≤ R)
    (hR : R ≤ P^2) (hφ : φ ≤ 1) (hη : η ≤ 1) :
    P^η*V P R φ ≤ P^5 := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hP3 : 1 ≤ P^3 := one_le_pow₀ hP
  have hmax : max 1 (φ*P^3) ≤ P^3 := by
    apply max_le hP3
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hφ (pow_nonneg hP0.le 3)
  have hratio : R/P ≤ P := (div_le_iff₀ hP0).mpr (by simpa only [pow_two] using hR)
  have hV : V P R φ ≤ P^4 := by
    calc
      _ ≤ P*P^3 := mul_le_mul hratio hmax (le_max_of_le_left zero_le_one) hP0.le
      _ = _ := by ring
  have hpower : P^η ≤ P := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hη
  calc
    _ ≤ P*P^4 := mul_le_mul hpower hV (by unfold V; positivity) hP0.le
    _ = _ := by ring

end CubicTenVariables.FiniteFrequencyRemainder
