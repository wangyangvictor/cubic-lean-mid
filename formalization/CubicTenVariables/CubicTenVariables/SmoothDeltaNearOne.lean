import CubicTenVariables.SmoothDeltaFourierIdentity
import CubicTenVariables.ModulatedDeltaRiemann
import CubicTenVariables.SmoothDeltaAmplitudeIntegral

/-! Uniform near-one estimates for the actual smooth delta kernel.
The two Riemann errors in the exact centered identity and the proved
normalization bounds give one constant before all varying parameters. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaNearOne
open MeasureTheory SmoothDeltaCutoffs SmoothDeltaKernel SmoothDeltaNormalization
  SmoothDeltaFourierIdentity SmoothDeltaFarDerivative ModulatedDeltaCutoff
open scoped BigOperators FourierTransform

private theorem first_sum_error (N : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ Q q : ℕ, 0 < Q → 1 ≤ q → (q : ℝ)/(Q : ℝ) ≤ 1 →
      |firstSum Q q - (∫ v : ℝ, omega v/v)/((q : ℝ)/(Q : ℝ))| ≤
        C*((q : ℝ)/(Q : ℝ))^N := by
  obtain ⟨C,hC,hb⟩ := exists_riemann_error_real firstProfile firstProfile_contDiff
    firstProfile_hasCompactSupport (N+1)
  refine ⟨C,hC,?_⟩
  intro Q q hQ hq hx1
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  let x : ℝ := (q : ℝ)/(Q : ℝ)
  have hx : 0 < x := div_pos hqR hQR
  have hh := hb x hx hx1
  have he : firstSum Q q = ∑' k : ℤ, firstProfile (x*(k : ℝ)) :=
    (firstProfile_tsum_eq_finite hQ hq).symm
  rw [he]
  have ha : (∑' k : ℤ, firstProfile (x*(k : ℝ))) -
      (∫ v : ℝ, omega v/v)/x =
        (x*(∑' k : ℤ, firstProfile (x*(k : ℝ))) -
          ∫ v : ℝ, firstProfile v)/x := by
    change _ - (∫ v : ℝ, firstProfile v)/x = _
    field_simp
  rw [ha,abs_div,abs_of_pos hx]
  apply (div_le_iff₀ hx).mpr
  simpa only [pow_succ,mul_assoc] using hh

private theorem modulated_integral_bound (t : ℝ) :
    ‖∫ y : ℝ, modulated t y‖ ≤ ∫ y : ℝ, |U y| := by
  simpa only [norm_modulated] using norm_integral_le_integral_norm (modulated t)

private theorem remainder_bound (N : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ x : ℝ, 0 < x → x ≤ 1/2 → ∀ t : ℝ, |t| ≤ 1 →
      ‖∫ v : ℝ, (omega v : ℂ)/((x*v : ℝ) : ℂ) *
        (((x*v : ℝ) : ℂ)*(∑' k : ℤ, modulated t (x*v*(k : ℝ))) -
          ∫ y : ℝ, modulated t y)‖ ≤ C*x^N := by
  obtain ⟨C,hC,hb⟩ := ModulatedDeltaRiemann.exists_bound (N+1)
  refine ⟨C,hC,?_⟩
  intro x hx hxhalf t ht
  have hpoint (v : ℝ) :
      ‖(omega v : ℂ)/((x*v : ℝ) : ℂ) *
        (((x*v : ℝ) : ℂ)*(∑' k : ℤ, modulated t (x*v*(k : ℝ))) -
          ∫ y : ℝ, modulated t y)‖ ≤ (C*x^N)*omega v := by
    by_cases hv : omega v = 0
    · simp [hv]
    have hs : v ∈ Set.Ioo (1/4 : ℝ) 1 := by rwa [← omega_support]
    have hv0 : 0 < v := by linarith [hs.1]
    have hv1 : v ≤ 1 := hs.2.le
    have hxb : 0 < x*v := mul_pos hx hv0
    have hxv : x*v ≤ x := mul_le_of_le_one_right hx.le hv1
    have hh := hb (x*v) hxb (hxv.trans hxhalf) t ht
    rw [norm_mul,norm_div,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (omega_nonneg v),abs_of_pos hxb]
    calc
      _ ≤ (omega v/(x*v)) * (C*(x*v)^(N+1)) :=
        mul_le_mul_of_nonneg_left hh (div_nonneg (omega_nonneg v) hxb.le)
      _ = (C*x^N)*omega v*v^N := by rw [pow_succ,mul_pow]; field_simp
      _ ≤ (C*x^N)*omega v :=
        mul_le_of_le_one_right
          (mul_nonneg (mul_nonneg (zero_le_one.trans hC) (pow_nonneg hx.le N)) (omega_nonneg v))
          (pow_le_one₀ hv0.le hv1)
  calc
    _ ≤ ∫ v : ℝ, (C*x^N)*omega v := by
      apply norm_integral_le_of_norm_le
        (omega_contDiff.continuous.integrable_of_hasCompactSupport omega_hasCompactSupport |>.const_mul (C*x^N))
      exact Filter.Eventually.of_forall hpoint
    _ = _ := by rw [integral_const_mul,omega_integral,mul_one]

private theorem fourier_near_one (N : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ Q : ℕ, 2 ≤ Q → ∀ q : ℕ, 1 ≤ q → (q : ℝ)/(Q : ℝ) ≤ 1/2 →
      ∀ t : ℝ, |t| ≤ 1 → ‖(𝓕 (amplitudeSchwartz Q q)) t - 1‖ ≤
        C*((q : ℝ)/(Q : ℝ))^N := by
  obtain ⟨A,hA,ha⟩ := first_sum_error N
  obtain ⟨B,hB,hb⟩ := remainder_bound N
  let J : ℝ := ∫ y : ℝ, |U y|
  have hJ : 0 ≤ J := integral_nonneg (fun y => abs_nonneg (U y))
  refine ⟨max 1 (A*J+B),le_max_left _ _,?_⟩
  intro Q hQ q hq hxhalf t ht
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  let x : ℝ := (q : ℝ)/(Q : ℝ)
  have hx : 0 < x := div_pos hqR hQR
  rw [centered_identity hQ hq t]
  have herr := ha Q q (by omega) hq (by linarith : (q : ℝ)/(Q : ℝ) ≤ 1)
  have hrem := hb x hx hxhalf t ht
  calc
    _ ≤ ‖((firstSum Q q - (∫ v : ℝ, omega v/v)/x : ℝ) : ℂ) *
          (∫ y : ℝ, modulated t y)‖ +
        ‖∫ v : ℝ, (omega v : ℂ)/((x*v : ℝ) : ℂ) *
          (((x*v : ℝ) : ℂ)*(∑' k : ℤ, modulated t (x*v*(k : ℝ))) -
            ∫ y : ℝ, modulated t y)‖ := norm_sub_le _ _
    _ ≤ (A*x^N)*J+B*x^N := by
      apply add_le_add _ hrem
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul herr (modulated_integral_bound t) (norm_nonneg _) (by positivity)
    _ = (A*J+B)*x^N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hx.le _)

private theorem norm_scaled_sub_one_le (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖(a : ℂ)*z-1‖ ≤ a*‖z-1‖+|a-1| := by
  have he : (a : ℂ)*z-1 = (a : ℂ)*(z-1)+((a : ℂ)-1) := by ring
  rw [he]
  have hh := norm_add_le ((a : ℂ)*(z-1)) ((a : ℂ)-1)
  simpa only [norm_mul,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg ha] using hh

set_option maxHeartbeats 400000 in
/-- The exact near-one clause needed by the delta kernel interface, with
one constant before Q, q and the entire prescribed frequency window. -/
theorem exists_bound (N : ℕ) (_hN : 1 ≤ N) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ Q : ℕ, 2 ≤ Q → ∀ q : ℕ, 1 ≤ q → q ≤ Q → ∀ θ : ℝ,
      |θ| ≤ (Q : ℝ)^(-(2 : ℝ)) →
      ‖p Q q θ-1‖ ≤ C*((q : ℝ)/(Q : ℝ))^N := by
  obtain ⟨A,hA,ha⟩ := fourier_near_one N
  obtain ⟨B,hB,hb⟩ := c_bounded
  obtain ⟨D,hD,hd⟩ := c_error N
  obtain ⟨E,hE,he⟩ := SmoothDeltaAmplitudeIntegral.rapid_decay 0
  let K := max (B*A+D) ((E+1)*(2 : ℝ)^N)
  have hK : 1 ≤ K := by
    have hBA : 1 ≤ B*A := one_le_mul_of_one_le_of_one_le hB hA
    exact (by linarith : 1 ≤ B*A+D).trans (le_max_left _ _)
  refine ⟨K,hK,?_⟩
  intro Q hQ q hq hqQ θ hθ
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let x : ℝ := (q : ℝ)/(Q : ℝ)
  have hx : 0 < x := div_pos (zero_lt_one.trans_le hqR) hQR
  by_cases hxhalf : x ≤ 1/2
  · have ht : |(Q : ℝ)^2*θ| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
      have hh : |θ| ≤ ((Q : ℝ)^2)⁻¹ := by
        simpa only [Real.rpow_neg hQR.le,Real.rpow_two] using hθ
      have hz := mul_le_mul_of_nonneg_left hh (sq_nonneg (Q : ℝ))
      simpa only [mul_inv_cancel₀ (pow_ne_zero _ hQR.ne')] using hz
    have hh := ha Q hQ q hq hxhalf ((Q : ℝ)^2*θ) ht
    have hinv : 1/(Q : ℝ)^N ≤ x^N := by
      dsimp only [x]
      rw [div_pow]
      exact div_le_div_of_nonneg_right (one_le_pow₀ hqR) (pow_nonneg hQR.le _)
    have hcerror : |c Q-1| ≤ D*x^N := by
      apply (hd Q hQ).trans
      calc
        D/(Q : ℝ)^N = D*(1/(Q : ℝ)^N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (zero_le_one.trans hD)
    have hp := norm_scaled_sub_one_le (c Q) (c_pos hQ).le
      ((𝓕 (amplitudeSchwartz Q q)) ((Q : ℝ)^2*θ))
    change ‖p Q q θ-1‖ ≤ _ at hp
    calc
      _ ≤ c Q*‖(𝓕 (amplitudeSchwartz Q q)) ((Q : ℝ)^2*θ)-(1 : ℂ)‖+|c Q-1| := hp
      _ ≤ B*(A*x^N)+D*x^N := by
        apply add_le_add
        · exact mul_le_mul (hb Q hQ) hh (norm_nonneg _) (zero_le_one.trans hB)
        · exact hcerror
      _ = (B*A+D)*x^N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx.le _)
  · have hh : ‖p Q q θ‖ ≤ E := by simpa using he Q hQ q hq hqQ θ
    have hxlow : 1/2 ≤ x := le_of_lt (lt_of_not_ge hxhalf)
    have hpow : 1 ≤ (2 : ℝ)^N*x^N := by
      rw [← mul_pow]
      exact one_le_pow₀ (by linarith)
    calc
      _ ≤ E+1 := by
        have hs : ‖p Q q θ-1‖ ≤ ‖p Q q θ‖+1 := by simpa only [norm_one] using norm_sub_le (p Q q θ) (1 : ℂ)
        linarith
      _ ≤ ((E+1)*(2 : ℝ)^N)*x^N := by
        have hz := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ E+1)
        simpa only [mul_one,mul_assoc] using hz
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hx.le _)

end CubicTenVariables.SmoothDeltaNearOne
