import CubicTenVariables.NonzeroFrequencyNumerics
import CubicTenVariables.LocalSupremumNumerics

/-! Explicit numerical optimization for the ten-variable integral-removal
estimate. The phase-range exponent, the frequency-cutoff exponent, and the
prefactor loss remain distinct. No analytic estimate is an input here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.NonzeroFrequencyPhaseNumerics
open NonzeroFrequencyNumerics LocalSupremumNumerics GradientVolumeNumerics

/-- The low-phase scale never exceeds the chosen cube-root radius. -/
theorem low_scale_le (P R φ : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hRmax : R ≤ P^((3:ℝ)/2)) (hsmall : φ*P^3 ≤ 1) :
    V P R φ ≤ R^((1:ℝ)/3) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  rw [V_small P R φ hsmall]
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  have h := Real.log_le_log hR0 hRmax
  simp (disch := positivity) only [Real.log_div, Real.log_rpow] at h ⊢
  linarith

/-- The integer ceiling contributes a fixed factor at most two. -/
theorem window_factor_le (R : ℝ) (hR : 1 ≤ R) :
    1 + R^((1:ℝ)/3)/(cubeRootWidth R : ℝ) ≤ 2 := by
  have hL := cubeRootWidth_bounds R hR
  have hL0 : (0:ℝ) < (cubeRootWidth R : ℝ) :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hR) _).trans_le hL.1
  have hh : R^((1:ℝ)/3)/(cubeRootWidth R : ℝ) ≤ 1 :=
    (div_le_one hL0).mpr hL.1
  linarith

/-- Low-phase optimization with its exact cutoff loss. -/
theorem low_phase_bound (P R φ b ε w : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (_hw : 0 ≤ w) (hb : b < 20/3)
    (hRmax : R ≤ P^((3:ℝ)/2)) (hsmall : φ*P^3 ≤ 1)
    (hcut : 1 ≤ P^w*V P R φ) :
    φ * R^(b-10) * P^(10+ε) *
      (1 + R^((1:ℝ)/3)/(cubeRootWidth R : ℝ))^10 *
      (V P R φ + (cubeRootWidth R : ℝ))^10 ≤
    (6:ℝ)^10 * P^(7+ε+(20/3-b)*w-saving (20/3-b)) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hV0 : 0 < V P R φ := V_pos P R φ hP0 hR0
  have hsum : V P R φ + (cubeRootWidth R : ℝ) ≤ 3*R^((1:ℝ)/3) := by
    linarith only [low_scale_le P R φ hP hR hRmax hsmall,
      (cubeRootWidth_bounds R hR).2]
  have hraw : φ*R^(b-10)*P^(10+ε)*
      (1+R^((1:ℝ)/3)/(cubeRootWidth R:ℝ))^10*
      (V P R φ+(cubeRootWidth R:ℝ))^10 ≤
      (6:ℝ)^10*(φ*R^(b-10)*P^(10+ε)*(R^((1:ℝ)/3))^10) := by
    calc
      _ ≤ φ*R^(b-10)*P^(10+ε)*2^10*(3*R^((1:ℝ)/3))^10 := by
        gcongr
        · exact window_factor_le R hR
      _ = _ := by ring
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  have hphase := Real.log_le_log (show 0 < φ*P^3 by positivity) hsmall
  have hcutlog := Real.log_le_log (show (0:ℝ)<1 by norm_num) hcut
  rw [V_small P R φ hsmall] at hcutlog
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hs : saving (20/3-b) ≤ 20/3-b := min_le_right _ _
  have hb0 : 0 < 20/3-b := sub_pos.mpr hb
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
    Real.log_rpow, Real.log_one] at hphase hcutlog ⊢
  norm_num at hphase hcutlog ⊢
  nlinarith only [hphase, mul_nonneg hb0.le hcutlog, mul_nonneg (sub_nonneg.mpr hs) hlogP]

/-- Exact logarithm of the high-phase gradient width. -/
theorem log_Vzero_large (P R φ : ℝ) (hP : 0 < P) (hR : 0 < R)
    (hφ : 0 < φ) (hlarge : 1 < φ*P^3) :
    Real.log (Vzero P R φ) = Real.log R + Real.log φ/2 + Real.log P/2 := by
  have hs : 1 ≤ Real.sqrt (φ*P^3) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hlarge.le
  rw [Vzero, max_eq_right hs]
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_sqrt, Real.log_pow]
  norm_num
  ring

/-- The phase upper endpoint bounds the gradient width by a slightly enlarged
cube-root radius; the loss is explicitly 3 eta / 2. -/
theorem high_scale_le (P R φ η : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (hη : 0 ≤ η) (hRmax : R ≤ P^((3:ℝ)/2))
    (hφmax : φ ≤ (R*P^((3:ℝ)/2))^(-1+η)) (hlarge : 1 < φ*P^3) :
    Vzero P R φ ≤ P^((3:ℝ)/2*η)*R^((1:ℝ)/3) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  apply (Real.log_le_log_iff (Vzero_pos P R φ hP0 hR0) (by positivity)).mp
  rw [log_Vzero_large P R φ hP0 hR0 hφ hlarge]
  have hphase := Real.log_le_log hφ hφmax
  have hrange := Real.log_le_log hR0 hRmax
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow] at hphase hrange ⊢
  nlinarith only [hphase,
    mul_nonneg (show 0 ≤ (1:ℝ)/6+η/2 by positivity) (sub_nonneg.mpr hrange)]

/-- The increasing endpoint of the high-phase seventh-power split. -/
theorem high_increasing_term (P R φ b ε η : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (hη : 0 ≤ η) (hRmax : R ≤ P^((3:ℝ)/2))
    (hφmax : φ ≤ (R*P^((3:ℝ)/2))^(-1+η)) (hlarge : 1 < φ*P^3) :
    φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3*
      (Vzero P R φ)^7 ≤
    P^(7+ε+18*η)*R^(-(20/3-b))*(R/P^((3:ℝ)/2))^((1:ℝ)/6) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hZ : 0 < Vzero P R φ := Vzero_pos P R φ hP0 hR0
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  have hphase := Real.log_le_log hφ hφmax
  have hrange := Real.log_le_log hR0 hRmax
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
    Real.log_rpow] at hphase hrange ⊢
  rw [log_Vzero_large P R φ hP0 hR0 hφ hlarge]
  norm_num
  nlinarith only [hphase, mul_nonneg hη (sub_nonneg.mpr hrange)]

/-- The decreasing endpoint uses both the nonempty-frequency cutoff and the
high-phase lower endpoint. -/
theorem high_decreasing_term (P R φ b ε η w : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (hw : 0 ≤ w) (hlarge : 1 < φ*P^3)
    (hcut : 1 ≤ P^w*V P R φ) :
    φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3*
      (R^((1:ℝ)/3)/Real.sqrt (φ*P^3))^7 ≤
    P^(7+ε+(9:ℝ)/2*η+(5:ℝ)/2*w)*R^(-(20/3-b))*(max 1 (P/R))^(-(5:ℝ)/2) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hs : 0 < Real.sqrt (φ*P^3) := by positivity
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hphase := Real.log_le_log (show (0:ℝ)<1 by norm_num) hlarge.le
  have hcutlog := Real.log_le_log (show (0:ℝ)<1 by norm_num) hcut
  rw [V_large P R φ hP0 hlarge] at hcutlog
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  by_cases hPR : P ≤ R
  · rw [max_eq_left ((div_le_one hR0).mpr hPR)]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
      Real.log_rpow, Real.log_sqrt, Real.log_one, Real.one_rpow] at hphase hcutlog ⊢
    norm_num at hphase hcutlog ⊢
    nlinarith only [hphase, mul_nonneg hw hlogP]
  · rw [max_eq_right ((one_le_div hR0).mpr (le_of_not_ge hPR))]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow,
      Real.log_rpow, Real.log_sqrt, Real.log_one] at hphase hcutlog ⊢
    norm_num at hphase hcutlog ⊢
    nlinarith only [hcutlog]

/-- Exact cancellation of the high-phase gradient and frequency scales. -/
theorem high_scale_ratio (P R φ : ℝ) (hP : 0 < P) (hR : 0 < R)
    (hφ : 0 < φ) (hlarge : 1 < φ*P^3) :
    Vzero P R φ / V P R φ = 1 / Real.sqrt (φ*P^3) := by
  have hV := V_pos P R φ hP hR
  have hZ := Vzero_pos P R φ hP hR
  have hs : 0 < Real.sqrt (φ*P^3) := by positivity
  apply Real.log_injOn_pos (div_pos hZ hV) (one_div_pos.mpr hs)
  rw [Real.log_div (ne_of_gt hZ) (ne_of_gt hV),
    log_Vzero_large P R φ hP hR hφ hlarge, V_large P R φ hP hlarge]
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow,
    Real.log_sqrt, Real.log_one]
  norm_num
  ring

/-- The explicit ceiling and additive constants cost only a universal factor.
The two summands are the increasing and decreasing phase endpoints. -/
theorem high_algebra_bound (P R φ b ε η : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (hη : 0 ≤ η) (hRmax : R ≤ P^((3:ℝ)/2))
    (hφmax : φ ≤ (R*P^((3:ℝ)/2))^(-1+η)) (hlarge : 1 < φ*P^3) :
    φ*R^(b-10)*P^(10+ε)*(1+R^((1:ℝ)/3)/(cubeRootWidth R:ℝ))^10*
      (1+(cubeRootWidth R:ℝ)/V P R φ)^7*
      (1+Vzero P R φ+(cubeRootWidth R:ℝ))^3*(Vzero P R φ)^7 ≤
    (2:ℝ)^30*(
      φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3*(Vzero P R φ)^7 +
      φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3*
        (R^((1:ℝ)/3)/Real.sqrt (φ*P^3))^7) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hV : 0 < V P R φ := V_pos P R φ hP0 hR0
  have hZ : 0 < Vzero P R φ := Vzero_pos P R φ hP0 hR0
  have hroot : 1 ≤ R^((1:ℝ)/3) := Real.one_le_rpow hR (by norm_num)
  have hM : 1 ≤ P^((3:ℝ)/2*η) := Real.one_le_rpow hP (by positivity)
  have hMQ : 1 ≤ P^((3:ℝ)/2*η)*R^((1:ℝ)/3) := one_le_mul_of_one_le_of_one_le hM hroot
  have hrootMQ : R^((1:ℝ)/3) ≤ P^((3:ℝ)/2*η)*R^((1:ℝ)/3) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hM
      (show 0 ≤ R^((1:ℝ)/3) by positivity)
  have hcompl : 1+Vzero P R φ+(cubeRootWidth R:ℝ) ≤
      4*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3)) := by
    linarith only [hMQ, hrootMQ, high_scale_le P R φ η hP hR hφ hη hRmax hφmax hlarge,
      (cubeRootWidth_bounds R hR).2]
  have hs : 0 < Real.sqrt (φ*P^3) := by positivity
  have hselected : (1+(cubeRootWidth R:ℝ)/V P R φ)*Vzero P R φ ≤
      2*(Vzero P R φ+R^((1:ℝ)/3)/Real.sqrt (φ*P^3)) := by
    have hratio := high_scale_ratio P R φ hP0 hR0 hφ hlarge
    have he : (1+(cubeRootWidth R:ℝ)/V P R φ)*Vzero P R φ =
        Vzero P R φ+(cubeRootWidth R:ℝ)/Real.sqrt (φ*P^3) := by
      calc
        _ = Vzero P R φ+(cubeRootWidth R:ℝ)*(Vzero P R φ/V P R φ) := by ring
        _ = _ := by rw [hratio]; ring
    rw [he]
    have hh := div_le_div_of_nonneg_right (cubeRootWidth_bounds R hR).2 hs.le
    rw [mul_div_assoc] at hh
    linarith only [hZ, hh]
  have hsplit : (Vzero P R φ+R^((1:ℝ)/3)/Real.sqrt (φ*P^3))^7 ≤
      (2:ℝ)^7*((Vzero P R φ)^7+(R^((1:ℝ)/3)/Real.sqrt (φ*P^3))^7) := by
    have h := add_pow_le hZ.le (show 0 ≤ R^((1:ℝ)/3)/Real.sqrt (φ*P^3) by positivity) 7
    norm_num at h ⊢
    exact h.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  calc
    _ = φ*R^(b-10)*P^(10+ε)*(1+R^((1:ℝ)/3)/(cubeRootWidth R:ℝ))^10*
        (1+Vzero P R φ+(cubeRootWidth R:ℝ))^3*
        ((1+(cubeRootWidth R:ℝ)/V P R φ)*Vzero P R φ)^7 := by ring
    _ ≤ φ*R^(b-10)*P^(10+ε)*2^10*
        (4*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3)))^3*
        (2*(Vzero P R φ+R^((1:ℝ)/3)/Real.sqrt (φ*P^3)))^7 := by
      gcongr
      exact window_factor_le R hR
    _ = (2:ℝ)^23*(φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3)*
        (Vzero P R φ+R^((1:ℝ)/3)/Real.sqrt (φ*P^3))^7 := by ring
    _ ≤ (2:ℝ)^23*(φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3)*
        ((2:ℝ)^7*((Vzero P R φ)^7+(R^((1:ℝ)/3)/Real.sqrt (φ*P^3))^7)) := by
      exact mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = _ := by ring

/-- Full high-phase optimization, with all epsilon losses displayed. -/
theorem high_phase_bound (P R φ b ε η w : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (hη : 0 ≤ η) (hw : 0 ≤ w) (hb : b < 20/3)
    (hRmax : R ≤ P^((3:ℝ)/2))
    (hφmax : φ ≤ (R*P^((3:ℝ)/2))^(-1+η)) (hlarge : 1 < φ*P^3)
    (hcut : 1 ≤ P^w*V P R φ) :
    φ*R^(b-10)*P^(10+ε)*(1+R^((1:ℝ)/3)/(cubeRootWidth R:ℝ))^10*
      (1+(cubeRootWidth R:ℝ)/V P R φ)^7*
      (1+Vzero P R φ+(cubeRootWidth R:ℝ))^3*(Vzero P R φ)^7 ≤
    (2:ℝ)^31*P^(7+ε+18*η+(5:ℝ)/2*w-saving (20/3-b)) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have ha := high_increasing_term P R φ b ε η hP hR hφ hη hRmax hφmax hlarge
  have hb' := high_decreasing_term P R φ b ε η w hP hR hφ hw hlarge hcut
  have ha' : φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3*(Vzero P R φ)^7 ≤
      P^(7+ε+18*η+(5:ℝ)/2*w)*R^(-(20/3-b))*(R/P^((3:ℝ)/2))^((1:ℝ)/6) := by
    apply ha.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hP (by linarith only [hw])
  have hb'' : φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3*
      (R^((1:ℝ)/3)/Real.sqrt (φ*P^3))^7 ≤
      P^(7+ε+18*η+(5:ℝ)/2*w)*R^(-(20/3-b))*(max 1 (P/R))^(-(5:ℝ)/2) := by
    apply hb'.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hP (by linarith only [hη])
  have hsaving := radial_saving P R (20/3-b) hP hR hRmax (sub_pos.mpr hb)
  calc
    _ ≤ (2:ℝ)^30*(
      φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3*(Vzero P R φ)^7 +
      φ*R^(b-10)*P^(10+ε)*(P^((3:ℝ)/2*η)*R^((1:ℝ)/3))^3*
        (R^((1:ℝ)/3)/Real.sqrt (φ*P^3))^7) :=
      high_algebra_bound P R φ b ε η hP hR hφ hη hRmax hφmax hlarge
    _ ≤ (2:ℝ)^30*(
      P^(7+ε+18*η+(5:ℝ)/2*w)*R^(-(20/3-b))*(R/P^((3:ℝ)/2))^((1:ℝ)/6) +
      P^(7+ε+18*η+(5:ℝ)/2*w)*R^(-(20/3-b))*(max 1 (P/R))^(-(5:ℝ)/2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add ha' hb'') (by positivity)
    _ = (2:ℝ)^30*P^(7+ε+18*η+(5:ℝ)/2*w)*
      (R^(-(20/3-b))*((R/P^((3:ℝ)/2))^((1:ℝ)/6)+(max 1 (P/R))^(-(5:ℝ)/2))) := by ring
    _ ≤ (2:ℝ)^30*P^(7+ε+18*η+(5:ℝ)/2*w)*(2*P^(-saving (20/3-b))) := by
      exact mul_le_mul_of_nonneg_left hsaving (by positivity)
    _ = _ := by
      calc
        _ = (2:ℝ)^31*(P^(7+ε+18*η+(5:ℝ)/2*w)*P^(-saving (20/3-b))) := by ring
        _ = _ := by rw [← Real.rpow_add hP0]; simp only [sub_eq_add_neg]

/-- A single uniform optimization theorem for the literal two-case volume
factor. The conservative total loss is epsilon + 18 eta + (beta+5/2) w,
where beta=20/3-b>0, and w is the frequency-cutoff exponent. -/
theorem optimized_bound (P R φ b ε η w : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (hη : 0 ≤ η) (hw : 0 ≤ w) (hb : b < 20/3)
    (hRmax : R ≤ P^((3:ℝ)/2))
    (hφmax : φ ≤ (R*P^((3:ℝ)/2))^(-1+η)) (hcut : 1 ≤ P^w*V P R φ) :
    φ*R^(b-10)*P^(10+ε)*(1+R^((1:ℝ)/3)/(cubeRootWidth R:ℝ))^10*
      (if 1 < φ*P^3 then
        (1+(cubeRootWidth R:ℝ)/V P R φ)^7*
        (1+Vzero P R φ+(cubeRootWidth R:ℝ))^3*(Vzero P R φ)^7
       else (V P R φ+(cubeRootWidth R:ℝ))^10) ≤
    (2:ℝ)^31*P^(7+ε+18*η+((20/3-b)+(5:ℝ)/2)*w-saving (20/3-b)) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hβ : 0 < 20/3-b := sub_pos.mpr hb
  by_cases hlarge : 1 < φ*P^3
  · rw [if_pos hlarge]
    have hh := high_phase_bound P R φ b ε η w hP hR hφ hη hw hb hRmax hφmax hlarge hcut
    have hh' : φ*R^(b-10)*P^(10+ε)*(1+R^((1:ℝ)/3)/(cubeRootWidth R:ℝ))^10*
        ((1+(cubeRootWidth R:ℝ)/V P R φ)^7*
          (1+Vzero P R φ+(cubeRootWidth R:ℝ))^3*(Vzero P R φ)^7) ≤
        (2:ℝ)^31*P^(7+ε+18*η+(5:ℝ)/2*w-saving (20/3-b)) := by
      simpa only [mul_assoc] using hh
    apply hh'.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hP (by nlinarith only [mul_nonneg hβ.le hw])
  · rw [if_neg hlarge]
    apply (low_phase_bound P R φ b ε w hP hR hφ hw hb hRmax (le_of_not_gt hlarge) hcut).trans
    apply mul_le_mul (show (6:ℝ)^10 ≤ (2:ℝ)^31 by norm_num) _ (by positivity) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hP (by nlinarith only [hη, hw])

end CubicTenVariables.NonzeroFrequencyPhaseNumerics
