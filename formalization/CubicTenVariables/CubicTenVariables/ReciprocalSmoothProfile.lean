import CubicTenVariables.SmoothDeltaCutoffs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Fixed reciprocal profiles for the smooth delta kernel. These smooth
compactly supported functions allow Poisson summation to be applied separately
to each finite derivative, without differentiating an infinite Fourier sum. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ReciprocalSmoothProfile
open MeasureTheory Set SmoothDeltaCutoffs
open scoped ContDiff Topology

/-- The reciprocal profile, with ordinary total inversion at zero. -/
def profile (j : ℕ) (v : ℝ) : ℝ :=
  (v⁻¹)^(j+1) * iteratedDeriv j omega v⁻¹

theorem omega_deriv_contDiff (j : ℕ) : ContDiff ℝ ∞ (iteratedDeriv j omega) := by
  induction j with
  | zero => simpa using omega_contDiff
  | succ j ih =>
      rw [iteratedDeriv_succ]
      apply ContDiff.deriv'
      simpa using ih

theorem omega_deriv_hasCompactSupport (j : ℕ) :
    HasCompactSupport (iteratedDeriv j omega) := by
  induction j with
  | zero => simpa using omega_hasCompactSupport
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem omega_deriv_eq_zero (j : ℕ) {v : ℝ}
    (hv : v ∉ Icc (1/4 : ℝ) 1) : iteratedDeriv j omega v = 0 := by
  have h : v ∉ tsupport omega := by rwa [omega_tsupport]
  have hz : iteratedFDeriv ℝ j omega v = 0 :=
    Function.notMem_support.mp (fun hh => h (support_iteratedFDeriv_subset j hh))
  simp [iteratedDeriv,hz]

theorem profile_eq_zero (j : ℕ) {v : ℝ} (hv : v ∉ Icc (1 : ℝ) 4) :
    profile j v = 0 := by
  have h : v⁻¹ ∉ Icc (1/4 : ℝ) 1 := by
    intro hi
    have hvi : 0 < v⁻¹ := lt_of_lt_of_le (by norm_num) hi.1
    have hvp : 0 < v := inv_pos.mp hvi
    have h1 := mul_le_mul_of_nonneg_right hi.1 hvp.le
    have h2 := mul_le_mul_of_nonneg_right hi.2 hvp.le
    rw [inv_mul_cancel₀ hvp.ne'] at h1 h2
    apply hv
    constructor <;> nlinarith
  simp [profile,omega_deriv_eq_zero j h]

theorem profile_tsupport (j : ℕ) : tsupport (profile j) ⊆ Icc (1 : ℝ) 4 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  by_contra h
  exact hv (profile_eq_zero j h)

theorem profile_hasCompactSupport (j : ℕ) : HasCompactSupport (profile j) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (profile_tsupport j)

theorem profile_contDiff (j : ℕ) : ContDiff ℝ ∞ (profile j) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst v
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
    exact profile_eq_zero j (by
      have hx' : x < 1 := hx
      simp only [mem_Icc,not_and]
      intro h
      linarith)
  · exact ((contDiffAt_id.inv hv).pow (j+1)).mul
      ((omega_deriv_contDiff j).contDiffAt.comp v (contDiffAt_id.inv hv))

theorem profile_integrable (j : ℕ) : Integrable (profile j) :=
  (profile_contDiff j).continuous.integrable_of_hasCompactSupport (profile_hasCompactSupport j)

private theorem moment_integrable (k j : ℕ) :
    Integrable (fun x : ℝ => x^k * iteratedDeriv j omega x) :=
  (continuous_pow k |>.mul (omega_deriv_contDiff j).continuous).integrable_of_hasCompactSupport
    ((omega_deriv_hasCompactSupport j).mul_left)

private theorem moment_succ (k j : ℕ) :
    (∫ x : ℝ, x^k * iteratedDeriv (j+1) omega x) =
      -(k : ℝ) * ∫ x : ℝ, x^(k-1) * iteratedDeriv j omega x := by
  have hv (x : ℝ) : HasDerivAt (iteratedDeriv j omega)
      (iteratedDeriv (j+1) omega x) x := by
    rw [iteratedDeriv_succ]
    exact ((omega_deriv_contDiff j).differentiable (by simp) x).hasDerivAt
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x : ℝ => hasDerivAt_pow k x) hv
    (moment_integrable k (j+1))
    (by
      change Integrable (fun x : ℝ => ((k : ℝ)*x^(k-1))*iteratedDeriv j omega x)
      simpa only [mul_assoc] using (moment_integrable (k-1) j).const_mul (k : ℝ))
    (moment_integrable k j)
  simpa only [Pi.mul_apply,mul_assoc,integral_const_mul,neg_mul] using h

private theorem moment_zero (k j : ℕ) (hkj : k < j) :
    (∫ x : ℝ, x^k * iteratedDeriv j omega x) = 0 := by
  induction k generalizing j with
  | zero =>
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      rw [moment_succ]
      simp
  | succ k ih =>
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      rw [moment_succ]
      simp only [Nat.add_sub_cancel]
      rw [ih j (by omega),mul_zero]

private theorem integral_inv_sq (f : ℝ → ℝ) :
    (∫ v in Ioi (0 : ℝ), (v⁻¹)^2 * f v⁻¹) = ∫ v in Ioi (0 : ℝ), f v := by
  have h := integral_comp_rpow_Ioi f (by norm_num : (-1 : ℝ) ≠ 0)
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  norm_num only [abs_neg,abs_one,one_mul,neg_sub,smul_eq_mul,
    Real.rpow_neg_one,Real.rpow_neg (le_of_lt hv),Real.rpow_two,Real.rpow_one,pow_one]
  ring

theorem integral_profile_succ (j : ℕ) : ∫ v, profile (j+1) v = 0 := by
  have h := integral_inv_sq (fun v : ℝ => v^j * iteratedDeriv (j+1) omega v)
  have hl : (∫ v in Ioi (0 : ℝ), (v⁻¹)^2 *
      ((v⁻¹)^j * iteratedDeriv (j+1) omega v⁻¹)) = ∫ v, profile (j+1) v := by
    have he : (fun v : ℝ => (v⁻¹)^2 *
        ((v⁻¹)^j * iteratedDeriv (j+1) omega v⁻¹)) = profile (j+1) := by
      funext v
      simp only [profile,pow_add,pow_one]
      ring
    rw [he]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    apply profile_eq_zero
    simp only [mem_Ioi,not_lt] at hv
    simp only [mem_Icc,not_and]
    intro hh
    linarith
  have hr : (∫ v in Ioi (0 : ℝ), v^j * iteratedDeriv (j+1) omega v) =
      ∫ v : ℝ, v^j * iteratedDeriv (j+1) omega v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [omega_deriv_eq_zero]
    · simp
    · simp only [mem_Ioi,not_lt] at hv
      simp only [mem_Icc,not_and]
      intro hh
      linarith
  rw [hl,hr,moment_zero j (j+1) (by omega)] at h
  exact h

/-- Every positive-order reciprocal profile has zero integral. -/
theorem integral_profile_eq_zero (j : ℕ) (hj : 1 ≤ j) : ∫ v, profile j v = 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact integral_profile_succ k

theorem integral_profile_zero : (∫ v, profile 0 v) = ∫ v : ℝ, omega v / v := by
  have h := integral_inv_sq (fun v : ℝ => omega v / v)
  have hl : (∫ v in Ioi (0 : ℝ), (v⁻¹)^2 * (omega v⁻¹ / v⁻¹)) =
      ∫ v, profile 0 v := by
    calc
      _ = ∫ v in Ioi (0 : ℝ), profile 0 v := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        simp only [profile,zero_add,pow_one,iteratedDeriv_zero]
        field_simp
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => by
        apply profile_eq_zero
        simp only [mem_Ioi,not_lt] at hv
        simp only [mem_Icc,not_and]
        intro hh
        linarith)
  have hr : (∫ v in Ioi (0 : ℝ), omega v / v) = ∫ v : ℝ, omega v / v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hz := omega_deriv_eq_zero 0 (v := v) (by
      simp only [mem_Ioi,not_lt] at hv
      simp only [mem_Icc,not_and]
      intro hh
      linarith)
    simp only [iteratedDeriv_zero] at hz
    simp [hz]
  rwa [hl,hr] at h

end CubicTenVariables.ReciprocalSmoothProfile
