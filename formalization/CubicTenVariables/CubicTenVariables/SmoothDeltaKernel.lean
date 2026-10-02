import CubicTenVariables.SmoothDeltaCutoffs
import CubicTenVariables.DeltaMethod
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The concrete finite smooth delta kernel and its exact Fourier identity.
No uniform size, approximate-identity, or rapid-decay estimate is assumed or
asserted here. The finite real amplitude becomes an actual Schwartz function;
Fourier inversion and the scalar Jacobian provide the literal phase integral. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaKernel
open MeasureTheory SmoothDeltaCutoffs DeltaMethod
open scoped BigOperators ContDiff FourierTransform SchwartzMap

/-- A smooth even extension, avoiding differentiation of absolute value. -/
def Omega (y : ℝ) : ℝ := omega y + omega (-y)

theorem Omega_contDiff : ContDiff ℝ ∞ Omega :=
  omega_contDiff.add (omega_contDiff.comp contDiff_neg)

theorem Omega_eq_abs (y : ℝ) : Omega y = omega |y| := by
  have hz (z : ℝ) (hz : z ≤ 0) : omega z = 0 := by
    by_contra hn
    have hs : z ∈ Function.support omega := hn
    rw [omega_support] at hs
    linarith [hs.1]
  by_cases hy : 0 ≤ y
  · simp [Omega,abs_of_nonneg hy,hz (-y) (neg_nonpos.mpr hy)]
  · have hy' : y ≤ 0 := le_of_not_ge hy
    simp [Omega,abs_of_nonpos hy',hz y hy']

/-- The finite divisor-switch amplitude before imposing its small real support. -/
def h (Q q : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 Q, (Q : ℝ)/((q : ℝ)*(j : ℝ)) *
    (omega (((q : ℝ)*(j : ℝ))/(Q : ℝ)) -
      Omega (y*(Q : ℝ)/((q : ℝ)*(j : ℝ))))

/-- The compactly supported real amplitude. -/
def g (Q q : ℕ) (y : ℝ) : ℝ := U y * h Q q y

theorem h_contDiff (Q q : ℕ) : ContDiff ℝ ∞ (h Q q) := by
  unfold h
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul (contDiff_const.sub
    (Omega_contDiff.comp ((contDiff_id.mul contDiff_const).div_const _)))

theorem g_contDiff (Q q : ℕ) : ContDiff ℝ ∞ (g Q q) :=
  U_contDiff.mul (h_contDiff Q q)

theorem g_hasCompactSupport (Q q : ℕ) : HasCompactSupport (g Q q) :=
  U_hasCompactSupport.mul_right

theorem g_tsupport_subset (Q q : ℕ) :
    tsupport (g Q q) ⊆ Set.Icc (-(1/4) : ℝ) (1/4) := by
  rw [← U_tsupport]
  exact tsupport_mul_subset_left (f := U) (g := h Q q)

/-- The literal complex-valued amplitude, without a change of measure. -/
def amplitude (Q q : ℕ) (y : ℝ) : ℂ := (g Q q y : ℂ)

theorem amplitude_contDiff (Q q : ℕ) : ContDiff ℝ ∞ (amplitude Q q) :=
  Complex.ofRealCLM.contDiff.comp (g_contDiff Q q)

theorem amplitude_hasCompactSupport (Q q : ℕ) : HasCompactSupport (amplitude Q q) :=
  (g_hasCompactSupport Q q).comp_left (by simp)

/-- The Schwartz packaging has exactly the finite amplitude as its value. -/
def amplitudeSchwartz (Q q : ℕ) : 𝓢(ℝ,ℂ) :=
  (amplitude_hasCompactSupport Q q).toSchwartzMap (amplitude_contDiff Q q)

@[simp] theorem amplitudeSchwartz_apply (Q q : ℕ) (y : ℝ) :
    amplitudeSchwartz Q q y = (g Q q y : ℂ) := rfl

/-- The normalization is positive for every natural `Q≥2`. -/
def c (Q : ℕ) : ℝ := (normalizer Q)⁻¹

theorem c_pos {Q : ℕ} (hQ : 2 ≤ Q) : 0 < c Q :=
  inv_pos.mpr (normalizer_pos hQ)

/-- The actual kernel with the negative-sign Fourier transform. -/
def p (Q q : ℕ) (θ : ℝ) : ℂ :=
  (c Q : ℂ) * (𝓕 (amplitudeSchwartz Q q)) ((Q : ℝ)^2 * θ)

theorem p_contDiff (Q q : ℕ) : ContDiff ℝ ∞ (p Q q) :=
  contDiff_const.mul (((𝓕 (amplitudeSchwartz Q q)).smooth (⊤ : ℕ∞)).comp
    (contDiff_const.mul contDiff_id))

theorem p_integrable {Q : ℕ} (hQ : 2 ≤ Q) (q : ℕ) : Integrable (p Q q) := by
  have hQ0 : (Q : ℝ)^2 ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (show Q ≠ 0 by omega))
  exact ((𝓕 (amplitudeSchwartz Q q)).integrable.comp_mul_left' hQ0).const_mul _

/-- Every phase integral is absolutely integrable, for arbitrary real phase. -/
theorem p_phase_integrable {Q : ℕ} (hQ : 2 ≤ Q) (q : ℕ) (m : ℝ) :
    Integrable (fun θ : ℝ => p Q q θ * realExponential (θ*m)) := by
  have he : Continuous (fun θ : ℝ => realExponential (θ*m)) := by
    unfold realExponential
    fun_prop
  refine (p_integrable hQ q).norm.mono'
    ((p_contDiff Q q).continuous.mul he).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun θ => by
    simp only [norm_mul,norm_realExponential,mul_one,le_refl])

/-- Fourier inversion in the project's positive-sign real exponential convention. -/
theorem fourier_phase_integral (Q q : ℕ) (y : ℝ) :
    (∫ t : ℝ, (𝓕 (amplitudeSchwartz Q q)) t * realExponential (t*y)) =
      (g Q q y : ℂ) := by
  let f := amplitudeSchwartz Q q
  have hi : 𝓕⁻ (𝓕 (f : ℝ → ℂ)) y = f y :=
    f.integrable.fourierInv_fourier_eq (𝓕 f).integrable f.continuous.continuousAt
  rw [Real.fourierInv_eq'] at hi
  have he (t : ℝ) :
      Complex.exp ((↑(2 * Real.pi * inner ℝ t y) : ℂ) * Complex.I) • (𝓕 f) t =
        (𝓕 f) t * realExponential (t*y) := by
    rw [smul_eq_mul]
    unfold realExponential
    have hex : ((↑(2 * Real.pi * inner ℝ t y) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * Complex.I * ((t*y : ℝ) : ℂ) := by
      change ((↑(2 * Real.pi * (y*t)) : ℂ) * Complex.I) = _
      push_cast
      ring
    rw [hex,mul_comm]
  change (∫ t : ℝ, Complex.exp ((↑(2 * Real.pi * inner ℝ t y) : ℂ) * Complex.I) •
    (𝓕 f) t) = f y at hi
  simpa only [he, f, amplitudeSchwartz_apply] using hi

/-- The `Q²` frequency dilation contributes exactly the reciprocal Jacobian. -/
theorem integral_phase {Q : ℕ} (hQ : 2 ≤ Q) (q : ℕ) (m : ℝ) :
    (∫ θ : ℝ, p Q q θ * realExponential (θ*m)) =
      ((c Q : ℂ)/(Q : ℂ)^2) * (g Q q (m/(Q : ℝ)^2) : ℂ) := by
  have hQ0 : 0 < (Q : ℝ)^2 := by
    exact pow_pos (by exact_mod_cast (show 0 < Q by omega)) _
  let J : ℝ → ℂ := fun t => (𝓕 (amplitudeSchwartz Q q)) t *
    realExponential (t*(m/(Q : ℝ)^2))
  have he (θ : ℝ) : p Q q θ * realExponential (θ*m) =
      (c Q : ℂ) * J ((Q : ℝ)^2 * θ) := by
    have hp : (Q : ℝ)^2 * θ * (m/(Q : ℝ)^2) = θ*m := by field_simp
    simp only [p,J,hp]
    ring
  simp_rw [he]
  rw [integral_const_mul,Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr hQ0)]
  have hi : (∫ t : ℝ, J t) = (g Q q (m/(Q : ℝ)^2) : ℂ) :=
    fourier_phase_integral Q q _
  rw [hi,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_natCast]
  ring

theorem integral_integer_phase {Q : ℕ} (hQ : 2 ≤ Q) (q : ℕ) (m : ℤ) :
    (∫ θ : ℝ, p Q q θ * realExponential (θ*(m : ℝ))) =
      ((c Q : ℂ)/(Q : ℂ)^2) * (g Q q ((m : ℝ)/(Q : ℝ)^2) : ℂ) :=
  integral_phase hQ q m

end CubicTenVariables.SmoothDeltaKernel
