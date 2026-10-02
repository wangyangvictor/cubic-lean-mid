import CubicTenVariables.ModulatedDeltaCutoff
import CubicTenVariables.SmoothDeltaFarDerivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Exact Fourier identity for the finite smooth delta amplitude. All changes
of variables and interchanges below involve finite sums; the whole-lattice
sum is identified pointwise on the fixed omega support. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaFourierIdentity
open MeasureTheory SmoothDeltaCutoffs SmoothDeltaKernel ModulatedDeltaCutoff
open scoped BigOperators ContDiff FourierTransform

/-- The constant first part of the finite delta amplitude. -/
def firstSum (Q q : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 Q, (Q : ℝ)/((q : ℝ)*(j : ℝ)) *
    omega (((q : ℝ)*(j : ℝ))/(Q : ℝ))

private theorem modulated_eq_zero (t z : ℝ) (hz : 1/4 ≤ |z|) : modulated t z=0 := by
  have hu : U z=0 := by
    apply Function.notMem_support.mp
    rw [U_support]
    intro hh
    have ha : |z|<1/4 := abs_lt.mpr hh
    linarith
  simp [modulated,hu]

private theorem int_sum_finite (f : ℤ → ℂ) (Q : ℕ)
    (hz : ∀ k : ℕ, Q<k → f k=0 ∧ f (-(k : ℤ))=0) :
    (∑' k : ℤ,f k)=f 0 + ∑ j ∈ Finset.Icc 1 Q, (f j+f (-(j : ℤ))) := by
  classical
  have hp : HasSum (fun k : ℕ => f (k : ℤ)) (∑ k ∈ Finset.Icc 0 Q,f (k : ℤ)) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => (hz k (by simpa using hk)).1)
  have hn : HasSum (fun k : ℕ => f (-(k : ℤ))) (∑ k ∈ Finset.Icc 0 Q,f (-(k : ℤ))) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => (hz k (by simpa using hk)).2)
  have hh := hp.of_nat_of_neg hn
  have hs : Finset.Icc 0 Q=insert 0 (Finset.Icc 1 Q) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have h0 : 0∉Finset.Icc 1 Q := by simp
  rw [hh.tsum_eq,hs,Finset.sum_insert h0,Finset.sum_insert h0]
  simp only [Nat.cast_zero,neg_zero,Finset.sum_add_distrib]
  ring

/-- Under the omega weight, the whole integer lattice has exactly the
finitely many terms already present in the amplitude, plus its zero term. -/
theorem weighted_lattice_sum_eq {Q q : ℕ} (hQ : 0<Q) (hq : 1≤q) (t v : ℝ) :
    (omega v : ℂ)*(∑' k : ℤ,modulated t (((q : ℝ)/(Q : ℝ))*v*(k : ℝ))) =
      (omega v : ℂ)*(1+∑ j ∈ Finset.Icc 1 Q,
        (modulated t (((q : ℝ)/(Q : ℝ))*(j : ℝ)*v) +
         modulated t (-(((q : ℝ)/(Q : ℝ))*(j : ℝ)*v)))) := by
  by_cases hv : omega v=0
  · simp [hv]
  have hvs : v ∈ Set.Ioo (1/4 : ℝ) 1 := by
    rw [← omega_support]
    exact hv
  have hQr : 0<(Q : ℝ) := by exact_mod_cast hQ
  have hqr : (1 : ℝ)≤q := by exact_mod_cast hq
  have hqp : 0<(q : ℝ) := zero_lt_one.trans_le hqr
  let f : ℤ → ℂ := fun k => modulated t (((q : ℝ)/(Q : ℝ))*v*(k : ℝ))
  have hz (k : ℕ) (hk : Q<k) : f k=0 ∧ f (-(k : ℤ))=0 := by
    have hkr : (Q : ℝ)<k := by exact_mod_cast hk
    have hkp : 0<(k : ℝ) := hQr.trans hkr
    have hxk : 1≤((q : ℝ)/(Q : ℝ))*(k : ℝ) := by
      rw [div_mul_eq_mul_div]
      apply (one_le_div hQr).mpr
      nlinarith
    have hpoint : 1/4≤((q : ℝ)/(Q : ℝ))*v*(k : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hxk (show 0≤v by linarith [hvs.1])
      nlinarith [hvs.1]
    constructor
    · apply modulated_eq_zero
      exact hpoint.trans (le_abs_self _)
    · dsimp only [f]
      simp only [Int.cast_neg,Int.cast_natCast]
      apply modulated_eq_zero
      simpa only [mul_neg,abs_neg] using hpoint.trans (le_abs_self _)
  have hh := int_sum_finite f Q hz
  have he (j : ℕ) : f j+f (-(j : ℤ)) =
      modulated t (((q : ℝ)/(Q : ℝ))*(j : ℝ)*v) +
      modulated t (-(((q : ℝ)/(Q : ℝ))*(j : ℝ)*v)) := by
    simp only [f,Int.cast_natCast,Int.cast_neg,mul_neg]
    congr 2 <;> ring
  simp_rw [he] at hh
  have hf0 : f 0=1 := by simp [f]
  rw [hf0] at hh
  rw [hh]

private theorem modulated_integrable (t : ℝ) : Integrable (modulated t) :=
  (modulated_contDiff t).continuous.integrable_of_hasCompactSupport
    (modulated_hasCompactSupport t)

private theorem omega_times_continuous_integrable (F : ℝ → ℂ) (hF : Continuous F) :
    Integrable (fun v : ℝ => (omega v : ℂ)*F v) := by
  have hc : HasCompactSupport (fun v : ℝ => (omega v : ℂ)*F v) :=
    (omega_hasCompactSupport.comp_left (g := fun v : ℝ => (v : ℂ)) (by simp)).mul_right
  exact ((Complex.continuous_ofReal.comp omega_contDiff.continuous).mul hF).integrable_of_hasCompactSupport hc

private theorem modulated_times_omega_integrable (t b : ℝ) :
    Integrable (fun y : ℝ => modulated t y*(omega (b*y) : ℂ)) := by
  apply ((modulated_contDiff t).continuous.mul
    (Complex.continuous_ofReal.comp (omega_contDiff.continuous.comp
      (continuous_const.mul continuous_id)))).integrable_of_hasCompactSupport
  exact (modulated_hasCompactSupport t).mul_right

/-- A positive scalar change of variables for both halves of the even omega. -/
theorem scaled_Omega_integral (t a : ℝ) (ha : 0<a) :
    (∫ y : ℝ, modulated t y * ((a⁻¹*Omega (y/a) : ℝ) : ℂ)) =
      ∫ v : ℝ, (omega v : ℂ)*(modulated t (a*v)+modulated t (-(a*v))) := by
  have hpos : (∫ v : ℝ,(omega v : ℂ)*modulated t (a*v)) =
      (a : ℂ)⁻¹ * ∫ y : ℝ,modulated t y*(omega (y/a) : ℂ) := by
    have hi := Measure.integral_comp_mul_left
      (fun y : ℝ => modulated t y*(omega (y/a) : ℂ)) a
    simp only [abs_of_pos (inv_pos.mpr ha),Complex.real_smul,Complex.ofReal_inv] at hi
    convert hi using 1
    apply integral_congr_ae
    filter_upwards [] with v
    rw [mul_div_cancel_left₀ v ha.ne',mul_comm]
  have hneg : (∫ v : ℝ,(omega v : ℂ)*modulated t (-(a*v))) =
      (a : ℂ)⁻¹ * ∫ y : ℝ,modulated t y*(omega (-(y/a)) : ℂ) := by
    have hi := Measure.integral_comp_mul_left
      (fun y : ℝ => modulated t y*(omega (-(y/a)) : ℂ)) (-a)
    simp only [inv_neg,abs_neg,abs_of_pos (inv_pos.mpr ha),Complex.real_smul,Complex.ofReal_inv] at hi
    convert hi using 1
    apply integral_congr_ae
    filter_upwards [] with v
    have he : -((-a)*v/a)=v := by field_simp
    rw [he,neg_mul,mul_comm]
  have hp : Integrable (fun y : ℝ => modulated t y*(omega (y/a) : ℂ)) := by
    simpa only [div_eq_mul_inv,mul_comm] using modulated_times_omega_integrable t a⁻¹
  have hn : Integrable (fun y : ℝ => modulated t y*(omega (-(y/a)) : ℂ)) := by
    convert modulated_times_omega_integrable t (-a⁻¹) using 1
    funext y
    congr 2
    ring
  have hrp := omega_times_continuous_integrable (fun v => modulated t (a*v))
    ((modulated_contDiff t).continuous.comp (continuous_const.mul continuous_id))
  have hrn := omega_times_continuous_integrable (fun v => modulated t (-(a*v)))
    ((modulated_contDiff t).continuous.comp (continuous_const.mul continuous_id).neg)
  simp_rw [mul_add]
  rw [integral_add hrp hrn,hpos,hneg,← mul_add,← integral_add hp hn]
  simp only [Omega,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_inv]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring



private def finiteSamples (Q q : ℕ) (t v : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 Q,
    (modulated t (((q : ℝ)/(Q : ℝ))*(j : ℝ)*v) +
     modulated t (-(((q : ℝ)/(Q : ℝ))*(j : ℝ)*v)))

private theorem finiteSamples_continuous (Q q : ℕ) (t : ℝ) :
    Continuous (finiteSamples Q q t) := by
  apply continuous_finset_sum
  intro j hj
  apply Continuous.add
  · exact (modulated_contDiff t).continuous.comp (continuous_const.mul continuous_id)
  · exact (modulated_contDiff t).continuous.comp (continuous_const.mul continuous_id).neg

private theorem finiteSamples_integrable (Q q : ℕ) (t : ℝ) :
    Integrable (fun v : ℝ => (omega v : ℂ)*finiteSamples Q q t v) :=
  omega_times_continuous_integrable _ (finiteSamples_continuous Q q t)

private theorem omegaComplex_integrable : Integrable (fun v : ℝ => (omega v : ℂ)) := by
  exact (omega_contDiff.continuous.integrable_of_hasCompactSupport omega_hasCompactSupport).ofReal

/-- The infinite notation in the integral is exactly a finite smooth compact
function after multiplication by omega. -/
theorem weighted_lattice_integrable {Q q : ℕ} (hQ : 0<Q) (hq : 1≤q) (t : ℝ) :
    Integrable (fun v : ℝ => (omega v : ℂ)*
      (∑' k : ℤ,modulated t (((q : ℝ)/(Q : ℝ))*v*(k : ℝ)))) := by
  have he : (fun v : ℝ => (omega v : ℂ)*
      (∑' k : ℤ,modulated t (((q : ℝ)/(Q : ℝ))*v*(k : ℝ)))) =
      fun v : ℝ => (omega v : ℂ)+(omega v : ℂ)*finiteSamples Q q t v := by
    funext v
    rw [weighted_lattice_sum_eq hQ hq]
    simp only [finiteSamples,mul_add,mul_one]
  rw [he]
  exact omegaComplex_integrable.add (finiteSamples_integrable Q q t)

private theorem weighted_lattice_integral {Q q : ℕ} (hQ : 0<Q) (hq : 1≤q) (t : ℝ) :
    (∫ v : ℝ, (omega v : ℂ)*
      (∑' k : ℤ,modulated t (((q : ℝ)/(Q : ℝ))*v*(k : ℝ)))) =
      1+∫ v : ℝ,(omega v : ℂ)*finiteSamples Q q t v := by
  simp_rw [weighted_lattice_sum_eq hQ hq,mul_add,mul_one]
  change (∫ v : ℝ,(omega v : ℂ)+(omega v : ℂ)*finiteSamples Q q t v)=_
  rw [integral_add omegaComplex_integrable (finiteSamples_integrable Q q t),
    integral_complex_ofReal,omega_integral,Complex.ofReal_one]

private theorem fourier_as_integral (Q q : ℕ) (t : ℝ) :
    (𝓕 (amplitudeSchwartz Q q)) t =
      ∫ y : ℝ, modulated t y*(h Q q y : ℂ) := by
  change 𝓕 (amplitude Q q) t = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_eq_mul,amplitude,g,Complex.ofReal_mul,modulated]
  have he : Complex.ofReal (-2*Real.pi*y*t)*Complex.I =
      -2*(Real.pi : ℂ)*Complex.I*Complex.ofReal (y*t) := by push_cast; ring
  push_cast at he
  norm_num only [Complex.ofReal_neg,Complex.ofReal_ofNat]
  rw [he]
  ring

private theorem modulated_times_continuous_integrable (t : ℝ) (F : ℝ → ℂ)
    (hF : Continuous F) : Integrable (fun y => modulated t y*F y) :=
  ((modulated_contDiff t).continuous.mul hF).integrable_of_hasCompactSupport
    (modulated_hasCompactSupport t).mul_right

private theorem fourier_as_finite_integral {Q q : ℕ} (hQ : 0<Q) (hq : 1≤q) (t : ℝ) :
    (𝓕 (amplitudeSchwartz Q q)) t =
      (firstSum Q q : ℂ)*(∫ y : ℝ,modulated t y) -
        ∫ v : ℝ,(omega v : ℂ)*finiteSamples Q q t v := by
  have hQr : 0<(Q : ℝ) := by exact_mod_cast hQ
  have hqr : 0<(q : ℝ) := by exact_mod_cast (show 0<q by omega)
  let a : ℕ → ℝ := fun j => (q : ℝ)*(j : ℝ)/(Q : ℝ)
  have ha (j : ℕ) (hj : j∈Finset.Icc 1 Q) : 0<a j :=
    div_pos (mul_pos hqr (by exact_mod_cast (show 0<j by have := (Finset.mem_Icc.mp hj).1; omega))) hQr
  have hf (j : ℕ) (hj : j∈Finset.Icc 1 Q) : Integrable
      (fun y : ℝ => modulated t y*((a j)⁻¹*Omega (y/a j) : ℝ)) := by
    apply modulated_times_continuous_integrable
    exact Complex.continuous_ofReal.comp
      (continuous_const.mul (Omega_contDiff.continuous.comp (continuous_id.div_const _)))
  have hsum : Integrable (fun y : ℝ => ∑ j ∈ Finset.Icc 1 Q,
      modulated t y*((a j)⁻¹*Omega (y/a j) : ℝ)) := integrable_finset_sum _ hf
  have he (y : ℝ) : modulated t y*(h Q q y : ℂ) =
      modulated t y*(firstSum Q q : ℂ) -
        ∑ j ∈ Finset.Icc 1 Q,modulated t y*((a j)⁻¹*Omega (y/a j) : ℝ) := by
    unfold h firstSum
    simp only [Complex.ofReal_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have haj : a j≠0 := (ha j hj).ne'
    have h1 : (a j)⁻¹=(Q : ℝ)/((q : ℝ)*(j : ℝ)) := by dsimp [a]; rw [inv_div]
    have h2 : y/a j=y*(Q : ℝ)/((q : ℝ)*(j : ℝ)) := by dsimp [a]; field_simp
    rw [h1,h2]
    push_cast
    ring
  rw [fourier_as_integral]
  simp_rw [he]
  rw [integral_sub ((modulated_integrable t).mul_const _) hsum,integral_mul_const,
    integral_finset_sum _ hf,mul_comm (∫ y : ℝ,modulated t y)]
  congr 1
  calc
    _ = ∑ j ∈ Finset.Icc 1 Q,∫ v : ℝ,(omega v : ℂ)*
        (modulated t ((a j)*v)+modulated t (-((a j)*v))) :=
      Finset.sum_congr rfl (fun j hj => scaled_Omega_integral t (a j) (ha j hj))
    _ = ∫ v : ℝ, ∑ j ∈ Finset.Icc 1 Q,(omega v : ℂ)*
        (modulated t ((a j)*v)+modulated t (-((a j)*v))) := by
      symm
      apply integral_finset_sum
      intro j hj
      apply omega_times_continuous_integrable
      exact ((modulated_contDiff t).continuous.comp (continuous_const.mul continuous_id)).add
        ((modulated_contDiff t).continuous.comp (continuous_const.mul continuous_id).neg)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [finiteSamples,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [a]
      rw [div_mul_eq_mul_div (q : ℝ) (Q : ℝ) (j : ℝ)]

/-- The exact Fourier identity used for the near-one estimate. The `+1` is
the zero lattice term, integrated against the normalized fixed omega. -/
theorem fourier_identity {Q q : ℕ} (hQ : 2≤Q) (hq : 1≤q) (t : ℝ) :
    (𝓕 (amplitudeSchwartz Q q)) t =
      1+(firstSum Q q : ℂ)*(∫ y : ℝ,modulated t y) -
        ∫ v : ℝ,(omega v : ℂ)*
          (∑' k : ℤ,modulated t (((q : ℝ)/(Q : ℝ))*v*(k : ℝ))) := by
  rw [fourier_as_finite_integral (by omega) hq,
    weighted_lattice_integral (by omega) hq]
  ring



private theorem weight_integrable (x : ℝ) :
    Integrable (fun v : ℝ => (omega v : ℂ)/((x*v : ℝ) : ℂ)) := by
  have hh := SmoothDeltaFarDerivative.firstProfile_integrable.ofReal.const_mul ((x : ℂ)⁻¹)
  convert hh using 1
  funext v
  change (omega v : ℂ)/((x*v : ℝ) : ℂ) = (x : ℂ)⁻¹*((omega v/v : ℝ) : ℂ)
  push_cast
  ring

private theorem weight_integral (x : ℝ) :
    (∫ v : ℝ,(omega v : ℂ)/((x*v : ℝ) : ℂ)) =
      (((∫ v : ℝ,omega v/v)/x : ℝ) : ℂ) := by
  have he (v : ℝ) : (omega v : ℂ)/((x*v : ℝ) : ℂ)=
      (x : ℂ)⁻¹*((omega v/v : ℝ) : ℂ) := by
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_complex_ofReal]
  push_cast
  ring

private theorem centered_pointwise (x : ℝ) (hx : 0<x) (t v : ℝ) :
    (omega v : ℂ)/((x*v : ℝ) : ℂ)*
      (((x*v : ℝ) : ℂ)*(∑' k : ℤ,modulated t (x*v*(k : ℝ))) -
        ∫ y : ℝ,modulated t y) =
      (omega v : ℂ)*(∑' k : ℤ,modulated t (x*v*(k : ℝ))) -
        (omega v : ℂ)/((x*v : ℝ) : ℂ)*(∫ y : ℝ,modulated t y) := by
  by_cases hv : v=0
  · subst v
    have hz : omega 0=0 := by
      apply Function.notMem_support.mp
      rw [omega_support]
      norm_num
    simp [hz]
  · have hxc : (x : ℂ)≠0 := by exact_mod_cast hx.ne'
    have hvc : (v : ℂ)≠0 := by exact_mod_cast hv
    push_cast
    field_simp

/-- The centered error integral is absolutely integrable, despite the
harmless total inverse at v=0. -/
theorem centered_integrable {Q q : ℕ} (hQ : 0<Q) (hq : 1≤q) (t : ℝ) :
    Integrable (fun v : ℝ => (omega v : ℂ)/((((q : ℝ)/(Q : ℝ))*v : ℝ) : ℂ)*
      (((((q : ℝ)/(Q : ℝ))*v : ℝ) : ℂ)*
        (∑' k : ℤ,modulated t (((q : ℝ)/(Q : ℝ))*v*(k : ℝ))) -
          ∫ y : ℝ,modulated t y)) := by
  have hx : 0<(q : ℝ)/(Q : ℝ) := div_pos
    (by exact_mod_cast (show 0<q by omega)) (by exact_mod_cast hQ)
  simp_rw [centered_pointwise _ hx]
  exact (weighted_lattice_integrable hQ hq t).sub
    ((weight_integrable _).mul_const _)

/-- Exact cancellation of the two profile means. This identity contains the
uniform Riemann error to be bounded next, without assuming that estimate. -/
theorem centered_identity {Q q : ℕ} (hQ : 2≤Q) (hq : 1≤q) (t : ℝ) :
    (𝓕 (amplitudeSchwartz Q q)) t - 1 =
      ((firstSum Q q - (∫ v : ℝ,omega v/v)/((q : ℝ)/(Q : ℝ)) : ℝ) : ℂ)*
        (∫ y : ℝ,modulated t y) -
      ∫ v : ℝ,(omega v : ℂ)/((((q : ℝ)/(Q : ℝ))*v : ℝ) : ℂ)*
        (((((q : ℝ)/(Q : ℝ))*v : ℝ) : ℂ)*
          (∑' k : ℤ,modulated t (((q : ℝ)/(Q : ℝ))*v*(k : ℝ))) -
            ∫ y : ℝ,modulated t y) := by
  have hx : 0<(q : ℝ)/(Q : ℝ) := div_pos
    (by exact_mod_cast (show 0<q by omega)) (by exact_mod_cast (show 0<Q by omega))
  simp_rw [centered_pointwise _ hx]
  rw [integral_sub (weighted_lattice_integrable (by omega) hq t)
      ((weight_integrable _).mul_const _),integral_mul_const,weight_integral,
    fourier_identity hQ hq]
  push_cast
  ring

end CubicTenVariables.SmoothDeltaFourierIdentity
