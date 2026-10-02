import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic

/-! The literal one-dimensional shifted residue Gaussian identity and
absolute summability. Poisson summation and Gaussian decay are proved
mathlib theorems; no analytic input is assumed. -/

noncomputable section
namespace CubicTenVariables.GaussianResiduePoisson
open scoped Topology

private theorem summable_norm_quadratic {A : ℂ} (hA : A.re < 0) (B D : ℂ) :
    Summable (fun n : ℤ => ‖Complex.exp (A*(n : ℂ)^2+B*n+D)‖) := by
  have hs : Summable (fun n : ℤ => ‖Complex.exp (A*(n : ℂ)^2+B*n)‖) := by
    have h := summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      ((cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hA B (-2)).isBigO.norm_left.comp_tendsto
        Int.tendsto_coe_cofinite)
    simpa only [Function.comp_def, Complex.ofReal_intCast] using h
  simpa only [← norm_mul, ← Complex.exp_add] using hs.mul_right ‖Complex.exp D‖

private theorem summable_norm_shifted_gaussian (q t : ℝ) (hq : 0 < q) :
    Summable (fun n : ℤ => ‖Complex.exp (-(q : ℂ)*((n : ℂ)+t)^2)‖) := by
  have hq' : (-(q : ℂ)).re < 0 := by simpa using neg_neg_of_pos hq
  convert summable_norm_quadratic hq' (-2*q*t) (-q*(t : ℂ)^2) using 1
  ext n
  congr 2
  ring

private theorem shifted_theta_complex (q t : ℝ) (hq : 0 < q) :
    (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ)*q*((n : ℂ)+t)^2)) =
      (1/(q : ℂ)^(1/2 : ℂ)) * ∑' h : ℤ,
        Complex.exp (-(Real.pi : ℂ)/q*(h : ℂ)^2) *
          Complex.exp (2*Real.pi*Complex.I*(h : ℂ)*(t : ℂ)) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have h := Complex.tsum_exp_neg_quadratic (by simpa using hq : 0 < (q : ℂ).re)
    (-(q : ℂ)*t)
  calc
    _ = Complex.exp (-(Real.pi : ℂ)*q*(t : ℂ)^2) *
        ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ)*q*(n : ℂ)^2+
          2*Real.pi*(-(q : ℂ)*t)*n) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [← Complex.exp_add]
      congr 1
      ring
    _ = Complex.exp (-(Real.pi : ℂ)*q*(t : ℂ)^2) *
        ((1/(q : ℂ)^(1/2 : ℂ)) *
          ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ)/q*((n : ℂ)+Complex.I*(-(q : ℂ)*t))^2)) := by
      rw [h]
    _ = _ := by
      rw [mul_left_comm, ← tsum_mul_left]
      congr 1
      apply tsum_congr
      intro n
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      field_simp
      ring_nf
      simp only [Complex.I_sq]
      ring

private theorem shifted_theta_real (q t : ℝ) (hq : 0 < q) :
    (∑' n : ℤ, (Real.exp (-Real.pi*q*((n : ℝ)+t)^2) : ℂ)) =
      ((1/Real.sqrt q : ℝ) : ℂ) * ∑' h : ℤ,
        (Real.exp (-Real.pi/q*(h : ℝ)^2) : ℂ) *
          Complex.exp (2*Real.pi*Complex.I*(h : ℂ)*(t : ℂ)) := by
  have hc : (q : ℂ)^(1/2 : ℂ) = (Real.sqrt q : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hq.le]
    norm_num
  simpa only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_add,
    Complex.ofReal_intCast, hc] using shifted_theta_complex q t hq

/-- Absolute convergence of the Gaussian over the actual shifted progression. -/
theorem summable_residue_gaussian_norm (c W a u : ℝ) (hc : 0 < c) (hW : 0 < W) :
    Summable (fun n : ℤ => ‖(Real.exp (-((a+c*(n : ℝ)-u)/W)^2) : ℂ)‖) := by
  have hs := summable_norm_shifted_gaussian ((c/W)^2) ((a-u)/c)
    (sq_pos_of_pos (div_pos hc hW))
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hWC : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  convert hs using 1
  ext n
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  field_simp [hcC, hWC]
  ring

/-- Convergence of the literal complex-valued progression Gaussian. -/
theorem summable_residue_gaussian (c W a u : ℝ) (hc : 0 < c) (hW : 0 < W) :
    Summable (fun n : ℤ => (Real.exp (-((a+c*(n : ℝ)-u)/W)^2) : ℂ)) :=
  (summable_residue_gaussian_norm c W a u hc hW).of_norm

/-- Absolute convergence on the Fourier side, including its translated phase. -/
theorem summable_dual_gaussian_norm (c W a u : ℝ) (hc : 0 < c) (hW : 0 < W) :
    Summable (fun h : ℤ => ‖(Real.exp (-Real.pi^2*W^2*(h : ℝ)^2/c^2) : ℂ) *
      Complex.exp (2*Real.pi*Complex.I*(h : ℂ)*(((a-u)/c : ℝ) : ℂ))‖) := by
  have hq : 0 < Real.pi^2*W^2/c^2 := by positivity
  have hs := summable_norm_shifted_gaussian (Real.pi^2*W^2/c^2) 0 hq
  convert hs using 1
  ext h
  rw [norm_mul, Complex.norm_exp]
  have him : (2*(Real.pi : ℂ)*Complex.I*(h : ℂ)*(((a-u)/c : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [him, Real.exp_zero, mul_one, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

/-- Convergence of the literal phase-weighted dual Gaussian. -/
theorem summable_dual_gaussian (c W a u : ℝ) (hc : 0 < c) (hW : 0 < W) :
    Summable (fun h : ℤ => (Real.exp (-Real.pi^2*W^2*(h : ℝ)^2/c^2) : ℂ) *
      Complex.exp (2*Real.pi*Complex.I*(h : ℂ)*(((a-u)/c : ℝ) : ℂ))) :=
  (summable_dual_gaussian_norm c W a u hc hW).of_norm

/-- Exact shifted residue Poisson identity with positive real spacing and
width. The dual phase retains the arbitrary real center and positive sign. -/
theorem residue_gaussian_eq (c W a u : ℝ) (hc : 0 < c) (hW : 0 < W) :
    (∑' n : ℤ, (Real.exp (-((a+c*(n : ℝ)-u)/W)^2) : ℂ)) =
      ((Real.sqrt Real.pi*W/c : ℝ) : ℂ) *
        ∑' h : ℤ, (Real.exp (-Real.pi^2*W^2*(h : ℝ)^2/c^2) : ℂ) *
          Complex.exp (2*Real.pi*Complex.I*(h : ℂ)*(((a-u)/c : ℝ) : ℂ)) := by
  let q : ℝ := c^2/(Real.pi*W^2)
  have hq : 0 < q := by dsimp [q]; positivity
  have hcoeff : 1/Real.sqrt q = Real.sqrt Real.pi*W/c := by
    dsimp [q]
    rw [Real.sqrt_div (sq_nonneg c), Real.sqrt_sq hc.le,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hW.le]
    field_simp
  have h := shifted_theta_real q ((a-u)/c) hq
  rw [hcoeff] at h
  convert h using 1
  · apply tsum_congr
    intro n
    congr 2
    dsimp [q]
    field_simp
    ring
  · congr 1
    apply tsum_congr
    intro n
    congr 2
    dsimp [q]
    field_simp

end CubicTenVariables.GaussianResiduePoisson
