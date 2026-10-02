import CubicTenVariables.SmoothDeltaNearBounds
import CubicTenVariables.SmoothDeltaFarDerivative
import CubicTenVariables.SmoothDeltaDecay
import CubicTenVariables.ScaledDerivativeIntegral
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.RealDeriv

/-! Uniform scaled derivative integrals for the actual smooth delta amplitude.
All pointwise estimates are supplied by proved near/far estimates. A finite
Leibniz sum handles the fixed cutoff, with one constant before both moduli. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaAmplitudeIntegral
open MeasureTheory Finset SmoothDeltaCutoffs SmoothDeltaKernel
open scoped BigOperators ContDiff

private theorem iteratedDeriv_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv N f) := by
  induction N with
  | zero => simpa using hf
  | succ N ih =>
    rw [iteratedDeriv_succ]
    apply ContDiff.deriv'
    simpa using ih

private theorem iteratedDeriv_ofReal (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    iteratedDeriv N (fun y => (f y : ℂ)) = fun y => ((iteratedDeriv N f y : ℝ) : ℂ) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [iteratedDeriv_succ,ih]
    funext y
    rw [iteratedDeriv_succ]
    exact (((iteratedDeriv_contDiff f hf N).differentiable (by simp) y).hasDerivAt.ofReal_comp).deriv

private theorem norm_amplitude_derivative (Q q N : ℕ) (y : ℝ) :
    ‖iteratedDeriv N (amplitude Q q) y‖ = ‖iteratedDeriv N (g Q q) y‖ := by
  change ‖iteratedDeriv N (fun z => (g Q q z : ℂ)) y‖ = _
  rw [iteratedDeriv_ofReal _ (g_contDiff Q q)]
  simp only [Complex.norm_real,Real.norm_eq_abs]

private theorem cutoff_derivative_bound (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y : ℝ, ‖iteratedDeriv N U y‖ ≤ C := by
  have hc : HasCompactSupport (iteratedDeriv N U) := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (U_hasCompactSupport.iteratedFDeriv N).comp_left (map_zero _)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous
    (iteratedDeriv_contDiff U U_contDiff N).continuous
  exact ⟨max 1 C,le_max_left _ _,fun y => (hC y).trans (le_max_right _ _)⟩

private theorem norm_amplitude_derivative_le (Q q N : ℕ) (y : ℝ) :
    ‖iteratedDeriv N (amplitude Q q) y‖ ≤
      ∑ i ∈ range (N+1), (N.choose i : ℝ) * ‖iteratedDeriv i U y‖ *
        ‖iteratedDeriv (N-i) (h Q q) y‖ := by
  rw [norm_amplitude_derivative]
  simpa only [g,norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
    norm_iteratedFDeriv_mul_le U_contDiff (h_contDiff Q q) y
      (show (N : WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top)

private theorem amplitude_derivative_zero {Q q N : ℕ} {y : ℝ} (hy : 1/4 < |y|) :
    iteratedDeriv N (amplitude Q q) y = 0 := by
  have hnot : y ∉ tsupport (g Q q) := by
    intro hmem
    have hm := g_tsupport_subset Q q hmem
    have habs : |y| ≤ 1/4 := abs_le.mpr hm
    linarith
  have hz : iteratedFDeriv ℝ N (g Q q) y = 0 :=
    Function.notMem_support.mp (fun hh => hnot (support_iteratedFDeriv_subset N hh))
  have hg : iteratedDeriv N (g Q q) y = 0 := by simp [iteratedDeriv,hz]
  change iteratedDeriv N (fun z => (g Q q z : ℂ)) y = 0
  rw [iteratedDeriv_ofReal _ (g_contDiff Q q)]
  change ((iteratedDeriv N (g Q q) y : ℝ) : ℂ) = 0
  rw [hg,Complex.ofReal_zero]

private theorem exists_pointwise_bounds (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ q : ℕ, 1 ≤ q → q ≤ Q →
      (∀ y : ℝ, |y| ≤ (q : ℝ)/(Q : ℝ) →
        ‖iteratedDeriv N (amplitude Q q) y‖ ≤ B/((q : ℝ)/(Q : ℝ))^(N+1)) ∧
      (∀ y : ℝ, (q : ℝ)/(Q : ℝ) ≤ |y| →
        ‖iteratedDeriv N (amplitude Q q) y‖ ≤
          B*((q : ℝ)/(Q : ℝ))*|y|^(-((N+2 : ℕ) : ℝ))) := by
  classical
  choose A hA hnear using SmoothDeltaNearBounds.exists_bound
  choose F hF hfar using SmoothDeltaFarDerivative.exists_bound
  choose V hV hcut using cutoff_derivative_bound
  let K : ℝ := ∑ i ∈ range (N+1), (N.choose i : ℝ)*V i*(A (N-i)+F (N-i))
  have hK0 : 0 ≤ K := by
    apply sum_nonneg
    intro i hi
    have hVi := zero_le_one.trans (hV i)
    have hAi := zero_le_one.trans (hA (N-i))
    have hFi := zero_le_one.trans (hF (N-i))
    positivity
  refine ⟨max 1 K,le_max_left _ _,?_⟩
  intro Q hQ q hq hqQ
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  let a : ℝ := (q : ℝ)/(Q : ℝ)
  have ha : 0 < a := div_pos hqR hQR
  have ha1 : a ≤ 1 := (div_le_one hQR).mpr (by exact_mod_cast hqQ)
  have hcoeff (i : ℕ) : 0 ≤ (N.choose i : ℝ)*V i :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (hV i))
  constructor
  · intro y hy
    have ht (i : ℕ) (hi : i ∈ range (N+1)) :
        ‖iteratedDeriv (N-i) (h Q q) y‖ ≤ (A (N-i)+F (N-i))/a^(N+1) := by
      have hh := hnear (N-i) Q hQ q hq hqQ y hy
      rw [← Real.norm_eq_abs] at hh
      have hp : a^(N+1) ≤ a^(N-i+1) :=
        pow_le_pow_of_le_one ha.le ha1 (by omega)
      exact hh.trans (div_le_div₀ (add_nonneg (zero_le_one.trans (hA _)) (zero_le_one.trans (hF _)))
        (le_add_of_nonneg_right (zero_le_one.trans (hF _))) (pow_pos ha _) hp)
    have hb : ‖iteratedDeriv N (amplitude Q q) y‖ ≤ K/a^(N+1) := by
      apply (norm_amplitude_derivative_le Q q N y).trans
      dsimp only [K]
      rw [sum_div]
      apply sum_le_sum
      intro i hi
      calc
        _ ≤ ((N.choose i : ℝ)*V i) * ((A (N-i)+F (N-i))/a^(N+1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hcut i y) (Nat.cast_nonneg _))
            (ht i hi) (norm_nonneg _) (hcoeff i)
        _ = _ := by ring
    exact hb.trans (div_le_div_of_nonneg_right (le_max_right _ _) (pow_nonneg ha.le _))
  · intro y hy
    by_cases hy4 : |y| ≤ 1/4
    · have hy0 : 0 < |y| := ha.trans_le hy
      have hy1 : |y| ≤ 1 := by linarith
      have ht (i : ℕ) (hi : i ∈ range (N+1)) :
          ‖iteratedDeriv (N-i) (h Q q) y‖ ≤
            ((A (N-i)+F (N-i))*a)/|y|^(N+2) := by
        have hh := hfar (N-i) Q q (by omega) hq y hy hy4
        rw [← Real.norm_eq_abs] at hh
        have hp : |y|^(N+2) ≤ |y|^(N-i+2) :=
          pow_le_pow_of_le_one hy0.le hy1 (by omega)
        exact hh.trans (div_le_div₀
          (mul_nonneg (add_nonneg (zero_le_one.trans (hA _)) (zero_le_one.trans (hF _))) ha.le)
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (zero_le_one.trans (hA _))) ha.le)
          (pow_pos hy0 _) hp)
      have hb : ‖iteratedDeriv N (amplitude Q q) y‖ ≤ K*a/|y|^(N+2) := by
        apply (norm_amplitude_derivative_le Q q N y).trans
        dsimp only [K]
        rw [sum_mul,sum_div]
        apply sum_le_sum
        intro i hi
        calc
          _ ≤ ((N.choose i : ℝ)*V i) * (((A (N-i)+F (N-i))*a)/|y|^(N+2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hcut i y) (Nat.cast_nonneg _))
              (ht i hi) (norm_nonneg _) (hcoeff i)
          _ = _ := by ring
      have hp : K*a/|y|^(N+2) = K*a*|y|^(-((N+2 : ℕ) : ℝ)) := by
        rw [Real.rpow_neg (abs_nonneg y),Real.rpow_natCast,div_eq_mul_inv]
      rw [hp] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le)
        (Real.rpow_nonneg (abs_nonneg y) _))
    · rw [amplitude_derivative_zero (lt_of_not_ge hy4),norm_zero]
      positivity

/-- One constant for each derivative order, chosen before both moduli,
bounds the scaled integral of the actual complex amplitude derivative. -/
theorem exists_scaled_integral_bound (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ q : ℕ, 1 ≤ q → q ≤ Q →
      ((q : ℝ)/(Q : ℝ))^N *
        (∫ y : ℝ, ‖iteratedDeriv N (amplitude Q q) y‖) ≤ B := by
  obtain ⟨B,hB,hbounds⟩ := exists_pointwise_bounds N
  refine ⟨4*B,(by linarith),?_⟩
  intro Q hQ q hq hqQ
  obtain ⟨hn,hf⟩ := hbounds Q hQ q hq hqQ
  apply ScaledDerivativeIntegral.scaled_integral_le _
    (SmoothDeltaDecay.amplitude_iteratedDeriv_integrable Q q N)
    ((q : ℝ)/(Q : ℝ)) B (by
      apply div_pos <;> exact_mod_cast (show 0 < _ by omega))
    (zero_le_one.trans hB) N hn hf

/-- Uniform rapid decay of the concrete Fourier kernel, with every
normalization and derivative-integral hypothesis discharged internally. -/
theorem rapid_decay : ∀ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ Q, 2 ≤ Q → ∀ q, 1 ≤ q → q ≤ Q → ∀ θ : ℝ,
      ‖p Q q θ‖ ≤ C*(1+(q : ℝ)*(Q : ℝ)*|θ|)^(-(N : ℝ)) :=
  SmoothDeltaDecay.rapid_decay_of_integral_bounds SmoothDeltaNormalization.c_bounded
    exists_scaled_integral_bound

end CubicTenVariables.SmoothDeltaAmplitudeIntegral
