import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact numerical assembly of the full Gaussian squarefull estimate. -/

noncomputable section
namespace CubicTenVariables.OnionExponentAssembly

/-- The enlarged width controls the full Gaussian kernel envelope. -/
theorem kernel_envelope_le (c d W : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hW : 0 < W) (hrW : c^2*d ≤ W^3) :
    (c/d+(c/W)^3)^5 ≤ (2*c/d)^5 := by
  have hsmall : (c/W)^3 ≤ c/d := by
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hW 3) hd).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrW hc.le]
  have hh : c/d+(c/W)^3 ≤ 2*c/d := by
    calc
      c/d+(c/W)^3 ≤ c/d+c/d := add_le_add le_rfl hsmall
      _ = 2*c/d := by ring
  exact pow_le_pow_left₀ (by positivity) hh 5

/-- All powers from Poisson, the character sum and scalar counting combine
with the claimed r^(6+epsilon) normalization. -/
theorem gaussian_factor_le (c d e W ε C : ℝ)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 0 ≤ e) (hW : 0 < W)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hrW : c^2*d ≤ W^3) :
    c^11*d^6*Real.exp 10*(Real.sqrt Real.pi*W/c)^10*c*
        (C*c^5*d^((11:ℝ)/2+ε)*e^((1:ℝ)/2)*(c/d+(c/W)^3)^5) ≤
      (32*Real.exp 10*Real.pi^5*C)*(c^2*d)^(6+ε)*
        d^((1:ℝ)/2)*e^((1:ℝ)/2)*W^10 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hr0 : 0 < c^2*d := by positivity
  have he0 : 0 ≤ e^((1:ℝ)/2) := Real.rpow_nonneg he _
  have henv := kernel_envelope_le c d W hc0 hd0 hW hrW
  have hbase : d ≤ c^2*d := by nlinarith [sq_nonneg (c-1)]
  have heps := Real.rpow_le_rpow hd0.le hbase hε
  have hpi : (Real.sqrt Real.pi)^10 = Real.pi^5 := by
    rw [show (10:ℕ)=2*5 by norm_num, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have hdexp : d^((11:ℝ)/2+ε) = d^5*d^((1:ℝ)/2)*d^ε := by
    rw [show (11:ℝ)/2+ε=(5+(1:ℝ)/2)+ε by ring,
      Real.rpow_add hd0, Real.rpow_add hd0]
    norm_num
  calc
    _ ≤ c^11*d^6*Real.exp 10*(Real.sqrt Real.pi*W/c)^10*c*
        (C*c^5*d^((11:ℝ)/2+ε)*e^((1:ℝ)/2)*(2*c/d)^5) := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left henv (by positivity)) (by positivity)
    _ = (32*Real.exp 10*Real.pi^5*C)*c^12*d^6*
        d^((1:ℝ)/2)*e^((1:ℝ)/2)*W^10*d^ε := by
      rw [hdexp, div_pow, mul_pow, hpi]
      field_simp
      ring
    _ ≤ (32*Real.exp 10*Real.pi^5*C)*c^12*d^6*
        d^((1:ℝ)/2)*e^((1:ℝ)/2)*W^10*(c^2*d)^ε :=
      mul_le_mul_of_nonneg_left heps (by positivity)
    _ = _ := by
      rw [Real.rpow_add hr0]
      norm_num
      ring

/-- The source's enlarged radius supplies the required cubic inequality. -/
theorem enlarged_width (r R : ℝ) (hr : 0 < r) (hR : 0 ≤ R) :
    0 < R+r^((1:ℝ)/3) ∧ R ≤ R+r^((1:ℝ)/3) ∧
      r ≤ (R+r^((1:ℝ)/3))^3 := by
  have hroot : 0 < r^((1:ℝ)/3) := Real.rpow_pos_of_pos hr _
  have hcube : (r^((1:ℝ)/3))^3 = r := by
    rw [← Real.rpow_mul_natCast hr.le]
    norm_num
  refine ⟨by positivity, le_add_of_nonneg_right hroot.le, ?_⟩
  calc
    r = (r^((1:ℝ)/3))^3 := hcube.symm
    _ ≤ _ := pow_le_pow_left₀ hroot.le (le_add_of_nonneg_left hR) 3

end CubicTenVariables.OnionExponentAssembly
