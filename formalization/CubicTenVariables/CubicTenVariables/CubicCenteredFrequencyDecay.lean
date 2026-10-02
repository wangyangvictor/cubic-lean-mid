import CubicTenVariables.CubicGradientWindow

/-! Simultaneous rapid scale and frequency decay for a fixed homogeneous cubic
and its fixed centered weight. The estimate follows from the proved centered
gradient-window theorem; no generic BHB proposition is assumed or imported.
The constant and frequency cutoff precede every varying scale, phase and frequency. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.CubicCenteredFrequencyDecay
open MvPolynomial MeasureTheory HessianTheorem11
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

/-- Compactness bounds the actual gradient on the doubled centered box. -/
theorem exists_gradient_bound (F : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ) (S : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x : Fin n → ℝ, ‖x-a‖ ≤ 2*S → ‖gradient F x‖ ≤ B := by
  have hg : Continuous (gradient F) := by
    exact continuous_pi fun i => (pderiv i F).continuous_eval
  obtain ⟨B,hB⟩ := (isCompact_closedBall a (2*S)).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro x hx
  exact (hB x (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)).trans
    (le_max_right _ _)

private theorem max_sqrt_sq_le (t : ℝ) :
    (max 1 (Real.sqrt |t|))^2 ≤ max 1 |t| := by
  rcases le_total 1 (Real.sqrt |t|) with h | h
  · rw [max_eq_right h,Real.sq_sqrt (abs_nonneg t)]
    exact le_max_right _ _
  · rw [max_eq_left h,one_pow]
    exact le_max_left _ _

/-- The actual centered gradient window is empty beyond an explicit frequency
threshold, provided the window radius has the displayed quadratic relation. -/
theorem window_empty_of_frequency (F : MvPolynomial (Fin n) ℝ)
    (a : Fin n → ℝ) (S B t : ℝ) (u : Fin n → ℝ) (R : ℝ)
    (hg : ∀ x : Fin n → ℝ, ‖x-a‖ ≤ 2*S → ‖gradient F x‖ ≤ B)
    (hu : 0 < ‖u‖) (huT : max 1 |t| ≤ ‖u‖)
    (huB : 4*B*|t| ≤ ‖u‖) (hRsq : 16*R^2 = ‖u‖) :
    CubicGradientWindow.window F a S t u R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hgrad := hg x hx.1
  let W : ℝ := max 1 (Real.sqrt |t|)
  have hWsq : W^2 ≤ max 1 |t| := max_sqrt_sq_le t
  have hs1 := mul_le_mul_of_nonneg_left hWsq (by positivity : 0 ≤ 16*R^2)
  have hs2 := mul_le_mul_of_nonneg_left huT hu.le
  have hRW : R*W ≤ ‖u‖/4 := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith [hRsq]
  have hgT : ‖t • gradient F x‖ ≤ |t| * B := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hgrad (abs_nonneg _)
  have hxu : ‖t • gradient F x-u‖ ≤ R*W := hx.2
  have htri := norm_le_norm_sub_add u (t • gradient F x)
  rw [norm_sub_rev] at htri
  nlinarith

/-- Arbitrarily strong simultaneous decay, with the original homogeneous
polynomial and centered compact weight. All constants precede P,t,u. The
constructed lower scale cutoff is one. No positivity of the weight is needed. -/
theorem exists_normalized_frequency_bound (F : MvPolynomial (Fin n) ℝ)
    (hF : F.IsHomogeneous 3) (w : (Fin n → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (a : Fin n → ℝ) (S : ℝ) (hS : 0 < S)
    (hs : ∀ x ∈ tsupport w, ‖x-a‖ ≤ S)
    (ε : ℝ) (hε : 0 < ε) (A N : ℕ) :
    ∃ C K P₀ : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ (t : ℝ) (u : Fin n → ℝ),
      K*P^(2*ε)*max 1 |t| ≤ ‖u‖ →
      ‖PolynomialOscillatory.integral F w t u‖ ≤ C*P^(-(A : ℝ))*‖u‖^(-(N : ℝ)) := by
  obtain ⟨B,hB,hg⟩ := exists_gradient_bound F a S
  obtain ⟨L,hL⟩ := exists_nat_gt ((A : ℝ)/ε)
  have hLA : (A : ℝ) ≤ ε*(L : ℝ) :=
    (div_le_iff₀ hε).mp hL.le |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hb⟩ := CubicGradientWindow.exists_bound F hF w hw hc a S hS hs (L+2*N)
  let D : ℝ := 16
  let K : ℝ := max D (4*B)
  refine ⟨C*D^N,K,1,?_,?_,le_rfl,?_⟩
  · exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by norm_num [D]))
  · exact le_trans (by norm_num [D] : (1 : ℝ) ≤ D) (le_max_left _ _)
  intro P hP t u hu
  have hP1 : 1 ≤ P := hP
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hD : 0 < D := by norm_num [D]
  have hD1 : 1 ≤ D := by norm_num [D]
  have hK1 : 1 ≤ K := le_trans hD1 (le_max_left _ _)
  have hPe : 1 ≤ P^(2*ε) := Real.one_le_rpow hP1 (by positivity)
  have hT : 1 ≤ max 1 |t| := le_max_left _ _
  have hT0 : 0 ≤ max 1 |t| := by positivity
  have hu1 : 1 ≤ ‖u‖ := (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK1 hPe) hT).trans hu
  have hu0 : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hu1
  have huT : max 1 |t| ≤ ‖u‖ :=
    (le_mul_of_one_le_left hT0 (one_le_mul_of_one_le_of_one_le hK1 hPe)).trans hu
  have huB : 4*B*|t| ≤ ‖u‖ := by
    calc
      _ ≤ K*|t| := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
      _ ≤ (K*P^(2*ε))*max 1 |t| := by
        apply mul_le_mul
        · exact le_mul_of_one_le_right (by linarith : 0 ≤ K) hPe
        · exact le_max_right _ _
        · exact abs_nonneg _
        · positivity
      _ ≤ _ := hu
  have huD : D*P^(2*ε) ≤ ‖u‖ := by
    calc
      _ ≤ K*P^(2*ε) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ (K*P^(2*ε))*max 1 |t| := le_mul_of_one_le_right (by positivity) hT
      _ ≤ _ := hu
  let R : ℝ := Real.sqrt (‖u‖/D)
  have hRpos : 0 < R := Real.sqrt_pos.mpr (div_pos hu0 hD)
  have hRsq : R^2=‖u‖/D := Real.sq_sqrt (div_nonneg hu0.le hD.le)
  have hRD : D*R^2=‖u‖ := by rw [hRsq]; field_simp
  have hPR : P^ε ≤ R := by
    apply le_of_sq_le_sq _ hRpos.le
    rw [hRsq,le_div_iff₀ hD]
    convert huD using 1
    rw [← Real.rpow_two,← Real.rpow_mul hP0.le]
    ring_nf
  have hRcut : 1 ≤ R := (Real.one_le_rpow hP1 hε.le).trans hPR
  have hempty := window_empty_of_frequency F a S B t u R hg hu0 huT huB hRD
  have hib := hb t u R hRcut
  rw [hempty,measure_empty,ENNReal.toReal_zero,add_zero] at hib
  have hRL : R^(-(L : ℝ)) ≤ P^(-(A : ℝ)) := by
    calc
      _ ≤ (P^ε)^(-(L : ℝ)) := Real.rpow_le_rpow_of_nonpos (by positivity) hPR
        (neg_nonpos.mpr (Nat.cast_nonneg L))
      _ ≤ P^(-(A : ℝ)) := by
        rw [← Real.rpow_mul hP0.le]
        exact Real.rpow_le_rpow_of_exponent_le hP1 (by nlinarith)
  have hRN : R^(-((2*N : ℕ) : ℝ)) = D^N*‖u‖^(-(N : ℝ)) := by
    rw [Real.rpow_neg hRpos.le,Real.rpow_natCast,pow_mul]
    rw [hRsq,div_pow,inv_div,Real.rpow_neg hu0.le,Real.rpow_natCast]
    rfl
  calc
    _ ≤ C*R^(-((L+2*N : ℕ) : ℝ)) := hib
    _ = C*(R^(-(L : ℝ))*R^(-((2*N : ℕ) : ℝ))) := by
      rw [← Real.rpow_add hRpos]
      congr 2
      push_cast
      ring
    _ ≤ C*(P^(-(A : ℝ))*(D^N*‖u‖^(-(N : ℝ)))) := by
      rw [hRN]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hRL (by positivity)) (by linarith)
    _ = _ := by ring

end CubicTenVariables.CubicCenteredFrequencyDecay
