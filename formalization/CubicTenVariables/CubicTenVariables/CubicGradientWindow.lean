import CubicTenVariables.CubicBumpLocalization
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! The fixed homogeneous cubic gradient-window estimate on a centered box.
A normalized smooth bump is constructed internally. The window stays in the
doubled support box, which is the actual regular-chart domain needed later.
All constants precede the phase, frequency and window parameter. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.CubicGradientWindow
open MvPolynomial MeasureTheory HessianTheorem11 CubicBumpLocalization
open scoped BigOperators ContDiff Topology
variable {n : ℕ}

/-- A normalized smooth bump in any prescribed positive coordinate radius. -/
theorem exists_normalized_bump (S : ℝ) (hS : 0 < S) :
    ∃ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∫ z, φ z = 1) ∧ (∀ z ∈ tsupport φ, ‖z‖ ≤ S) := by
  let b : ContDiffBump (0 : Fin n → ℝ) :=
    ⟨S/2,S,half_pos hS,half_lt_self hS⟩
  refine ⟨b.normed volume,b.contDiff_normed,b.hasCompactSupport_normed,
    b.integral_normed,?_⟩
  intro z hz
  rw [b.tsupport_normed_eq] at hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using hz

/-- The positive localization scale includes the small-phase regime. -/
def scale (t : ℝ) : ℝ := (max 1 (Real.sqrt |t|))⁻¹

theorem scale_bounds (t : ℝ) :
    0 < scale t ∧ scale t ≤ 1 ∧ |t * (scale t)^2| ≤ 1 := by
  let m := max 1 (Real.sqrt |t|)
  have hm : 1 ≤ m := le_max_left _ _
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hδ : 0 < scale t := inv_pos.mpr hm0
  have hδ1 : scale t ≤ 1 := (inv_le_one₀ hm0).mpr hm
  refine ⟨hδ,hδ1,?_⟩
  have ht : |t| ≤ m^2 := by
    have hs := Real.sq_sqrt (abs_nonneg t)
    have hb : Real.sqrt |t| ≤ m := le_max_right _ _
    nlinarith [Real.sqrt_nonneg |t|]
  rw [abs_mul,abs_of_nonneg (sq_nonneg (scale t))]
  calc
    |t| * (scale t)^2 ≤ m^2 * (scale t)^2 :=
      mul_le_mul_of_nonneg_right ht (sq_nonneg _)
    _ = 1 := by dsimp [scale,m]; field_simp

/-- Both weights force the center into the doubled support box. -/
theorem localized_eq_zero_outside_centered (F : MvPolynomial (Fin n) ℝ)
    (w φ : (Fin n → ℝ) → ℝ) (a : Fin n → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hsw : ∀ x ∈ tsupport w, ‖x-a‖ ≤ S)
    (hsφ : ∀ z ∈ tsupport φ, ‖z‖ ≤ S)
    (t δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (u y : Fin n → ℝ)
    (hy : ¬ ‖y-a‖ ≤ 2*S) : localized F w φ t δ u y = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  by_cases hφz : φ z = 0
  · simp [wave,hφz]
  by_cases hwz : w (y + δ • z) = 0
  · simp [wave,hwz]
  exfalso
  apply hy
  have hz := hsφ z (subset_tsupport φ hφz)
  have hx := hsw (y + δ • z) (subset_tsupport w hwz)
  calc
    ‖y-a‖ = ‖((y + δ • z)-a) - δ • z‖ := by congr 1; abel
    _ ≤ ‖(y + δ • z)-a‖ + ‖δ • z‖ := norm_sub_le _ _
    _ ≤ 2*S := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ.1]
      nlinarith [norm_nonneg z,hδ.1,hδ.2]

/-- Centered-box version of the already proved localized Fourier estimate. -/
theorem exists_centered_integral_bound (F : MvPolynomial (Fin n) ℝ)
    (hF : F.IsHomogeneous 3) (w : (Fin n → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (hcw : HasCompactSupport w)
    (a : Fin n → ℝ) (S : ℝ) (hS : 0 < S)
    (hsw : ∀ x ∈ tsupport w, ‖x-a‖ ≤ S) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (u : Fin n → ℝ),
      ‖PolynomialOscillatory.integral F w t u‖ ≤
        C * ∫ y in Metric.closedBall a (2*S),
          1 / (1 + scale t * ‖u-t • gradient F y‖)^N := by
  obtain ⟨φ,hφ,hcφ,hnorm,hsφ⟩ := exists_normalized_bump (n := n) S hS
  let Y := Metric.closedBall a (2*S)
  have hY : IsCompact Y := isCompact_closedBall _ _
  obtain ⟨C,hC,hbound⟩ := CubicLocalizedFourierFamily.exists_uniform_bound
    F w φ hw hφ hcφ Y hY 1 (by norm_num) N
  refine ⟨C,hC,?_⟩
  intro t u
  obtain ⟨hδ0,hδ1,ht⟩ := scale_bounds t
  have hδ : scale t ∈ Set.Icc (0 : ℝ) 1 := ⟨hδ0.le,hδ1⟩
  have hp : ∀ y ∈ Y, ‖localized F w φ t (scale t) u y‖ ≤
      C / (1 + scale t * ‖u-t • gradient F y‖)^N := by
    intro y hy
    rw [norm_localized_eq_fourier F hF]
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hδ0] using
      hbound y hy (scale t) hδ (t*(scale t)^2) (abs_le.mp ht)
        ((scale t) • (u-t • gradient F y))
  have hz : ∀ y, y ∉ Y → localized F w φ t (scale t) u y = 0 := by
    intro y hy
    apply localized_eq_zero_outside_centered F w φ a S hS.le hsw hsφ t (scale t) hδ u y
    simpa only [Y,Metric.mem_closedBall,dist_eq_norm] using hy
  have hg : Continuous (fun y : Fin n → ℝ =>
      C / (1 + scale t * ‖u-t • gradient F y‖)^N) := by
    apply continuous_const.div
    · apply Continuous.pow
      apply continuous_const.add
      apply continuous_const.mul
      apply Continuous.norm
      apply continuous_const.sub
      apply continuous_const.smul
      exact continuous_pi fun i => (PolynomialCalculus.contDiff_eval (pderiv i F)).continuous
    · intro y
      exact ne_of_gt (pow_pos (by positivity) N)
  calc
    ‖PolynomialOscillatory.integral F w t u‖ =
        ‖∫ y in Y, localized F w φ t (scale t) u y‖ := by
      rw [integral_eq_localized F w φ hw.continuous hcw hφ.continuous hcφ hnorm]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    _ ≤ ∫ y in Y, C / (1 + scale t * ‖u-t • gradient F y‖)^N := by
      apply norm_integral_le_of_norm_le (hg.continuousOn.integrableOn_compact hY)
      filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
      exact hp y hy
    _ = C * ∫ y in Y, 1 / (1 + scale t * ‖u-t • gradient F y‖)^N := by
      rw [← integral_const_mul]
      congr 1
      ext y
      ring

/-- The literal centered gradient window for the original homogeneous cubic. -/
def window (F : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ)
    (S t : ℝ) (u : Fin n → ℝ) (R : ℝ) : Set (Fin n → ℝ) :=
  {y | ‖y-a‖ ≤ 2*S ∧
    ‖t • gradient F y-u‖ ≤ R * max 1 (Real.sqrt |t|)}

private theorem integral_kernel_le (Y : Set (Fin n → ℝ)) (hY : IsCompact Y)
    (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) (hgn : ∀ y, 0 ≤ g y)
    (m R : ℝ) (hm : 1 ≤ m) (hR : 1 ≤ R) (N : ℕ) :
    (∫ y in Y, 1 / (1 + m⁻¹ * g y)^N) ≤
      (volume Y).toReal / R^N + (volume (Y ∩ {y | g y ≤ R*m})).toReal := by
  let W := Y ∩ {y | g y ≤ R*m}
  have hW : MeasurableSet W := hY.measurableSet.inter (isClosed_le hg continuous_const).measurableSet
  have hWY : W ⊆ Y := Set.inter_subset_left
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  haveI : IsFiniteMeasure (volume.restrict Y) := ⟨by simpa using hY.measure_lt_top⟩
  have hi : Integrable (W.indicator (fun _ : Fin n → ℝ => (1 : ℝ))) (volume.restrict Y) :=
    (integrable_const 1).indicator hW
  have hb : ∀ y ∈ Y, 1 / (1 + m⁻¹ * g y)^N ≤
      1/R^N + W.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) y := by
    intro y hy
    have hbase : 1 ≤ 1 + m⁻¹ * g y := by
      have hnonneg := mul_nonneg (inv_nonneg.mpr hm0.le) (hgn y)
      linarith
    by_cases hw : y ∈ W
    · rw [Set.indicator_of_mem hw]
      have hle : 1 / (1 + m⁻¹ * g y)^N ≤ 1 := by
        apply (div_le_one (pow_pos (zero_lt_one.trans_le hbase) N)).mpr
        exact one_le_pow₀ hbase
      have hnonneg : 0 ≤ 1/R^N := by positivity
      linarith
    · rw [Set.indicator_of_notMem hw,add_zero]
      have hlt : R*m < g y := by
        exact lt_of_not_ge (fun h => hw ⟨hy,h⟩)
      have hge : R ≤ 1 + m⁻¹ * g y := by
        have hmul := (mul_le_mul_of_nonneg_left hlt.le (inv_nonneg.mpr hm0.le))
        have he : m⁻¹ * (R*m) = R := by field_simp
        rw [he] at hmul
        linarith
      exact one_div_le_one_div_of_le (pow_pos hR0 N)
        (pow_le_pow_left₀ hR0.le hge N)
  calc
    _ ≤ ∫ y in Y, 1/R^N + W.indicator (fun _ : Fin n → ℝ => (1 : ℝ)) y := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by
        have hy := hgn y
        positivity)
        ((integrable_const _).add hi)
      filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
      exact hb y hy
    _ = _ := by
      rw [integral_add (integrable_const _) hi, setIntegral_const, integral_indicator hW,
        Measure.restrict_restrict hW, Set.inter_eq_left.mpr hWY, setIntegral_const]
      simp only [smul_eq_mul,mul_one,Measure.real]
      ring

/-- Fixed homogeneous cubic form of the BHB gradient-window estimate. The
weight need not be nonnegative. No normalized bump, local Fourier estimate or
oscillatory bound is assumed. The original polynomial is retained throughout,
and the window lies in the doubled centered support box. -/
theorem exists_bound (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hcw : HasCompactSupport w)
    (a : Fin n → ℝ) (S : ℝ) (hS : 0 < S)
    (hsw : ∀ x ∈ tsupport w, ‖x-a‖ ≤ S) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (u : Fin n → ℝ) (R : ℝ), 1 ≤ R →
      ‖PolynomialOscillatory.integral F w t u‖ ≤
        C * (R^(-(N : ℝ)) + (volume (window F a S t u R)).toReal) := by
  obtain ⟨C,hC,hbound⟩ := exists_centered_integral_bound F hF w hw hcw a S hS hsw N
  let Y := Metric.closedBall a (2*S)
  let V := (volume Y).toReal
  let A := max 1 V
  refine ⟨C*A,?_,?_⟩
  · exact one_le_mul_of_one_le_of_one_le hC (le_max_left _ _)
  intro t u R hR
  let g : (Fin n → ℝ) → ℝ := fun y => ‖u-t • gradient F y‖
  have hg : Continuous g := by
    apply Continuous.norm
    apply continuous_const.sub
    apply continuous_const.smul
    exact continuous_pi fun i => (PolynomialCalculus.contDiff_eval (pderiv i F)).continuous
  have hsplit := integral_kernel_le Y (isCompact_closedBall _ _) g hg
    (fun _ => norm_nonneg _) (max 1 (Real.sqrt |t|)) R (le_max_left _ _) hR N
  have hset : Y ∩ {y | g y ≤ R * max 1 (Real.sqrt |t|)} = window F a S t u R := by
    ext y
    simp only [Y,Metric.mem_closedBall,dist_eq_norm,Set.mem_inter_iff,Set.mem_setOf_eq,
      g,window,norm_sub_rev]
  rw [hset] at hsplit
  have hpow : R^(-(N : ℝ)) = 1 / R^N := by
    rw [Real.rpow_neg (zero_lt_one.trans_le hR).le,Real.rpow_natCast,one_div]
  have h1 : 0 ≤ 1/R^N := by positivity
  have h2 : 0 ≤ (volume (window F a S t u R)).toReal := ENNReal.toReal_nonneg
  calc
    _ ≤ C * ∫ y in Y, 1 / (1 + scale t * g y)^N := hbound t u
    _ ≤ C * (V/R^N + (volume (window F a S t u R)).toReal) :=
      mul_le_mul_of_nonneg_left hsplit (zero_le_one.trans hC)
    _ ≤ C * (A*(1/R^N + (volume (window F a S t u R)).toReal)) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
      have hV : V ≤ A := le_max_right _ _
      have hA : 1 ≤ A := le_max_left _ _
      calc
        _ = V*(1/R^N) + (volume (window F a S t u R)).toReal := by ring
        _ ≤ A*(1/R^N) + A*(volume (window F a S t u R)).toReal :=
          add_le_add (mul_le_mul_of_nonneg_right hV h1)
            (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA h2)
        _ = _ := by ring
    _ = _ := by rw [hpow]; ring

end CubicTenVariables.CubicGradientWindow
