import CubicTenVariables.CubicGradientWindow
import CubicTenVariables.OscillatoryLocalizationApplication

/-! The actual homogeneous cubic estimate in a fixed affine chart. The
translation and dilation are carried through the original integral and its
window; the chart polynomial itself need not be homogeneous. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.CubicChartLocalization
open MvPolynomial MeasureTheory HessianTheorem11 OscillatoryLocalization
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

private theorem physical_window_one_finite (F : MvPolynomial (Fin n) ℝ)
    (x₀ : Fin n → ℝ) (ρ t : ℝ) (u : Fin n → ℝ) (R : ℝ) :
    volume (physicalWindow F x₀ ρ 1 t u 1 R) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (show volume (Metric.closedBall x₀ (2*ρ)) < ⊤ from measure_closedBall_lt_top).ne
  apply measure_mono
  intro x hx
  simpa only [Metric.mem_closedBall,dist_eq_norm,inv_one,one_smul] using hx.1

/-- The normalized chart window, with height constant one and threshold
`max 1 ρ`. Constants precede every phase, frequency and window parameter. -/
theorem normalized_chart_bound (F : MvPolynomial (Fin n) ℝ)
    (hF : F.IsHomogeneous 3) (w : (Fin n → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (u : Fin n → ℝ) (R : ℝ), max 1 ρ ≤ R →
      ‖PolynomialOscillatory.integral (chartPolynomial F x₀ ρ) w t u‖ ≤
        C * (R^(-(N : ℝ)) +
          (volume (PolynomialOscillatory.window (chartPolynomial F x₀ ρ)
            1 1 t u R)).toReal) := by
  have hsupport : ∀ x ∈ tsupport (chartWeight w x₀ ρ), ‖x-x₀‖ ≤ ρ := by
    intro x hx
    have hb := chartWeight_support w hs x₀ ρ x hx
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)] at hb
    have hh := mul_le_mul_of_nonneg_left hb hρ.le
    simpa [hρ.ne'] using hh
  obtain ⟨A,hA,hbound⟩ := CubicGradientWindow.exists_bound F hF (chartWeight w x₀ ρ)
    (chartWeight_smooth w hw x₀ ρ) (chartWeight_compact w hc x₀ ρ hρ.ne')
    x₀ ρ hρ hsupport N
  let m : ℝ := max 1 ρ
  let K : ℝ := max 1 (m^N/ρ^n)
  have hm : 0 < m := zero_lt_one.trans_le (le_max_left _ _)
  have hK : 1 ≤ K := le_max_left _ _
  have hpow : 0 < ρ^n := pow_pos hρ n
  have hfactor : m^N ≤ ρ^n*K := by
    simpa only [mul_comm] using
      (div_le_iff₀ hpow).mp (show m^N/ρ^n ≤ K from le_max_right _ _)
  refine ⟨A*K,one_le_mul_of_one_le_of_one_le hA hK,?_⟩
  intro t u R hR
  change m ≤ R at hR
  have hR0 : 0 < R := hm.trans_le hR
  have hRm : 1 ≤ R/m := (le_div_iff₀ hm).mpr (by simpa only [one_mul] using hR)
  have hsub : CubicGradientWindow.window F x₀ ρ t (ρ⁻¹ • u) (R/m) ⊆
      physicalWindow F x₀ ρ 1 t (ρ⁻¹ • u) 1 R := by
    intro x hx
    refine ⟨by simpa using hx.1,?_⟩
    have hd : R/m ≤ R/ρ := div_le_div_of_nonneg_left hR0.le hρ (le_max_right _ _)
    have he : (fun i => t*eval x (pderiv i F)-(ρ⁻¹ • u) i) =
        t • gradient F x-ρ⁻¹ • u := by rfl
    change ‖(fun i => t*eval x (pderiv i F)-(ρ⁻¹ • u) i)‖ ≤ _
    rw [he]
    simpa only [one_mul,one_pow,mul_one] using hx.2.trans
      (mul_le_mul_of_nonneg_right hd (le_trans zero_le_one (le_max_left _ _)))
  have hvol := ENNReal.toReal_mono
    (physical_window_one_finite F x₀ ρ t (ρ⁻¹ • u) R) (measure_mono hsub)
  have hmeasure := physicalWindow_measure F hF x₀ ρ 1 hρ (by norm_num)
    t (ρ⁻¹ • u) 1 R
  simp only [one_mul,one_pow,mul_one,smul_smul,mul_inv_cancel₀ hρ.ne',one_smul] at hmeasure
  rw [hmeasure] at hvol
  have hi := norm_scaledIntegral_chart F hF w x₀ ρ 1 hρ (by norm_num)
    t (ρ⁻¹ • u)
  simp only [scaledIntegral,inv_one,one_smul,one_mul,one_pow,mul_one,smul_smul,
    mul_inv_cancel₀ hρ.ne'] at hi
  have hrpow : (R/m)^(-(N : ℝ)) = m^N*R^(-(N : ℝ)) := by
    rw [Real.rpow_neg (div_pos hR0 hm).le,Real.rpow_natCast,div_pow,
      Real.rpow_neg hR0.le,Real.rpow_natCast]
    field_simp
  have hp : 0 ≤ R^(-(N : ℝ)) := Real.rpow_nonneg hR0.le _
  have hv : 0 ≤ (volume (PolynomialOscillatory.window (chartPolynomial F x₀ ρ)
      1 1 t u R)).toReal := ENNReal.toReal_nonneg
  have hb := hbound t (ρ⁻¹ • u) (R/m) hRm
  rw [hi,hrpow] at hb
  apply (mul_le_mul_iff_right₀ hpow).mp
  calc
    ρ^n * ‖PolynomialOscillatory.integral (chartPolynomial F x₀ ρ) w t u‖
        ≤ A*(m^N*R^(-(N : ℝ)) +
          ρ^n*(volume (PolynomialOscillatory.window (chartPolynomial F x₀ ρ)
            1 1 t u R)).toReal) :=
      hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hvol) (zero_le_one.trans hA))
    _ ≤ ρ^n*(A*K*(R^(-(N : ℝ)) +
          (volume (PolynomialOscillatory.window (chartPolynomial F x₀ ρ)
            1 1 t u R)).toReal)) := by
      have hfirst := mul_le_mul_of_nonneg_right hfactor hp
      have hsecond : ρ^n * (volume (PolynomialOscillatory.window
          (chartPolynomial F x₀ ρ) 1 1 t u R)).toReal ≤
          (ρ^n*K) * (volume (PolynomialOscillatory.window
          (chartPolynomial F x₀ ρ) 1 1 t u R)).toReal := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hK hpow.le) hv
      have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (zero_le_one.trans hA)
      convert hh using 1; ring

/-- The full existing chart-localization conclusion for an actual homogeneous
cubic, with its Jacobian and all parameter quantifiers unchanged. -/
theorem localization_on_chart (_hn : 1 ≤ n)
    (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (_hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ N : ℕ, 1 ≤ N → ∃ C R₀ : ℝ, 1 ≤ C ∧ 1 ≤ R₀ ∧
      ∀ P : ℝ, 0 < P → ∀ (θ : ℝ) (β : Fin n → ℝ) (R : ℝ), R₀ ≤ R →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ β‖ ≤
        (P*ρ)^n * C * (R^(-(N : ℝ)) +
          (volume (PolynomialOscillatory.window (chartPolynomial F x₀ ρ)
            1 H (θ*P^3) ((P*ρ) • β) R)).toReal) := by
  refine ⟨1,le_rfl,?_⟩
  intro N _hN
  obtain ⟨C,hC,hbound⟩ := normalized_chart_bound F hF w hw hc hs x₀ ρ hρ N
  refine ⟨C,max 1 ρ,hC,le_max_left _ _,?_⟩
  intro P hP θ β R hR
  rw [norm_scaledIntegral_chart F hF w x₀ ρ P hρ hP θ β]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (hbound (θ*P^3) ((P*ρ) • β) R hR) (pow_nonneg (mul_pos hP hρ).le n)

private theorem localization_physical (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ N : ℕ, 1 ≤ N → ∃ C R₀ : ℝ, 1 ≤ C ∧ 1 ≤ R₀ ∧
      ∀ P : ℝ, 0 < P → ∀ (θ : ℝ) (β : Fin n → ℝ) (R : ℝ), R₀ ≤ R →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ β‖ ≤
        C * ((P*ρ)^n*R^(-(N : ℝ)) +
          (volume (physicalWindow F x₀ ρ P θ β H R)).toReal) := by
  obtain ⟨H,hH,h⟩ := localization_on_chart hn F hF w hw hc hwn hs x₀ ρ hρ
  refine ⟨H,hH,?_⟩
  intro N hN
  obtain ⟨C,R₀,hC,hR₀,hb⟩ := h N hN
  refine ⟨C,R₀,hC,hR₀,?_⟩
  intro P hP θ β R hR
  rw [physicalWindow_measure F hF x₀ ρ P hρ hP]
  convert hb P hP θ β R hR using 1; ring

private theorem exists_localization_bound (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ H C P₀ : ℝ, 1 ≤ H ∧ 1 ≤ C ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ (θ : ℝ) (β : Fin n → ℝ),
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ β‖ ≤
        C * (P^(-(N : ℝ)) +
          (volume (physicalWindow F x₀ ρ P θ β H (P^ε))).toReal) := by
  obtain ⟨M,hM,hMN⟩ := exists_decay_order ε hε n N
  obtain ⟨H,hH,h⟩ := localization_physical hn F hF w hw hc hwn hs x₀ ρ hρ
  obtain ⟨C,R₀,hC,hR₀,hb⟩ := h M hM
  let A : ℝ := max 1 (ρ^n)
  refine ⟨H,C*A,max 1 (R₀^ε⁻¹),hH,?_,le_max_left _ _,?_⟩
  · exact one_le_mul_of_one_le_of_one_le hC (le_max_left _ _)
  intro P hP θ β
  have hP1 : 1 ≤ P := (le_max_left _ _).trans hP
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hR : R₀ ≤ P^ε :=
    (Real.rpow_inv_le_iff_of_pos (by linarith : 0 ≤ R₀) hP0.le hε).mp
      ((le_max_right _ _).trans hP)
  have hd := scale_decay P ε hP1 n N M hMN
  have hpow : 0 ≤ P^(-(N : ℝ)) := Real.rpow_nonneg hP0.le _
  have hv : 0 ≤ (volume (physicalWindow F x₀ ρ P θ β H (P^ε))).toReal :=
    ENNReal.toReal_nonneg
  have hρn : 0 ≤ ρ^n := pow_nonneg hρ.le n
  have ha : 1 ≤ A := le_max_left _ _
  have haρ : ρ^n ≤ A := le_max_right _ _
  calc
    _ ≤ C*((P*ρ)^n*(P^ε)^(-(M : ℝ))+
      (volume (physicalWindow F x₀ ρ P θ β H (P^ε))).toReal) := hb P hP0 θ β _ hR
    _ ≤ C*(A*P^(-(N : ℝ))+A*
      (volume (physicalWindow F x₀ ρ P θ β H (P^ε))).toReal) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply add_le_add
        · calc
            _ = ρ^n*(P^n*(P^ε)^(-(M : ℝ))) := by rw [mul_pow]; ring
            _ ≤ ρ^n*P^(-(N : ℝ)) := mul_le_mul_of_nonneg_left hd hρn
            _ ≤ A*P^(-(N : ℝ)) := mul_le_mul_of_nonneg_right haρ hpow
        · exact le_mul_of_one_le_left hv ha
    _ = _ := by ring

private theorem exists_source_localization_bound (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C K P₀ : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → ∀ (θ : ℝ) (v : Fin n → ℝ),
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤
        C * (P^(-(N : ℝ)) + (volume (sourceWindow F x₀ ρ P θ q v K ε)).toReal) := by
  obtain ⟨H,C,P₀,hH,hC,hP₀,hb⟩ :=
    exists_localization_bound hn F hF w hw hc hwn hs x₀ ρ hρ ε hε N
  refine ⟨C,max 1 (Real.sqrt H/ρ),P₀,hC,le_max_left _ _,hP₀,?_⟩
  intro P hP q hq θ v
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one (hP₀.trans hP)
  apply le_trans (hb P hP θ (q⁻¹ • v))
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply add_le_add_right
  apply ENNReal.toReal_mono (sourceWindow_measure_ne_top F x₀ ρ P θ q v _ ε hPpos)
  exact measure_mono (physicalWindow_subset_sourceWindow F x₀ ρ P θ q H _ ε v
    hρ hPpos hq hH (le_max_right _ _))

/-- The coefficient-one source gradient window for a homogeneous cubic,
with no oscillatory estimate supplied as a premise. -/
theorem exists_source_localization_exact (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → ∀ (θ : ℝ) (v : Fin n → ℝ),
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤
        C*(P^(-(N : ℝ))+(volume (sourceWindow F x₀ ρ P θ q v 1 ε)).toReal) := by
  obtain ⟨C,K,P₀,hC,hK,hP₀,hb⟩ := exists_source_localization_bound hn
    F hF w hw hc hwn hs x₀ ρ hρ (ε/2) (by positivity) N
  refine ⟨C,max P₀ (K^((ε/2)⁻¹)),hC,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP q hq θ v
  have hPbase : P₀ ≤ P := (le_max_left _ _).trans hP
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one (hP₀.trans hPbase)
  have hKpow : K ≤ P^(ε/2) :=
    (Real.rpow_inv_le_iff_of_pos (zero_le_one.trans hK) hPpos.le (half_pos hε)).mp
      ((le_max_right _ _).trans hP)
  have hfactor : K*P^(ε/2) ≤ P^ε := by
    calc
      _ ≤ P^(ε/2)*P^(ε/2) :=
        mul_le_mul_of_nonneg_right hKpow (Real.rpow_nonneg hPpos.le _)
      _ = _ := by rw [← Real.rpow_add hPpos]; congr 1; ring
  have hsub : sourceWindow F x₀ ρ P θ q v K (ε/2) ⊆
      sourceWindow F x₀ ρ P θ q v 1 ε := by
    intro x hx
    refine ⟨hx.1,hx.2.trans ?_⟩
    dsimp
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfactor (div_nonneg hq.le hPpos.le))
      (le_trans (by norm_num) (le_max_left _ _))
  apply le_trans (hb P hPbase q hq θ v)
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  apply add_le_add_right
  exact ENNReal.toReal_mono
    (sourceWindow_measure_ne_top F x₀ ρ P θ q v 1 ε hPpos) (measure_mono hsub)

end CubicTenVariables.CubicChartLocalization
