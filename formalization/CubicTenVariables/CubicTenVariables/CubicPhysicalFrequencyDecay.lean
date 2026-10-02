import CubicTenVariables.CubicCenteredFrequencyDecay
import CubicTenVariables.OscillatoryLocalizationApplication

/-! Physical frequency decay for the original homogeneous cubic and its
actual chart weight. The Jacobian and frequency rescaling are explicit;
no generic oscillatory-integral literature premise is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicPhysicalFrequencyDecay
open MvPolynomial MeasureTheory HessianTheorem11 OscillatoryLocalization
open scoped ContDiff
variable {n : ℕ}

theorem norm_scaledIntegral_original (F : MvPolynomial (Fin n) ℝ)
    (hF : F.IsHomogeneous 3) (W : (Fin n → ℝ) → ℝ)
    (P : ℝ) (hP : 0 < P) (θ : ℝ) (β : Fin n → ℝ) :
    ‖scaledIntegral F W P θ β‖ =
      P^n * ‖PolynomialOscillatory.integral F W (θ*P^3) (P • β)‖ := by
  have hW : chartWeight W (0 : Fin n → ℝ) 1 = W := by
    funext x
    simp [chartWeight]
  simpa [hW,chartPolynomial] using
    norm_scaledIntegral_chart F hF W 0 1 P (by norm_num) hP θ β

theorem exists_rapid_frequency_bound
    (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (A N : ℕ) :
    ∃ C K P₀ : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → q ≤ P^2 →
      ∀ (θ : ℝ) (v : Fin n → ℝ),
      K*P^(2*ε)*(q/P)*max 1 (|θ| * P^3) ≤ ‖v‖ →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤
        C*P^(-(A : ℝ))*‖v‖^(-(N : ℝ)) := by
  let W := chartWeight w x₀ ρ
  have hsupport : ∀ x ∈ tsupport W, ‖x-x₀‖ ≤ ρ := by
    intro x hx
    have h := chartWeight_support w hs x₀ ρ x hx
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)] at h
    have hb := mul_le_mul_of_nonneg_left h hρ.le
    simpa only [mul_one,← mul_assoc,mul_inv_cancel₀ hρ.ne',one_mul] using hb
  obtain ⟨C,K,P₀,hC,hK,hP₀,hb⟩ :=
    CubicCenteredFrequencyDecay.exists_normalized_frequency_bound F hF W
      (chartWeight_smooth w hw x₀ ρ) (chartWeight_compact w hc x₀ ρ hρ.ne')
      x₀ ρ hρ hsupport ε hε (n+N+A) N
  refine ⟨C,K,P₀,hC,hK,hP₀,?_⟩
  intro P hP q hq hqP θ v hv
  have hP1 : 1 ≤ P := hP₀.trans hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP1
  let u : Fin n → ℝ := P • (q⁻¹ • v)
  have hunorm : ‖u‖=(P/q)*‖v‖ := by
    dsimp [u]
    rw [smul_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    rfl
  have ht : |θ*P^3|=|θ| * P^3 := by rw [abs_mul,abs_of_pos (pow_pos hPpos _)]
  have hcut : K*P^(2*ε)*max 1 |θ*P^3| ≤ ‖u‖ := by
    rw [hunorm,ht]
    have hh := mul_le_mul_of_nonneg_left hv (div_nonneg hPpos.le hq.le)
    convert hh using 1
    field_simp
  have hnormu : 0 < ‖u‖ := lt_of_lt_of_le (by positivity) hcut
  have hnormv : 0 < ‖v‖ := by
    rw [hunorm] at hnormu
    exact (mul_pos_iff_of_pos_left (div_pos hPpos hq)).mp hnormu
  have hI := hb P hP (θ*P^3) u hcut
  have hcancel : P^n*P^(-((n+N+A : ℕ) : ℝ)) =
      P^(-(A : ℝ))*P^(-(N : ℝ)) := by
    rw [Real.rpow_neg hPpos.le,Real.rpow_natCast,
      Real.rpow_neg hPpos.le,Real.rpow_natCast,
      Real.rpow_neg hPpos.le,Real.rpow_natCast,pow_add,pow_add]
    field_simp
  have hPU : ‖v‖ ≤ P*‖u‖ := by
    rw [hunorm]
    have hcoeff : 1 ≤ P*(P/q) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hq).mpr
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg v)
    simpa only [one_mul,mul_assoc] using hh
  have hdecay : P^(-(N : ℝ))*‖u‖^(-(N : ℝ)) ≤ ‖v‖^(-(N : ℝ)) := by
    rw [← Real.mul_rpow hPpos.le hnormu.le]
    exact Real.rpow_le_rpow_of_nonpos hnormv hPU (neg_nonpos.mpr (Nat.cast_nonneg N))
  rw [norm_scaledIntegral_original F hF _ P hPpos]
  calc
    _ ≤ P^n*(C*P^(-((n+N+A : ℕ) : ℝ))*‖u‖^(-(N : ℝ))) :=
      mul_le_mul_of_nonneg_left hI (pow_nonneg hPpos.le n)
    _ = (C*P^(-(A : ℝ)))*(P^(-(N : ℝ))*‖u‖^(-(N : ℝ))) := by
      calc
        _ = C*(P^n*P^(-((n+N+A : ℕ) : ℝ)))*‖u‖^(-(N : ℝ)) := by ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

theorem exists_frequency_bound
    (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C K P₀ : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → q ≤ P^2 →
      ∀ (θ : ℝ) (v : Fin n → ℝ),
      K*P^(2*ε)*(q/P)*max 1 (|θ| * P^3) ≤ ‖v‖ →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤ C*‖v‖^(-(N : ℝ)) := by
  simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one] using
    exists_rapid_frequency_bound hn F hF w hw hc hwn hs x₀ ρ hρ ε hε 0 N

end CubicTenVariables.CubicPhysicalFrequencyDecay
