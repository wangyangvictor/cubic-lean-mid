import CubicTenVariables.OscillatoryLocalizationApplication
import CubicTenVariables.CubicChartLocalization
import CubicTenVariables.CubicPhysicalFrequencyDecay

/-! Source-sized cutoffs for the actual localized integral. Fixed constants in
frequency and gradient cutoffs are absorbed by using epsilon/2 and increasing
one threshold before all physical parameters. The localization region remains
the controlled enlarged chart, not the exact support of the weight.
The needed homogeneous cubic estimates are proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.OscillatoryLocalization
open MvPolynomial MeasureTheory
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

/-- Decay past the coefficient-one source frequency threshold. -/
theorem exists_source_frequency_bound (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → q ≤ P^2 →
      ∀ (θ : ℝ) (v : Fin n → ℝ),
      P^(2*ε)*(q/P)*max 1 (|θ| * P^3) ≤ ‖v‖ →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤
        C*‖v‖^(-(N : ℝ)) := by
  obtain ⟨C,K,P₀,hC,hK,hP₀,hb⟩ := CubicPhysicalFrequencyDecay.exists_frequency_bound hn
    F hF w hw hc hwn hs x₀ ρ hρ (ε/2) (by positivity) N
  refine ⟨C,max P₀ (K^ε⁻¹),hC,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP q hq hqP θ v hv
  have hPbase : P₀ ≤ P := (le_max_left _ _).trans hP
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one (hP₀.trans hPbase)
  have hKpow : K ≤ P^ε :=
    (Real.rpow_inv_le_iff_of_pos (zero_le_one.trans hK) hPpos.le hε).mp
      ((le_max_right _ _).trans hP)
  have hfactor : K*P^(2*(ε/2)) ≤ P^(2*ε) := by
    rw [show 2*(ε/2)=ε by ring]
    calc
      _ ≤ P^ε*P^ε := mul_le_mul_of_nonneg_right hKpow (Real.rpow_nonneg hPpos.le _)
      _ = _ := by rw [← Real.rpow_add hPpos]; congr 1; ring
  apply hb P hPbase q hq hqP θ v
  apply le_trans _ hv
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfactor (div_nonneg hq.le hPpos.le))
    (le_trans (by norm_num) (le_max_left _ _))

/-- Localization with coefficient one in the actual q-scaled gradient cutoff. -/
theorem exists_source_localization_exact (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → ∀ (θ : ℝ) (v : Fin n → ℝ),
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤
        C*(P^(-(N : ℝ))+(volume (sourceWindow F x₀ ρ P θ q v 1 ε)).toReal) := by
  exact CubicChartLocalization.exists_source_localization_exact
    hn F hF w hw hc hwn hs x₀ ρ hρ ε hε N

/-- The coarse source truncation |v| ≫ P³ throughout the circle-method
q and theta range. The constant is fixed before P,q,theta,v. -/
theorem exists_cubic_frequency_bound (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) :
    ∃ C K P₀ : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 1 ≤ q → q ≤ P^2 →
      ∀ (θ : ℝ) (v : Fin n → ℝ), |θ| ≤ 1/(q*P) → K*P^3 ≤ ‖v‖ →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤
        C*‖v‖^(-(N : ℝ)) := by
  obtain ⟨C,K,P₀,hC,hK,hP₀,hb⟩ := CubicPhysicalFrequencyDecay.exists_frequency_bound hn
    F hF w hw hc hwn hs x₀ ρ hρ 1 (by norm_num) N
  refine ⟨C,K,P₀,hC,hK,hP₀,?_⟩
  intro P hP q hq hqP θ v hθ hv
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one (hP₀.trans hP)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hsmall : (q/P)*max 1 (|θ| * P^3) ≤ P := by
    rcases le_total (|θ| * P^3) 1 with h | h
    · rw [max_eq_left h,mul_one]
      exact (div_le_iff₀ hPpos).mpr (by nlinarith [hqP])
    · rw [max_eq_right h]
      calc
        _ ≤ (q/P)*((1/(q*P))*P^3) := by gcongr
        _ = P := by field_simp
  apply hb P hP q hqpos hqP θ v
  apply le_trans _ hv
  calc
    K*P^(2*(1:ℝ))*(q/P)*max 1 (|θ| * P^3) =
        (K*P^2)*((q/P)*max 1 (|θ| * P^3)) := by norm_num; ring
    _ ≤ (K*P^2)*P := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = K*P^3 := by ring

end CubicTenVariables.OscillatoryLocalization
