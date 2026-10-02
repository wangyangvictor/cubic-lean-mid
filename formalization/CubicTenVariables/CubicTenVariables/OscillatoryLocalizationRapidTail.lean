import CubicTenVariables.OscillatoryLocalizationTail
import CubicTenVariables.CubicPhysicalFrequencyDecay

/-! Simultaneous arbitrary physical-scale and frequency decay from the proved
homogeneous cubic estimate. The fixed chart and weight are unchanged, and
all constants precede the physical parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace CubicTenVariables.OscillatoryLocalization
open MvPolynomial MeasureTheory
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

/-- The normalized decay order n+N+A absorbs the physical Jacobian, the
frequency conversion, and a retained arbitrary factor P^-A. -/
theorem exists_rapid_frequency_bound (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (A N : ℕ) :
    ∃ C K P₀ : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → q ≤ P^2 →
      ∀ (θ : ℝ) (v : Fin n → ℝ),
      K*P^(2*ε)*(q/P)*max 1 (|θ| * P^3) ≤ ‖v‖ →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤
        C*P^(-(A : ℝ))*‖v‖^(-(N : ℝ)) := by
  exact CubicPhysicalFrequencyDecay.exists_rapid_frequency_bound
    hn F hF w hw hc hwn hs x₀ ρ hρ ε hε A N

/-- The coefficient-one source frequency cutoff, with the same arbitrary
physical-scale decay retained. Its larger P₀ is still fixed before P,q,θ,v. -/
theorem exists_source_rapid_frequency_bound (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (A N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → q ≤ P^2 →
      ∀ (θ : ℝ) (v : Fin n → ℝ),
      P^(2*ε)*(q/P)*max 1 (|θ| * P^3) ≤ ‖v‖ →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤
        C*P^(-(A : ℝ))*‖v‖^(-(N : ℝ)) := by
  obtain ⟨C,K,P₀,hC,hK,hP₀,hb⟩ := exists_rapid_frequency_bound hn
    F hF w hw hc hwn hs x₀ ρ hρ (ε/2) (by positivity) A N
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

end CubicTenVariables.OscillatoryLocalization
