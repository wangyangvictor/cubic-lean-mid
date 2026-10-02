import CubicTenVariables.OscillatoryLocalizationWindow

/-! Asymptotic physical localization, retaining the explicit fixed enlarged
chart. Every constant precedes the varying physical scale and frequency. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.OscillatoryLocalization
open MvPolynomial MeasureTheory
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

/-- A sufficiently high order in the cited free-R estimate absorbs any fixed
Jacobian power after setting R=P^ε. -/
theorem scale_decay (P ε : ℝ) (hP : 1 ≤ P) (a N M : ℕ)
    (hM : (a : ℝ)+(N : ℝ) ≤ ε*(M : ℝ)) :
    P^a * (P^ε)^(-(M : ℝ)) ≤ P^(-(N : ℝ)) := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  rw [← Real.rpow_natCast P a,← Real.rpow_mul hP0.le,← Real.rpow_add hP0]
  exact Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)

theorem exists_decay_order (ε : ℝ) (hε : 0 < ε) (a N : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ (a : ℝ)+(N : ℝ) ≤ ε*(M : ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 (((a : ℝ)+(N : ℝ))/ε))
  refine ⟨M,?_,?_⟩
  · have hm : (1 : ℝ) < M := lt_of_le_of_lt (le_max_left _ _) hM
    exact_mod_cast hm.le
  · have hm := lt_of_le_of_lt (le_max_right _ _) hM
    exact (div_le_iff₀ hε).mp hm.le |>.trans_eq (mul_comm _ _)

/-- The final decay remainder is P^-N. The window uses the actual physical
first derivatives; its fixed coefficient H and chart radius are exposed. -/
theorem exists_localization_bound (lit : Literature.BrowningHeathBrown2009Lemma6)
    (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ H C P₀ : ℝ, 1 ≤ H ∧ 1 ≤ C ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ (θ : ℝ) (β : Fin n → ℝ),
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ β‖ ≤
        C * (P^(-(N : ℝ)) +
          (volume (physicalWindow F x₀ ρ P θ β H (P^ε))).toReal) := by
  obtain ⟨M,hM,hMN⟩ := exists_decay_order ε hε n N
  obtain ⟨H,hH,h⟩ := localization_physical lit hn F hF w hw hc hwn hs x₀ ρ hρ
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

/-- The displayed physical radius has the source scale, with an explicit
fixed factor sqrt(H)/ρ. No support restriction is used here. -/
theorem physical_radius_le (P ρ H θ ε : ℝ) (hP : 0 < P) (hρ : 0 < ρ)
    (hH : 1 ≤ H) :
    (P^ε/(P*ρ))*max 1 (Real.sqrt (|θ*P^3| * H)) ≤
      (Real.sqrt H/ρ)*(P^ε/P)*max 1 (Real.sqrt (|θ| * P^3)) := by
  have hH0 : 0 ≤ H := by linarith
  have hroot : 1 ≤ Real.sqrt H := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hH
  have habs : |θ*P^3|=|θ| * P^3 := by rw [abs_mul,abs_of_pos (pow_pos hP _)]
  have hs : max 1 (Real.sqrt (|θ*P^3| * H)) ≤
      Real.sqrt H*max 1 (Real.sqrt (|θ| * P^3)) := by
    rw [habs,Real.sqrt_mul (mul_nonneg (abs_nonneg _) (pow_nonneg hP.le _))]
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le hroot (le_max_left _ _)
    · simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (le_max_right 1 (Real.sqrt (|θ| * P^3))) (Real.sqrt_nonneg H)
  calc
    _ ≤ (P^ε/(P*ρ))*(Real.sqrt H*max 1 (Real.sqrt (|θ| * P^3))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end CubicTenVariables.OscillatoryLocalization
