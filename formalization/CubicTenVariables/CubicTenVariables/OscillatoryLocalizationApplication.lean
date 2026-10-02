import CubicTenVariables.OscillatoryLocalizationTail
import CubicTenVariables.LocalizedSums

/-! Literal arithmetic-frequency windows and actual counting weights on a
controlled fixed chart. The enlarged region stays in the chosen neighborhood;
it is not asserted to equal the closed support of the weight. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.OscillatoryLocalization
open MvPolynomial MeasureTheory
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

def sourceWindow (F : MvPolynomial (Fin n) ℝ) (x₀ : Fin n → ℝ)
    (ρ P θ q : ℝ) (v : Fin n → ℝ) (K ε : ℝ) : Set (Fin n → ℝ) :=
  {x | ‖P⁻¹ • x-x₀‖ ≤ 2*ρ ∧
    ‖(fun i => q*θ*eval x (pderiv i F)-v i)‖ ≤
      K*P^ε*(q/P)*max 1 (Real.sqrt (|θ| * P^3))}

theorem sourceWindow_measure_ne_top (F : MvPolynomial (Fin n) ℝ) (x₀ : Fin n → ℝ)
    (ρ P θ q : ℝ) (v : Fin n → ℝ) (K ε : ℝ) (hP : 0 < P) :
    volume (sourceWindow F x₀ ρ P θ q v K ε) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (show volume (Metric.closedBall (0 : Fin n → ℝ) (P*(2*ρ+‖x₀‖))) < ⊤ from
      measure_closedBall_lt_top).ne
  apply measure_mono
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  have ht := norm_le_norm_sub_add (P⁻¹ • x) x₀
  have hb : ‖P⁻¹ • x‖ ≤ 2*ρ+‖x₀‖ := by have hh := hx.1; linarith
  have he : ‖x‖=P*‖P⁻¹ • x‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hP)]
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hb hP.le

theorem physicalWindow_subset_sourceWindow (F : MvPolynomial (Fin n) ℝ)
    (x₀ : Fin n → ℝ) (ρ P θ q H K ε : ℝ) (v : Fin n → ℝ)
    (hρ : 0 < ρ) (hP : 0 < P) (hq : 0 < q) (hH : 1 ≤ H)
    (hK : Real.sqrt H/ρ ≤ K) :
    physicalWindow F x₀ ρ P θ (q⁻¹ • v) H (P^ε) ⊆
      sourceWindow F x₀ ρ P θ q v K ε := by
  intro x hx
  refine ⟨hx.1,?_⟩
  have he : (fun i => q*θ*eval x (pderiv i F)-v i) =
      q • (fun i => θ*eval x (pderiv i F)-(q⁻¹ • v) i) := by
    funext i
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hq]
  calc
    _ ≤ q*((P^ε/(P*ρ))*max 1 (Real.sqrt (|θ*P^3| * H))) :=
      mul_le_mul_of_nonneg_left hx.2 hq.le
    _ ≤ q*((Real.sqrt H/ρ)*(P^ε/P)*max 1 (Real.sqrt (|θ| * P^3))) :=
      mul_le_mul_of_nonneg_left (physical_radius_le P ρ H θ ε hP hρ hH) hq.le
    _ = (Real.sqrt H/ρ)*P^ε*(q/P)*max 1 (Real.sqrt (|θ| * P^3)) := by ring
    _ ≤ _ := by gcongr

theorem sourceWindow_subset_neighborhood (F : MvPolynomial (Fin n) ℝ)
    (x₀ : Fin n → ℝ) (ρ P θ q : ℝ) (v : Fin n → ℝ) (K ε : ℝ)
    (hρ : 0 < ρ) (_hP : 0 < P) (U : Set (Fin n → ℝ))
    (hU : ∀ y : Fin n → ℝ, ‖y‖ ≤ 2 → chartPoint x₀ ρ y ∈ U) :
    ∀ x ∈ sourceWindow F x₀ ρ P θ q v K ε, P⁻¹ • x ∈ U := by
  intro x hx
  let y := ρ⁻¹ • (P⁻¹ • x-x₀)
  have hy : ‖y‖ ≤ 2 := by
    dsimp [y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
    have hh := mul_le_mul_of_nonneg_left hx.1 (inv_nonneg.mpr hρ.le)
    exact hh.trans_eq (by field_simp)
  have he : chartPoint x₀ ρ y=P⁻¹ • x := by simp [chartPoint,y,hρ.ne']
  rw [← he]
  exact hU y hy

/-- Literal qθ∇F−v localization with P^-N remainder, uniform before all
q>0, P≥P₀, θ and v. The source q≤P² and θ-range are therefore permitted. -/
theorem exists_source_localization_bound (lit : Literature.BrowningHeathBrown2009Lemma6)
    (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C K P₀ : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → ∀ (θ : ℝ) (v : Fin n → ℝ),
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤
        C * (P^(-(N : ℝ)) + (volume (sourceWindow F x₀ ρ P θ q v K ε)).toReal) := by
  obtain ⟨H,C,P₀,hH,hC,hP₀,hb⟩ :=
    exists_localization_bound lit hn F hF w hw hc hwn hs x₀ ρ hρ ε hε N
  refine ⟨C,max 1 (Real.sqrt H/ρ),P₀,hC,le_max_left _ _,hP₀,?_⟩
  intro P hP q hq θ v
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one (hP₀.trans hP)
  apply le_trans (hb P hP θ (q⁻¹ • v))
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply add_le_add_right
  apply ENNReal.toReal_mono (sourceWindow_measure_ne_top F x₀ ρ P θ q v _ ε hPpos)
  exact measure_mono (physicalWindow_subset_sourceWindow F x₀ ρ P θ q H _ ε v
    hρ hPpos hq hH (le_max_right _ _))

def chartHomeomorph (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : ρ ≠ 0) :
    (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  (Homeomorph.smulOfNeZero ρ hρ).trans (Homeomorph.addLeft x₀)

theorem chartWeight_smooth (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w)
    (x₀ : Fin n → ℝ) (ρ : ℝ) : ContDiff ℝ ∞ (chartWeight w x₀ ρ) := by
  unfold chartWeight
  fun_prop

theorem chartWeight_compact (w : (Fin n → ℝ) → ℝ) (hc : HasCompactSupport w)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : ρ ≠ 0) : HasCompactSupport (chartWeight w x₀ ρ) := by
  convert hc.comp_homeomorph (chartHomeomorph x₀ ρ hρ).symm using 1
  ext x
  simp [chartHomeomorph,chartWeight,Homeomorph.addLeft_symm,sub_eq_add_neg,add_comm]

theorem chartWeight_support (w : (Fin n → ℝ) → ℝ)
    (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1) (x₀ : Fin n → ℝ) (ρ : ℝ) :
    ∀ x ∈ tsupport (chartWeight w x₀ ρ), ‖ρ⁻¹ • (x-x₀)‖ ≤ 1 := by
  intro x hx
  exact hs _ (tsupport_comp_subset_preimage w (f := fun x => ρ⁻¹ • (x-x₀)) (by fun_prop) hx)

/-- The actual physical integrand is integrable for each fixed frequency;
no conclusion here relies on the totalized integral of a nonintegrable map. -/
theorem scaled_integrand_integrable (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (P θ : ℝ) (β : Fin n → ℝ) (hP : P ≠ 0) :
    Integrable (fun x : Fin n → ℝ => (w (P⁻¹ • x) : ℂ)*Complex.exp
      (2*(Real.pi : ℂ)*Complex.I*((θ*eval x F-∑ i,β i*x i : ℝ) : ℂ))) := by
  have hwc : HasCompactSupport (fun x => w (P⁻¹ • x)) := by
    have hh := chartWeight_compact w hc (0 : Fin n → ℝ) P hP
    change HasCompactSupport (fun x => w (P⁻¹ • (x-0))) at hh
    simpa only [sub_zero] using hh
  apply Continuous.integrable_of_hasCompactSupport
  · have hF := F.continuous_eval
    have hweight := hw.continuous
    fun_prop
  · exact (hwc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).mul_right

/-- A genuine counting weight and its enlarged chart fit simultaneously in
any prescribed neighborhood of the chosen nonzero real point. -/
theorem exists_counting_weight_chart (x₀ : Fin n → ℝ) (hx₀ : x₀ ≠ 0)
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 x₀) :
    ∃ (ρ : ℝ) (w : (Fin n → ℝ) → ℝ) (W : SmoothCountingWeight x₀),
      0 < ρ ∧ ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      (∀ x, 0 ≤ w x) ∧ (∀ x ∈ tsupport w, ‖x‖ ≤ 1) ∧
      W.weight=chartWeight w x₀ ρ ∧ tsupport W.weight ⊆ U ∧
      ∀ y : Fin n → ℝ, ‖y‖ ≤ 2 → chartPoint x₀ ρ y ∈ U := by
  have hxpos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  let V := U ∩ Metric.ball x₀ (‖x₀‖/2)
  obtain ⟨ρ,hρ,hchart⟩ := exists_chart_inside x₀ V
    (Filter.inter_mem hU (Metric.ball_mem_nhds x₀ (half_pos hxpos)))
  obtain ⟨w,hs,hc,hw,hbounds,hw0⟩ :=
    exists_smooth_tsupport_subset (Metric.ball_mem_nhds (0 : Fin n → ℝ) zero_lt_one)
  have hs1 : ∀ x ∈ tsupport w, ‖x‖ ≤ 1 := by
    intro x hx
    exact (by simpa using Metric.mem_ball.mp (hs hx) : ‖x‖ < 1).le
  have hsu : tsupport (chartWeight w x₀ ρ) ⊆ V := by
    intro x hx
    let y := ρ⁻¹ • (x-x₀)
    have hy : ‖y‖ ≤ 2 := (chartWeight_support w hs1 x₀ ρ x hx).trans (by norm_num)
    have he : chartPoint x₀ ρ y=x := by simp [chartPoint,y,hρ.ne']
    rw [← he]
    exact hchart y hy
  obtain ⟨A,hA⟩ := exists_nat_ge (‖x₀‖+‖x₀‖/2)
  let W : SmoothCountingWeight x₀ := {
    weight := chartWeight w x₀ ρ
    boxRadius := A
    smooth := chartWeight_smooth w hw x₀ ρ
    compact := chartWeight_compact w hc x₀ ρ hρ.ne'
    bounds := fun x => hbounds (Set.mem_range_self _)
    value_at := by simpa [chartWeight] using hw0
    origin_excluded := by
      intro hz
      have hh := Metric.mem_ball.mp (hsu hz).2
      simp only [dist_zero_left] at hh
      linarith
    supported := by
      intro x hx i
      have hh := Metric.mem_ball.mp (hsu (subset_tsupport _ hx)).2
      have ht := norm_le_norm_sub_add x x₀
      rw [dist_eq_norm] at hh
      have hn : ‖x‖ ≤ (A : ℝ) := by linarith
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans hn }
  refine ⟨ρ,w,W,hρ,hw,hc,fun x => (hbounds (Set.mem_range_self x)).1,hs1,rfl,?_,?_⟩
  · exact fun x hx => (hsu hx).1
  · exact fun y hy => (hchart y hy).1

/-- At W=1, the already defined localized Poisson frequency is exactly the
frequency used above; no q-to-lcm replacement is made for general W. -/
theorem localizedFrequency_one_eq (q : ℕ) (v : Fin n → ℤ) :
    localizedFrequency q 1 v = (q : ℝ)⁻¹ • (fun i => (v i : ℝ)) := by
  rw [localizedFrequency_one]
  funext i
  simp [div_eq_mul_inv,mul_comm]

end CubicTenVariables.OscillatoryLocalization
