import CubicTenVariables.RealRegularGradientChart
import CubicTenVariables.SingularIntegralPositivity
import CubicTenVariables.IntegerAnisotropy

/-! A single regular gradient chart and counting weight with positive
singular integral. The counting data are refined before any analytic
parameters are chosen. No analytic or literature input is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.RegularChartPositiveWeight
open MvPolynomial MeasureTheory Filter HessianTheorem11
open RealRegularGradientChart OscillatoryLocalization PolynomialCoordinateChart
open scoped Topology ContDiff

/-- Rechoose the radius and normalized weight inside any prescribed
neighborhood, while preserving the original regular point. -/
theorem exists_data_in_neighborhood {F : MvPolynomial (Fin 10) ℝ}
    (D : Data F) (U : Set (Fin 10 → ℝ)) (hU : U ∈ 𝓝 D.point) :
    ∃ D' : Data F, D'.point = D.point ∧ tsupport D'.weight.weight ⊆ U := by
  let V := U ∩ (D.domain ∩ Metric.ball D.point D.radius)
  have hV : V ∈ 𝓝 D.point :=
    Filter.inter_mem hU (Filter.inter_mem (D.domain_open.mem_nhds D.point_mem)
      (Metric.ball_mem_nhds D.point D.radius_pos))
  obtain ⟨ρ,w,W,hρ,hw,hc,hwn,hs,hW,hsupp,hchart⟩ :=
    exists_counting_weight_chart D.point D.point_ne_zero V hV
  have hpartial : ∀ z : Fin 10 → ℝ, ‖z-D.point‖ ≤ 2*ρ →
      D.partialBound ≤ |eval z (pderiv D.partialIndex F)| := by
    intro z hz
    let a := ρ⁻¹ • (z-D.point)
    have ha : ‖a‖ ≤ 2 := by
      dsimp [a]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
      exact (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hρ.le)).trans_eq
        (by field_simp [hρ.ne'])
    have he : chartPoint D.point ρ a=z := by simp [chartPoint,a,hρ.ne']
    have hball := (hchart a ha).2.2
    rw [he,Metric.mem_ball,dist_eq_norm] at hball
    exact D.partial_lowerBound z (by linarith [D.radius_pos])
  let D' : Data F := { D with
    radius := ρ
    radius_pos := hρ
    normalizedWeight := w
    normalized_smooth := hw
    normalized_compact := hc
    normalized_nonneg := hwn
    normalized_support := hs
    weight := W
    weight_eq := hW
    chart_inside := fun a ha => (hchart a ha).2.1
    partial_lowerBound := hpartial }
  exact ⟨D',rfl,fun x hx => (hsupp hx).1⟩

/-- Every regular gradient datum can be refined at the same point so that
its own weight has an absolutely integrable oscillatory integral and a
strictly positive singular integral, including the truncated limit. -/
theorem exists_positive_refinement {F : MvPolynomial (Fin 10) ℝ}
    (D : Data F) :
    ∃ D' : Data F, D'.point = D.point ∧
      Integrable (cubicOscillatoryIntegral F D'.weight.weight) ∧
      ∃ J : ℝ, 0 < J ∧ cubicSingularIntegral F D'.weight.weight = (J:ℂ) ∧
        Tendsto (cubicSingularIntegralTruncated F D'.weight.weight) atTop (𝓝 (J:ℂ)) := by
  have hi : eval D.point (pderiv D.partialIndex F) ≠ 0 := by
    have hh := D.partial_lowerBound D.point (by
      simpa only [sub_self,norm_zero] using
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) D.radius_pos.le))
    exact abs_pos.mp (lt_of_lt_of_le D.partialBound_pos hh)
  obtain ⟨D',hp,hs⟩ := exists_data_in_neighborhood D
    (coordinateChart F D.partialIndex D.point hi).source
    ((coordinateChart F D.partialIndex D.point hi).open_source.mem_nhds
      (mem_coordinateChart_source F D.partialIndex D.point hi))
  have hi' : eval D'.point (pderiv D.partialIndex F) ≠ 0 := by simpa only [hp] using hi
  have hs' : tsupport D'.weight.weight ⊆
      (coordinateChart F D.partialIndex D'.point hi').source := by
    simpa only [hp] using hs
  exact ⟨D',hp,positive_singularIntegral_of_chart_weight F D.partialIndex
    D'.point hi' D'.point_zero D'.weight hs'⟩

/-- The same selected data can be passed both to the global counting
estimate and to singular-integral positivity. Rational anisotropy is
the only premise; no separate weight is chosen for the main term. -/
theorem exists_data (F : AnisotropicCubic 10) :
    ∃ D : Data (map (algebraMap ℚ ℝ) F.polynomial),
      Integrable (cubicOscillatoryIntegral (map (algebraMap ℚ ℝ) F.polynomial)
        D.weight.weight) ∧
      ∃ J : ℝ, 0 < J ∧
        cubicSingularIntegral (map (algebraMap ℚ ℝ) F.polynomial) D.weight.weight = (J:ℂ) ∧
        Tendsto (cubicSingularIntegralTruncated (map (algebraMap ℚ ℝ) F.polynomial)
          D.weight.weight) atTop (𝓝 (J:ℂ)) := by
  obtain ⟨D⟩ := RealRegularGradientChart.exists_data F
  obtain ⟨D',_,hD'⟩ := exists_positive_refinement D
  exact ⟨D',hD'⟩

theorem exists_data_positive_re (F : AnisotropicCubic 10) :
    ∃ D : Data (map (algebraMap ℚ ℝ) F.polynomial),
      Integrable (cubicOscillatoryIntegral (map (algebraMap ℚ ℝ) F.polynomial)
        D.weight.weight) ∧
      0 < (cubicSingularIntegral (map (algebraMap ℚ ℝ) F.polynomial) D.weight.weight).re := by
  obtain ⟨D,hi,J,hJ,heq,_⟩ := exists_data F
  exact ⟨D,hi,by simpa only [heq,Complex.ofReal_re] using hJ⟩

/-- Literal integer-coefficient form for the circle-method contradiction
branch, with the same Data.weight in every analytic conclusion. -/
theorem exists_integer_data (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (hzero : ¬ HasIntegerZero G) :
    ∃ D : Data (map (Int.castRingHom ℝ) G),
      Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) D.weight.weight) ∧
      ∃ J : ℝ, 0 < J ∧
        cubicSingularIntegral (map (Int.castRingHom ℝ) G) D.weight.weight = (J:ℂ) ∧
        Tendsto (cubicSingularIntegralTruncated (map (Int.castRingHom ℝ) G)
          D.weight.weight) atTop (𝓝 (J:ℂ)) := by
  have h := exists_data (anisotropicCubicOfNoIntegerZero G hG hzero)
  change (∃ D : Data (map (algebraMap ℚ ℝ) (map (Int.castRingHom ℚ) G)),
    Integrable (cubicOscillatoryIntegral (map (algebraMap ℚ ℝ) (map (Int.castRingHom ℚ) G))
      D.weight.weight) ∧ ∃ J : ℝ, 0 < J ∧
      cubicSingularIntegral (map (algebraMap ℚ ℝ) (map (Int.castRingHom ℚ) G))
        D.weight.weight = (J:ℂ) ∧
      Tendsto (cubicSingularIntegralTruncated
        (map (algebraMap ℚ ℝ) (map (Int.castRingHom ℚ) G)) D.weight.weight)
        atTop (𝓝 (J:ℂ))) at h
  have he : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext x
    simp
  have hmap : map (algebraMap ℚ ℝ) (map (Int.castRingHom ℚ) G) =
      map (Int.castRingHom ℝ) G := by rw [MvPolynomial.map_map,he]
  rw [← hmap]
  exact h

theorem exists_integer_data_positive_re (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (hzero : ¬ HasIntegerZero G) :
    ∃ D : Data (map (Int.castRingHom ℝ) G),
      Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) D.weight.weight) ∧
      0 < (cubicSingularIntegral (map (Int.castRingHom ℝ) G) D.weight.weight).re := by
  obtain ⟨D,hi,J,hJ,heq,_⟩ := exists_integer_data G hG hzero
  exact ⟨D,hi,by simpa only [heq,Complex.ofReal_re] using hJ⟩

end CubicTenVariables.RegularChartPositiveWeight
