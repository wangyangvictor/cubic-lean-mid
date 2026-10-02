import CubicTenVariables.DeltaKernelSeriesLimit
import CubicTenVariables.LocalizedZeroTermScaling
import CubicTenVariables.CountingScaleSequence

/-! The literal localized zero-frequency term has the expected normalized
complex limit. Absolute convergence of its actual arithmetic coefficients
and integrability of the actual oscillatory integral remain explicit.
No positivity, arithmetic convergence theorem, or new literature is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedZeroTermLimit
open MvPolynomial MeasureTheory Filter LocalizedPoissonCount
open scoped Topology BigOperators

/-- The exact P^7 normalization of the actual zero-frequency contribution. -/
theorem normalized_zeroTerm_eq (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (w : (Fin 10 → ℝ) → ℝ) (P Q W : ℕ)
    (hP : 0 < P) (Ω : Set (Fin 10 → ZMod W)) (η : ℝ)
    (p : ℕ → ℕ → ℝ → ℂ) :
    zeroTerm G w P Q W Ω η p / (P:ℂ)^7 =
      ∑ q ∈ Finset.Icc 1 Q, localizedSingularSeriesTerm G W Ω q *
        RescaledDeltaArc.integral p (P:ℝ) Q q η
          (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w) := by
  rw [LocalizedZeroTermScaling.zeroTerm_eq_ten G hG w P Q W hP Ω η p]
  have hp : (P:ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  field_simp

/-- The localized series and singular integral in this limit are the
literal ones, using the same polynomial, congruence conditions and weight. -/
theorem tendsto_normalized (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (w : (Fin 10 → ℝ) → ℝ) (W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (p : ℕ → ℕ → ℝ → ℂ)
    (hp : DeltaMethod.KernelEstimates 1 p) (η : ℝ) (hη : 0 ≤ η)
    (P Q : ℕ → ℕ) (hP : Tendsto P atTop atTop) (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun k => (Q k:ℝ)^2/(P k:ℝ)^3) atTop (𝓝 0))
    (ha : Summable (fun q => ‖localizedSingularSeriesTerm G W Ω q‖))
    (hJ : Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w)) :
    Tendsto (fun k => zeroTerm G w (P k) (Q k) W Ω η p / (P k:ℂ)^7)
      atTop (𝓝 (localizedSingularSeries G W Ω *
        cubicSingularIntegral (map (Int.castRingHom ℝ) G) w)) := by
  have ht := DeltaKernelSeriesLimit.tendsto_sum p hp
    (localizedSingularSeriesTerm G W Ω) (by simp [localizedSingularSeriesTerm])
    ha η hη P Q hP hQ hratio (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w) hJ
  have ht' : Tendsto (fun k => ∑ q ∈ Finset.Icc 1 (Q k),
      localizedSingularSeriesTerm G W Ω q * RescaledDeltaArc.integral p
        (P k:ℝ) (Q k) q η (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w))
      atTop (𝓝 (localizedSingularSeries G W Ω *
        cubicSingularIntegral (map (Int.castRingHom ℝ) G) w)) := by
    simpa only [localizedSingularSeries,cubicSingularIntegral] using ht
  apply ht'.congr'
  filter_upwards [hP.eventually (eventually_ge_atTop 1)] with k hk
  exact (normalized_zeroTerm_eq G hG w (P k) (Q k) W (by omega) Ω η p).symm

/-- A concrete choice Q=ceil(P^(3/2-eta)) realizes the main-term limit
along every natural physical scale, with 0<eta<=1/2. -/
theorem tendsto_normalized_scale (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (w : (Fin 10 → ℝ) → ℝ) (W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (p : ℕ → ℕ → ℝ → ℂ)
    (hp : DeltaMethod.KernelEstimates 1 p) (η : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1/2)
    (ha : Summable (fun q => ‖localizedSingularSeriesTerm G W Ω q‖))
    (hJ : Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w)) :
    Tendsto (fun k : ℕ => zeroTerm G w k (CountingScaleSequence.scale η k) W Ω η p /
      (k:ℂ)^7) atTop (𝓝 (localizedSingularSeries G W Ω *
        cubicSingularIntegral (map (Int.castRingHom ℝ) G) w)) :=
  tendsto_normalized G hG w W Ω p hp η hη.le id (CountingScaleSequence.scale η)
    tendsto_id (CountingScaleSequence.tendsto_scale η hηhalf)
    (CountingScaleSequence.normalized_square_tendsto_zero η hη hηhalf) ha hJ

end CubicTenVariables.LocalizedZeroTermLimit
