import CubicTenVariables.LocalizedCountPowerSaving
import CubicTenVariables.LocalizedZeroTermLimit
import CubicTenVariables.RegularChartPositiveWeight
import CubicTenVariables.WeightedCounting

/-! The actual counting asymptotic and integer-zero criterion, conditional
on explicitly named remaining arithmetic hypotheses. The shifted average,
absolute convergence and positivity of the localized singular series are
not proved here. Delta kernels are proved internally; Poisson summation remains
an explicit input of this wrapper.
The regular weight used by the count is exactly the weight of its main term. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedCountingAsymptoticCriterion
open MvPolynomial MeasureTheory Filter RealRegularGradientChart LocalizedShiftedWindow
open LocalizedPoissonCount
open scoped Topology

/-- A power-saving error is negligible after the exact seventh-power
normalization, with no assumption on its behavior at zero scale. -/
theorem normalized_error_tendsto_zero (E : ℕ → ℂ) (C δ : ℝ) (hδ : 0 < δ)
    (hE : ∀ᶠ k : ℕ in atTop, ‖E k‖ ≤ C*(k:ℝ)^(7-δ)) :
    Tendsto (fun k : ℕ => E k/(k:ℂ)^7) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun k : ℕ => C*(k:ℝ)^(-δ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  filter_upwards [hE,eventually_ge_atTop 1] with k hk hk1
  have hkr : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have he : (k:ℝ)^(7-δ)/(k:ℝ)^7 = (k:ℝ)^(-δ) := by
    rw [← Real.rpow_natCast (k:ℝ) 7,← Real.rpow_sub hkr]
    congr 1
    norm_num
  rw [norm_div,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (C*(k:ℝ)^(7-δ))/(k:ℝ)^7 :=
      div_le_div_of_nonneg_right hk (by positivity)
    _ = _ := by rw [mul_div_assoc,he]

/-- Actual normalized complex count limit for any fixed regular datum
whose own oscillatory integral is integrable. -/
theorem tendsto_normalized 
    (poisson : Literature.SteinShakarchi2011Poisson)
    
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b)
    (ha : Summable (fun q => ‖localizedSingularSeriesTerm G W Ω q‖))
    (hJ : Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) D.weight.weight)) :
    Tendsto (fun k : ℕ =>
      (localizedWeightedCount G D.weight.weight D.weight.boxRadius k W Ω:ℂ)/(k:ℂ)^7)
      atTop (𝓝 (localizedSingularSeries G W Ω *
        cubicSingularIntegral (map (Int.castRingHom ℝ) G) D.weight.weight)) := by
  obtain ⟨p,hp,η,δ,C,P₀,hη,hηquarter,hδ,_,_,_,hbound⟩ :=
    LocalizedCountPowerSaving.exists_bound poisson G hG D W hW Ω b hb hshift
  have hηhalf : η ≤ 1/2 := by linarith
  let Q := CountingScaleSequence.scale η
  let A : ℕ → ℂ := fun k => localizedWeightedCount G D.weight.weight D.weight.boxRadius k W Ω
  let Z : ℕ → ℂ := fun k => zeroTerm G D.weight.weight k (Q k) W Ω η p
  have herr : ∀ᶠ k : ℕ in atTop, ‖A k-Z k‖ ≤ C*(k:ℝ)^(7-δ) := by
    have hk : ∀ᶠ k : ℕ in atTop, P₀ ≤ (k:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop P₀)
    filter_upwards [hk,CountingScaleSequence.eventually_window η hη hηhalf] with k hk hw
    exact hbound k (Q k) hk hw.1 hw.2.1 hw.2.2
  have herror := normalized_error_tendsto_zero (fun k => A k-Z k) C δ hδ herr
  have hmain := LocalizedZeroTermLimit.tendsto_normalized_scale G hG D.weight.weight
    W Ω p hp η hη hηhalf ha hJ
  have ht := hmain.add herror
  rw [add_zero] at ht
  apply ht.congr
  intro k
  change Z k/(k:ℂ)^7+(A k-Z k)/(k:ℂ)^7 = A k/(k:ℂ)^7
  ring

/-- Real normalized count limit, obtained from the preceding complex limit. -/
theorem tendsto_normalized_re 
    (poisson : Literature.SteinShakarchi2011Poisson)
    
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b)
    (ha : Summable (fun q => ‖localizedSingularSeriesTerm G W Ω q‖))
    (hJ : Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) D.weight.weight)) :
    Tendsto (fun k : ℕ =>
      localizedWeightedCount G D.weight.weight D.weight.boxRadius k W Ω/(k:ℝ)^7)
      atTop (𝓝 (localizedSingularSeries G W Ω *
        cubicSingularIntegral (map (Int.castRingHom ℝ) G) D.weight.weight).re) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_normalized poisson G hG D W hW Ω b hb hshift ha hJ)
  simpa only [Function.comp_def,← Complex.ofReal_natCast,← Complex.ofReal_pow,
    ← Complex.ofReal_div,Complex.ofReal_re] using ht

/-- A positive real part of the actual main constant gives eventual
positivity of the concrete finite weighted count. -/
theorem eventually_count_pos 
    (poisson : Literature.SteinShakarchi2011Poisson)
    
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b)
    (ha : Summable (fun q => ‖localizedSingularSeriesTerm G W Ω q‖))
    (hJ : Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) D.weight.weight))
    (hmain : 0 < (localizedSingularSeries G W Ω *
      cubicSingularIntegral (map (Int.castRingHom ℝ) G) D.weight.weight).re) :
    ∀ᶠ k : ℕ in atTop, 0 < localizedWeightedCount G D.weight.weight D.weight.boxRadius k W Ω :=
  eventually_localizedWeightedCount_pos_of_tendsto G D.weight.weight D.weight.boxRadius W Ω 7
    hmain (tendsto_normalized_re poisson G hG D W hW Ω b hb hshift ha hJ)

/-- An integer zero follows from the explicit Poisson
input and the remaining actual arithmetic estimates. The positive regular
weight is constructed in the contradiction branch, then used in the count. -/
theorem hasIntegerZero_of_series_re_pos 
    (poisson : Literature.SteinShakarchi2011Poisson)
    
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (W : ℕ) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (b : ℝ) (hb : b < 20/3) (hshift : CleanShiftedAverage G W Ω b)
    (ha : Summable (fun q => ‖localizedSingularSeriesTerm G W Ω q‖))
    (hseries : 0 < (localizedSingularSeries G W Ω).re) : HasIntegerZero G := by
  by_contra hzero
  obtain ⟨D,hJ,J,hJpos,hI,_⟩ := RegularChartPositiveWeight.exists_integer_data G hG hzero
  have hmain : 0 < (localizedSingularSeries G W Ω *
      cubicSingularIntegral (map (Int.castRingHom ℝ) G) D.weight.weight).re := by
    rw [hI]
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      using mul_pos hseries hJpos
  obtain ⟨k,hk⟩ := (eventually_count_pos poisson G hG D W hW Ω b hb hshift ha hJ hmain).exists
  exact hzero (hasIntegerZero_of_localizedWeightedCount_pos G D.weight.weight
    D.weight.boxRadius k W Ω hk)

/-- Source-facing criterion with the singular series explicitly equal to
a strictly positive real number. Its convergence and positivity are inputs. -/
theorem hasIntegerZero 
    (poisson : Literature.SteinShakarchi2011Poisson)
    
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (W : ℕ) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (b : ℝ) (hb : b < 20/3) (hshift : CleanShiftedAverage G W Ω b)
    (ha : Summable (fun q => ‖localizedSingularSeriesTerm G W Ω q‖))
    (σ : ℝ) (hσ : 0 < σ) (hseries : localizedSingularSeries G W Ω = (σ:ℂ)) :
    HasIntegerZero G :=
  hasIntegerZero_of_series_re_pos poisson G hG W hW Ω b hb hshift ha
    (by simpa only [hseries,Complex.ofReal_re] using hσ)

end CubicTenVariables.LocalizedCountingAsymptoticCriterion
