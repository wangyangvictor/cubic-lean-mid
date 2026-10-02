import CubicTenVariables.GradientWindowFamily
import CubicTenVariables.LocalSupremumSelector
import CubicTenVariables.PhysicalGradientWindow
import CubicTenVariables.LocalSupremumNumerics

/-! The actual lattice sum of local maximum volumes on the chosen regular
chart. The underlying set may be any subset of the fixed chart box, including
the support of the constructed counting weight. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.AveragedGradientVolume
open MvPolynomial MeasureTheory RealRegularGradientChart GradientWindowScaling
open LocalSupremumWindow LocalSupremumSelector
open scoped BigOperators

/-- The source local maximum, with separate frequency cutoff and gradient
width. Empty frequency windows have value zero. -/
def localMaximum (F : MvPolynomial (Fin 10) ℝ) (K : Set (Fin 10 → ℝ))
    (P α B δ L : ℝ) (v : Fin 10 → ℤ) : ℝ :=
  maximum (frequencies 10 B)
    (fun a => (volume (GradientWindowScaling.window F K P α (fun i => (a i : ℝ)) δ)).toReal) v L

/-- The literal unrestricted lattice sum; its summand has finite support. -/
def volumeSum (F : MvPolynomial (Fin 10) ℝ) (K : Set (Fin 10 → ℝ))
    (P α B δ L : ℝ) : ℝ := ∑' v : Fin 10 → ℤ, localMaximum F K P α B δ L v

theorem volumeSum_eq_zero_of_lt_one (F : MvPolynomial (Fin 10) ℝ)
    (K : Set (Fin 10 → ℝ)) (P α B δ L : ℝ) (hB : B < 1) :
    volumeSum F K P α B δ L=0 := by
  simp only [volumeSum,localMaximum,maximum_frequencies_zero_of_lt_one _ B L _ hB,tsum_zero]

/-- Uniform raw estimate, retaining every cutoff and width factor. No
literature input, asymptotic hypothesis, or slice-count premise is assumed. -/
theorem exists_bound (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3) (D : Data F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Set (Fin 10 → ℝ)), K ⊆ D.box →
      ∀ (P α B δ L : ℝ), 0 < P → α ≠ 0 → 0 ≤ B → 0 ≤ δ → 0 ≤ L →
      volumeSum F K P α B δ L ≤
        C*P^10*(1+B+L)^7*(1+δ+L)^3*min 1 ((δ/(|α| * P^2))^7) := by
  classical
  obtain ⟨C,hC,hfamily⟩ := GradientWindowFamily.exists_bound D
  refine ⟨C,hC,?_⟩
  intro K hK P α B δ L hP hα hB hδ hL
  let g : (Fin 10 → ℤ) → ℝ := fun a =>
    (volume (GradientWindowScaling.window F K P α (fun i => (a i : ℝ)) δ)).toReal
  obtain ⟨T,a,_hT,ha,hsum⟩ := exists_frequency_selector g B L
  have hsub (v : Fin 10 → ℤ) :
      GradientWindowScaling.window F K P α (fun i => (a v i : ℝ)) δ ⊆
        GradientWindowScaling.window F D.box P α (fun i => (a v i : ℝ)) δ := by
    intro x hx
    exact ⟨hK hx.1,hx.2⟩
  have hβ : α*P^2 ≠ 0 := mul_ne_zero hα (pow_ne_zero 2 hP.ne')
  have hb := hfamily (α*P^2) δ B L hβ hδ hB hL T a
    (fun v hv => (ha v hv).2.1) (fun v hv => (ha v hv).2.2.1)
  have hscale : |α*P^2|=|α| * P^2 := by rw [abs_mul,abs_of_nonneg (sq_nonneg P)]
  calc
    volumeSum F K P α B δ L = ∑ v ∈ T, g (a v) := hsum
    _ ≤ ∑ v ∈ T,
        (volume (GradientWindowScaling.window F D.box P α (fun i => (a v i : ℝ)) δ)).toReal := by
      apply Finset.sum_le_sum
      intro v _
      exact ENNReal.toReal_mono (PhysicalGradientWindow.volume_window_ne_top F hF D P hP α _ δ)
        (measure_mono (hsub v))
    _ = P^10 * ∑ v ∈ T,
        (volume (GradientWindowScaling.window F D.box 1 (α*P^2) (fun i => (a v i : ℝ)) δ)).toReal := by
      simp only [PhysicalGradientWindow.volume_window_toReal F hF D P hP,Finset.mul_sum]
    _ ≤ P^10*(C*(1+B+L)^7*(1+δ+L)^3*min 1 ((δ/|α*P^2|)^7)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hP.le 10)
    _ = _ := by rw [hscale]; ring

/-- The physical scales of the manuscript, before the phase split. The
window exponent eta is kept separate from the eventual error exponent. -/
theorem exists_scaled_bound (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Set (Fin 10 → ℝ)), K ⊆ D.box →
      ∀ (P R φ α η L : ℝ), 0 < P → 0 < R → α ≠ 0 → 0 ≤ L →
      volumeSum F K P α (P^η*LocalSupremumNumerics.V P R φ)
        (P^η*GradientVolumeNumerics.Vzero P R φ) L ≤
          C*LocalSupremumNumerics.rawBound P R φ α η L := by
  obtain ⟨C,hC,hbound⟩ := exists_bound F hF D
  refine ⟨C,hC,?_⟩
  intro K hK P R φ α η L hP hR hα hL
  have hv := LocalSupremumNumerics.V_pos P R φ hP hR
  have hv0 := GradientVolumeNumerics.Vzero_pos P R φ hP hR
  have hb := hbound K hK P α (P^η*LocalSupremumNumerics.V P R φ)
    (P^η*GradientVolumeNumerics.Vzero P R φ) L hP hα (by positivity) (by positivity) hL
  calc
    _ ≤ _ := hb
    _ = _ := by unfold LocalSupremumNumerics.rawBound; ring

end CubicTenVariables.AveragedGradientVolume
