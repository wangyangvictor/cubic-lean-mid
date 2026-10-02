import CubicTenVariables.LocalizedSeriesUnconditional
import CubicTenVariables.ConstructedDeltaSource
import CubicTenVariables.LocalizedCountingAsymptoticCriterion
import CubicTenVariables.ScalarLatticePoissonProved

/-! The actual positive zero-frequency main term, with no unproved literature
input. The integer-zero criterion still requires the displayed actual shifted
average estimate; that obligation is not assumed to hold in this module. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedPositiveMainTermUnconditional
open MvPolynomial MeasureTheory Filter PrimeLocalizationSeries
open RealRegularGradientChart LocalizedPoissonCount LocalizedShiftedWindow
open scoped Topology

/-- A single regular weight, chosen before the analytic scales and kernels,
has a strictly positive actual main constant and the normalized zero-term
limit for each canonical smaller-Q scale. -/
theorem exists_weight (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s),
      @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial) :
    ∃ R : Data (map (Int.castRingHom ℝ) T.polynomial),
      Integrable (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) T.polynomial)
        R.weight.weight) ∧
      ∃ c : ℝ, 0 < c ∧
        localizedSingularSeries T.polynomial (modulus s hprimes D)
          (restriction s hprimes D) *
          cubicSingularIntegral (map (Int.castRingHom ℝ) T.polynomial) R.weight.weight = (c:ℂ) ∧
        ∀ (p : ℕ → ℕ → ℝ → ℂ), DeltaMethod.KernelEstimates 1 p →
          ∀ η : ℝ, 0 < η → η ≤ 1/2 →
            Tendsto (fun k : ℕ => zeroTerm T.polynomial R.weight.weight k
              (CountingScaleSequence.scale η k) (modulus s hprimes D)
              (restriction s hprimes D) η p / (k:ℂ)^7) atTop (𝓝 (c:ℂ)) := by
  obtain ⟨ha,S,hS,hseries⟩ := LocalizedSeriesUnconditional.series T hzero s hprimes D
  obtain ⟨R,hI,J,hJ,hint,_⟩ :=
    RegularChartPositiveWeight.exists_integer_data T.polynomial T.polynomial_homogeneous hzero
  have hc : localizedSingularSeries T.polynomial (modulus s hprimes D)
      (restriction s hprimes D) *
      cubicSingularIntegral (map (Int.castRingHom ℝ) T.polynomial) R.weight.weight =
      ((S*J:ℝ):ℂ) := by rw [hseries,hint,Complex.ofReal_mul]
  refine ⟨R,hI,S*J,mul_pos hS hJ,hc,?_⟩
  intro p hp η hη hηhalf
  simpa only [hc] using LocalizedZeroTermLimit.tendsto_normalized_scale
    T.polynomial T.polynomial_homogeneous R.weight.weight (modulus s hprimes D)
    (restriction s hprimes D) p hp η hη hηhalf ha hI

/-- Constructed local data, regular weight, delta kernel and positive limit. -/
theorem exists_positive_limit 
    (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime) :
    ∃ D : ∀ (p : ℕ) (hp : p ∈ s),
        @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial,
      ∃ R : Data (map (Int.castRingHom ℝ) T.polynomial),
        ∃ c : ℝ, 0 < c ∧ ∃ p : ℕ → ℕ → ℝ → ℂ,
          DeltaMethod.KernelEstimates 1 p ∧
          ∀ η : ℝ, 0 < η → η ≤ 1/2 →
            Tendsto (fun k : ℕ => zeroTerm T.polynomial R.weight.weight k
              (CountingScaleSequence.scale η k) (modulus s hprimes D)
              (restriction s hprimes D) η p / (k:ℂ)^7) atTop (𝓝 (c:ℂ)) := by
  let D := LocalizedSeriesUnconditional.chosenData T hzero s hprimes
  obtain ⟨R,_,c,hc,_,hlimit⟩ := exists_weight T hzero s hprimes D
  obtain ⟨p,hp⟩ := ConstructedDeltaSource.exists_source_kernels
  exact ⟨D,R,c,hc,p,hp,hlimit p hp⟩

/-- The actual shifted-average estimate implies an integer zero. -/
theorem hasIntegerZero 

    (T : SymmetricIntegerCubicTensor 10)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s),
      @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial)
    (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage T.polynomial (modulus s hprimes D)
      (restriction s hprimes D) b) : HasIntegerZero T.polynomial := by
  by_contra hzero
  obtain ⟨ha,S,hS,hseries⟩ := LocalizedSeriesUnconditional.series T hzero s hprimes D
  exact hzero (LocalizedCountingAsymptoticCriterion.hasIntegerZero ScalarLatticePoissonProved.proved
    T.polynomial T.polynomial_homogeneous (modulus s hprimes D)
    (modulus_pos s hprimes D) (restriction s hprimes D) b hb hshift ha S hS hseries)

end CubicTenVariables.LocalizedPositiveMainTermUnconditional
