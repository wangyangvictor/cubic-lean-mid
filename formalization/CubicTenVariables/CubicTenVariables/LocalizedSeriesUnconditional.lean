import CubicTenVariables.OrdinarySeriesUnconditional
import CubicTenVariables.PrimeLocalizationSeries

/-! Exact localized convergence and positivity, with the ordinary series
and every required local point constructed internally. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedSeriesUnconditional
open MvPolynomial PrimeLocalizationSeries

/-- The exact localized series for any supplied finite local data. -/
theorem series (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s),
      @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial) :
    Summable (fun q => ‖localizedSingularSeriesTerm T.polynomial
      (modulus s hprimes D) (restriction s hprimes D) q‖) ∧
      ∃ S : ℝ, 0 < S ∧ localizedSingularSeries T.polynomial
        (modulus s hprimes D) (restriction s hprimes D) = (S:ℂ) := by
  obtain ⟨ha,S,hS,hvalue⟩ :=
    OrdinarySeriesUnconditional.of_cubic T.polynomial
      T.polynomial_homogeneous hzero
  exact assemble s hprimes D T.polynomial_homogeneous ha S hS hvalue

/-- Choose the internally proved local data at the prescribed primes. -/
def chosenData (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime) :
    ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial :=
  fun p hp => @Classical.choice _
    (@nonempty_primeLocalizationData PleasantsProved.proved T.polynomial T.polynomial_homogeneous
      (anisotropicCubicOfNoIntegerZero T.polynomial T.polynomial_homogeneous hzero).anisotropic
      p ⟨hprimes p hp⟩)

/-- Constructed finite local data and a positive absolutely convergent series. -/
theorem exists_positive_series (T : SymmetricIntegerCubicTensor 10) (hzero : ¬ HasIntegerZero T.polynomial)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime) :
    ∃ D : ∀ (p : ℕ) (hp : p ∈ s),
        @PrimeLocalizationData p ⟨hprimes p hp⟩ T.polynomial,
      0 < modulus s hprimes D ∧
      Summable (fun q => ‖localizedSingularSeriesTerm T.polynomial
        (modulus s hprimes D) (restriction s hprimes D) q‖) ∧
      ∃ S : ℝ, 0 < S ∧ localizedSingularSeries T.polynomial
        (modulus s hprimes D) (restriction s hprimes D) = (S:ℂ) := by
  let D := chosenData T hzero s hprimes
  exact ⟨D,modulus_pos s hprimes D,series T hzero s hprimes D⟩

end CubicTenVariables.LocalizedSeriesUnconditional
