import CubicTenVariables.MicrolocalFixedLeadingPartition
import CubicTenVariables.MicrolocalConductorDepthReduced
import CubicTenVariables.PlanAlphaCleanShiftedReduced
import CubicTenVariables.LocalizedPositiveMainTermUnconditional
import CubicTenVariables.TensorReduction
import CubicTenVariables.CubicGenericIntegralityUniform
import CubicTenVariables.CubicPrincipalOpenUniform
import CubicTenVariables.SmoothInfinityGeometricIntegralityProved
import CubicTenVariables.FixedFamilyPrimeFieldPointCountProved
import CubicTenVariables.PlaneCubicWeilReduction
import CubicTenVariables.DegreeSpanEightPlaneProved

/-!
# Fixed-leading counts with the isolated-conjugate surface remainder

This endpoint combines the proved fixed-leading replacement for Salberger's
general hypersurface estimate with the already reduced cubic-surface chain.
Thus the broad finite-extension surface amplification premise is replaced by
the literal residual point count for an integral nonconical cubic surface
whose singularities form a finite nonempty conjugate orbit of size at most
four and contain no ground-field point.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

namespace CubicTenVariables.Theorem11ReducedFixedLeadingIsolatedConjugate

open MvPolynomial HessianTheorem11 PrimeLocalizationSeries

/-- The original main statement from fixed-leading high-component counts and
the exact isolated-conjugate cubic-surface remainder. -/
theorem main_from_counts
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (weil : Literature.SmoothCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (highCounts : ConeComponentFixedLeadingCount.HighDegreeFixedLeadingCounts)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount) :
    MainTheorem := by
  classical
  apply main_iff_symmetricTen.mpr
  intro T
  by_contra hzero
  have hAn := (anisotropicCubicOfNoIntegerZero T.polynomial
    T.polynomial_homogeneous hzero).anisotropic
  obtain ⟨t, f, N, B, tables, hP⟩ :=
    MicrolocalFixedLeadingPartition.exists_partition
      microlocal TranslatedDepthSeven.rationalProjectiveDegreeSpan_internal
      SmoothInfinityGeometricIntegralityProved.proved
      CubicGenericIntegralityUniform.proved
      (PlaneCubicWeilReduction.affine weil.plane) dichotomy highCounts
      T.polynomial T.polynomial_homogeneous hAn
  obtain ⟨_hQ, C, d₀, h, hc⟩ := MicrolocalConductorDepthReduced.of_partition
    CubicPrincipalOpenUniform.proved weil isolated
      FixedFamilyPrimeFieldPointCountProved.proved
      T.polynomial T.polynomial_homogeneous hAn f N B tables hP
  obtain ⟨p₀, hp₀, hshift⟩ := PlanAlphaCleanShiftedReduced.of_data
    CubicPrincipalOpenUniform.proved weil isolated
      FixedFamilyPrimeFieldPointCountProved.proved hP
      T.polynomial_homogeneous hAn hc
      ((1 : ℝ) / 192) (by norm_num) (by norm_num)
  let s := N.primeFactors ∪ (Finset.range p₀).filter Nat.Prime
  have hprimes : ∀ p ∈ s, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact (Finset.mem_filter.mp hp).2
  have hsN : N.primeFactors ⊆ s := Finset.subset_union_left
  have hsmall : ∀ p : ℕ, p.Prime → p < p₀ → p ∈ s := by
    intro p hp hlt
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hp⟩))
  let D := LocalizedSeriesUnconditional.chosenData T hzero s hprimes
  exact hzero (LocalizedPositiveMainTermUnconditional.hasIntegerZero
    T s hprimes D ((20 : ℝ) / 3 - 1 / 192) (by norm_num)
    (hshift s hprimes D hsN hsmall))

end CubicTenVariables.Theorem11ReducedFixedLeadingIsolatedConjugate
