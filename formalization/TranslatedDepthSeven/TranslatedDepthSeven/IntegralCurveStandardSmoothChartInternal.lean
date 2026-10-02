import TranslatedDepthSeven.GenericComponentJacobianChartSpreading
import TranslatedDepthSeven.SmoothRationalPointStandardChartInternal
import TranslatedDepthSeven.HomogeneousConeStandardChart
import Mathlib.RingTheory.Nullstellensatz

/-!
# A nonempty standard-smooth chart of an integral curve

Finite normalization determines the generic differential rank. The
already proved generic conormal selection chooses exactly the expected
number of equations, so its principal open has the actual relative
dimension, not an unspecified one. Nullstellensatz supplies a rational
augmentation over an algebraically closed field.

All affine rings below are literal quotients and principal localizations.
In particular the projective corollary retains the original first chart,
so the existing homogeneous/affine Hilbert-function identity applies.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Every affine domain in characteristic zero has a nonempty standard-
smooth principal open of its actual dimension. -/
theorem exists_nonzero_standardSmooth_principalOpen_of_primeAffine_dimension
    {K : Type*} [Field K] [CharZero K] {N r : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ J) = (r : WithBot ℕ∞)) :
    ∃ a : MvPolynomial (Fin N) K ⧸ J, a ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension r K (Localization.Away a) := by
  classical
  letI : J.IsPrime := hJ
  obtain ⟨s, hsN, g, hginj, hgfinite, htrdeg⟩ :=
    exists_finite_injective_normalization_of_primeAffine_with_trdeg J
  have hsr : s = r := by
    have h := htrdeg.symm.trans (trdeg_eq_nat_of_primeAffine_ringKrullDim_eq K J hJ hdim)
    exact_mod_cast h
  subst s
  obtain ⟨n, F, hF⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian J)
  obtain ⟨rows, cols, u, _hrows, hcols, hu, hDdvd, hclear, _haway⟩ :=
    exists_genericPrime_principalOpen_selectedJacobianChart J F hF g hginj hgfinite
  let equations := fun i ↦ F (rows i)
  let D := selectedJacobianDeterminant equations cols
  have hDnot : D ∉ J := by
    intro hD
    obtain ⟨b, hb⟩ := hDdvd
    apply hu
    rw [hb]
    exact J.mul_mem_right b hD
  have hproduct : u * D ∉ J := hJ.mul_notMem hu hDnot
  have hIJ : Ideal.span (Set.range equations) ≤ J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hF.le (Ideal.subset_span ⟨rows i, rfl⟩)
  refine ⟨Ideal.Quotient.mk J (u * D), ?_, ?_⟩
  · exact fun hzero ↦ hproduct (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  · have hstandard := local_equations_selectedJacobian_standardSmooth_principalOpen
      J equations cols hcols u hIJ hclear
    have hcount : N - (N - r) = r := by omega
    simpa only [hcount] using hstandard

/-- A nonzero principal open of an affine domain over an algebraically
closed field has an actual augmentation to that field. -/
theorem nonempty_algHom_principalOpen_of_primeAffine
    {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (a : MvPolynomial (Fin N) K ⧸ J) (ha : a ≠ 0) :
    Nonempty (Localization.Away a →ₐ[K] K) := by
  classical
  letI : J.IsPrime := hJ
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hG : G ∉ J := fun h ↦ ha (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hex : ∃ z : Fin N → K, z ∈ zeroLocus K J ∧ aeval z G ≠ 0 := by
    by_contra h
    have hvanish : G ∈ vanishingIdeal K (zeroLocus K J) := by
      intro z hz
      by_contra hne
      exact h ⟨z, hz, hne⟩
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hvanish
    exact hG hvanish
  obtain ⟨z, hz, hGz⟩ := hex
  let f : (MvPolynomial (Fin N) K ⧸ J) →ₐ[K] K :=
    Ideal.Quotient.liftₐ J (aeval z) hz
  have hunit : ∀ y : Submonoid.powers (Ideal.Quotient.mk J G), IsUnit (f y) := by
    intro y
    obtain ⟨n, hn⟩ := y.2
    change IsUnit (f y.1)
    rw [← hn, map_pow]
    exact (isUnit_iff_ne_zero.mpr hGz).pow n
  exact ⟨IsLocalization.liftAlgHom (S := Localization.Away (Ideal.Quotient.mk J G)) hunit⟩

/-- The actual first chart of an integral projective curve admits a
dimension-one standard-smooth principal localization and an augmentation.
Its affine ideal and dimension are retained explicitly. -/
theorem integralProjectiveCurve_firstChart_exists_standardSmooth_augmentation
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hX : X (0 : Fin (N + 1)) ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 1 d) :
    let J := I.map (standardDehomogenizationHom K N)
    J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin N) K ⧸ J) = (1 : WithBot ℕ∞) ∧
      ∃ a : MvPolynomial (Fin N) K ⧸ J, a ≠ 0 ∧
        Algebra.IsStandardSmoothOfRelativeDimension 1 K (Localization.Away a) ∧
        Nonempty (Localization.Away a →ₐ[K] K) := by
  let J := I.map (standardDehomogenizationHom K N)
  have hJ : J.IsPrime := standardAffineChart_isPrime I hhom hI hX
  obtain ⟨r, hr, hdim⟩ := exists_standardAffineChart_dimension I hhom hI hX
    (s := 2) (by simpa only [Nat.one_add, Nat.cast_ofNat] using hdegree.1)
  have hr1 : r = 1 := by omega
  subst r
  obtain ⟨a, ha, hstandard⟩ :=
    exists_nonzero_standardSmooth_principalOpen_of_primeAffine_dimension J hJ hdim
  exact ⟨hJ, hdim, a, ha, hstandard,
    nonempty_algHom_principalOpen_of_primeAffine J hJ a ha⟩

end
end TranslatedDepthSeven
