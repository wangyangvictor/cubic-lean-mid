import TranslatedDepthSeven.HomogeneousConeStandardChart
import TranslatedDepthSeven.RankSevenEdgeFrontierGeometry
import TranslatedDepthSeven.RankSevenDegreeOneSmoothStarCounting
import TranslatedDepthSeven.HomogeneousMinimalComponents
import TranslatedDepthSeven.CoefficientExtensionHomogeneousIdeal

/-!
# Real affine-chart degree mass from real cone degree mass

Each actual minimal prime of a dehomogenized homogeneous ideal is the
dehomogenization of a minimal prime of that ideal.  It suffices to choose a
minimal prime below the contraction: its chart is prime, and minimality
then identifies this chart with the original prime.  These chosen cone
components are distinct for distinct chart components.

The cone-to-chart Hilbert and dimension identities are internally proved.
Consequently the sole geometric input below is the already-used real
cone component degree mass; no real affine-chart mass is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Every minimal chart component is the chart of a minimal homogeneous
cone component which avoids the homogenizing variable. -/
theorem exists_minimalConeComponent_of_minimalStandardChartComponent
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (Q : Ideal (MvPolynomial (Fin N) K))
    (hQ : Q ∈ finiteMinimalPrimes (I.map (standardDehomogenizationHom K N))) :
    ∃ R ∈ finiteMinimalPrimes I,
      X (0 : Fin (N + 1)) ∉ R ∧
      R.map (standardDehomogenizationHom K N) = Q := by
  let f := standardDehomogenizationHom K N
  letI : Q.IsPrime := isPrime_of_mem_finiteMinimalPrimes hQ
  letI : (Q.comap f).IsPrime := Ideal.comap_isPrime f Q
  have hIQ : I ≤ Q.comap f :=
    (Ideal.map_le_iff_le_comap).mp (le_of_mem_finiteMinimalPrimes hQ)
  obtain ⟨R, hR, hRQ⟩ := exists_finiteMinimalPrime_le hIQ
  have hRprime := isPrime_of_mem_finiteMinimalPrimes hR
  have hRhom := isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hI
    ((mem_finiteMinimalPrimes_iff I R).mp hR)
  have hRX : X (0 : Fin (N + 1)) ∉ R := by
    intro hX
    have hone : (1 : MvPolynomial (Fin N) K) ∈ Q := by
      have h := hRQ hX
      change f (X (0 : Fin (N + 1))) ∈ Q at h
      simpa [f, standardDehomogenizationHom] using h
    exact (isPrime_of_mem_finiteMinimalPrimes hQ).ne_top
      ((Ideal.eq_top_iff_one Q).mpr hone)
  have hmapPrime := standardAffineChart_isPrime R hRhom hRprime hRX
  have hmapLe : R.map f ≤ Q := (Ideal.map_le_iff_le_comap).mpr hRQ
  have hmapContains : I.map f ≤ R.map f :=
    Ideal.map_mono (le_of_mem_finiteMinimalPrimes hR)
  have hQmin := (mem_finiteMinimalPrimes_iff (I.map f) Q).mp hQ
  exact ⟨R, hR, hRX, le_antisymm hmapLe
    (hQmin.2 ⟨hmapPrime, hmapContains⟩ hmapLe)⟩

/-- The displayed real affine-chart degree-mass premise follows from the
real cone degree-mass premise already present in the argument.  The source
projective certificate is recovered by first differences, not assumed. -/
theorem homogeneousPrimeRealAffineChartDegreeMass_of_coneComponentDegreeMass
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass) :
    StandardAG.HomogeneousPrimeRealAffineChartDegreeMass := by
  classical
  intro N s d I hprime hI haffine
  by_cases hX : X (0 : Fin (N + 1)) ∈ I
  · have htop : realProjectiveAffineChartIdeal I = ⊤ := by
      apply (Ideal.eq_top_iff_one _).mpr
      have h := Ideal.mem_map_of_mem (standardDehomogenizationHom ℝ N)
        (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap ℚ ℝ)) hX)
      simpa [realProjectiveAffineChartIdeal, standardDehomogenizationHom] using h
    have hempty : finiteMinimalPrimes (realProjectiveAffineChartIdeal I) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      have hle := le_of_mem_finiteMinimalPrimes hQ
      rw [htop] at hle
      exact (isPrime_of_mem_finiteMinimalPrimes hQ).ne_top (top_unique hle)
    refine ⟨fun _ ↦ 0, fun _ ↦ 0, ?_, ?_⟩
    · simp [hempty]
    · simp [hempty]
  · obtain ⟨r, hrs, _hchartDim⟩ :=
      exists_standardAffineChart_dimension I hI hprime hX haffine.2.1
    obtain ⟨r', hr's, hprojective⟩ :=
      exists_projectiveDimensionDegree_of_homogeneous_affineCone I hI haffine (by omega)
    have hrr : r' = r := by omega
    subst r'
    obtain ⟨componentDegree, hcomponent, hmass⟩ :=
      hRealMass N r d I hprime hI hprojective
    let J := realCoefficientExtensionOfRationalIdeal I
    have hJhom : J.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℝ) :=
      isHomogeneous_map_mvPolynomialMap (algebraMap ℚ ℝ) I hI
    let chart := finiteMinimalPrimes (realProjectiveAffineChartIdeal I)
    have hexists (Q : Ideal (MvPolynomial (Fin N) ℝ)) (hQ : Q ∈ chart) :
        ∃ R ∈ finiteMinimalPrimes J,
          X (0 : Fin (N + 1)) ∉ R ∧
          R.map (standardDehomogenizationHom ℝ N) = Q :=
      exists_minimalConeComponent_of_minimalStandardChartComponent J hJhom Q hQ
    let lift : Ideal (MvPolynomial (Fin N) ℝ) →
        Ideal (MvPolynomial (Fin (N + 1)) ℝ) := fun Q ↦
      if hQ : Q ∈ chart then Classical.choose (hexists Q hQ) else ⊤
    have hlift (Q : Ideal (MvPolynomial (Fin N) ℝ)) (hQ : Q ∈ chart) :
        lift Q ∈ finiteMinimalPrimes J ∧
          X (0 : Fin (N + 1)) ∉ lift Q ∧
          (lift Q).map (standardDehomogenizationHom ℝ N) = Q := by
      simpa only [lift, dif_pos hQ] using Classical.choose_spec (hexists Q hQ)
    refine ⟨fun _ ↦ r, fun Q ↦ componentDegree (lift Q), ?_, ?_⟩
    · intro Q hQ
      obtain ⟨hRmem, hRX, hRmap⟩ := hlift Q hQ
      have hRhom := isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
        ((mem_finiteMinimalPrimes_iff J (lift Q)).mp hRmem)
      obtain ⟨rQ, hrQ, hQdegree⟩ := exists_standardAffineChart_dimensionDegree
        (lift Q) hRhom hRX (hcomponent (lift Q) hRmem).2
      have hdimEq : rQ = r := by omega
      subst rQ
      refine ⟨hrs, ?_⟩
      change HasAffineDimensionDegree Q r (componentDegree (lift Q))
      rwa [hRmap] at hQdegree
    · have hinj : Set.InjOn lift (↑chart : Set (Ideal (MvPolynomial (Fin N) ℝ))) := by
        intro Q hQ Q' hQ' heq
        rw [← (hlift Q hQ).2.2, ← (hlift Q' hQ').2.2, heq]
      have hsubset : chart.image lift ⊆ finiteMinimalPrimes J := by
        intro R hR
        obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hR
        exact (hlift Q hQ).1
      calc
        ∑ Q ∈ chart, componentDegree (lift Q) =
            ∑ R ∈ chart.image lift, componentDegree R :=
          (Finset.sum_image hinj).symm
        _ ≤ ∑ R ∈ finiteMinimalPrimes J, componentDegree R :=
          Finset.sum_le_sum_of_subset hsubset
        _ ≤ d := hmass

end
end TranslatedDepthSeven
