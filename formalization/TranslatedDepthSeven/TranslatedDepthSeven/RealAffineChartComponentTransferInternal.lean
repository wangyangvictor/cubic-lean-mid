import TranslatedDepthSeven.RealAffineChartDegreeMassInternal

/-!
# From rational component degrees to actual real chart components

Every target minimal prime is minimal above the image of at least one
source minimal prime. Choose one such source for each target, and sum over
the resulting disjoint finite subsets. Sources with empty charts contribute
nothing; a target belonging to several source chart families is counted
only once. The rational dimension and degree certificates remain explicit.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

universe u v

/-- A target minimal component is a minimal component of the image of
some source minimal component. No flatness hypothesis is required. -/
theorem exists_sourceMinimalPrime_of_mem_minimalPrimes_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (I : Ideal R) (Q : Ideal S)
    (hQ : Q ∈ finiteMinimalPrimes (I.map f)) :
    ∃ P ∈ finiteMinimalPrimes I, Q ∈ finiteMinimalPrimes (P.map f) := by
  letI : Q.IsPrime := isPrime_of_mem_finiteMinimalPrimes hQ
  letI : (Q.comap f).IsPrime := Ideal.comap_isPrime f Q
  have hIQ : I ≤ Q.comap f :=
    Ideal.map_le_iff_le_comap.mp (le_of_mem_finiteMinimalPrimes hQ)
  obtain ⟨P, hP, hPQ⟩ := exists_finiteMinimalPrime_le hIQ
  have hmapPQ : P.map f ≤ Q := Ideal.map_le_iff_le_comap.mpr hPQ
  obtain ⟨Q', hQ', hQ'Q⟩ := exists_finiteMinimalPrime_le hmapPQ
  have hIQ' : I.map f ≤ Q' :=
    (Ideal.map_mono (le_of_mem_finiteMinimalPrimes hP)).trans
      (le_of_mem_finiteMinimalPrimes hQ')
  have hQmin := (mem_finiteMinimalPrimes_iff (I.map f) Q).mp hQ
  have hQQ' : Q ≤ Q' :=
    hQmin.2 ⟨isPrime_of_mem_finiteMinimalPrimes hQ', hIQ'⟩ hQ'Q
  have heq : Q' = Q := le_antisymm hQ'Q hQQ'
  exact ⟨P, hP, heq ▸ hQ'⟩

/-- Each actual real chart component is assigned a rational minimal
component. Its chart dimension is one less than the source cone dimension,
and the total chart degree is bounded by the total supplied rational degree.

The only geometric input is the existing real cone component degree mass;
its affine-chart consequence is already proved internally. -/
theorem realAffineChart_componentDegreeMass_of_rationalComponents
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass)
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (sourceDimension sourceDegree : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ)
    (hsource : ∀ P ∈ finiteMinimalPrimes I,
      HasAffineDimensionDegree P (sourceDimension P) (sourceDegree P)) :
    ∃ source : Ideal (MvPolynomial (Fin N) ℝ) →
        Ideal (MvPolynomial (Fin (N + 1)) ℚ),
      ∃ chartDimension chartDegree : Ideal (MvPolynomial (Fin N) ℝ) → ℕ,
        (∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal I),
          source Q ∈ finiteMinimalPrimes I ∧
          Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal (source Q)) ∧
          chartDimension Q + 1 = sourceDimension (source Q) ∧
          HasAffineDimensionDegree Q (chartDimension Q) (chartDegree Q)) ∧
        ∑ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal I),
          chartDegree Q ≤ ∑ P ∈ finiteMinimalPrimes I, sourceDegree P := by
  classical
  have hChart := homogeneousPrimeRealAffineChartDegreeMass_of_coneComponentDegreeMass hRealMass
  have hdata (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
      ∃ cdim cdeg : Ideal (MvPolynomial (Fin N) ℝ) → ℕ,
        P ∈ finiteMinimalPrimes I →
          (∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal P),
            cdim Q + 1 = sourceDimension P ∧
            HasAffineDimensionDegree Q (cdim Q) (cdeg Q)) ∧
          ∑ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal P), cdeg Q ≤
            sourceDegree P := by
    by_cases hP : P ∈ finiteMinimalPrimes I
    · obtain ⟨cdim, cdeg, hc, hm⟩ := hChart N (sourceDimension P) (sourceDegree P) P
        (isPrime_of_mem_finiteMinimalPrimes hP)
        (isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hI
          ((mem_finiteMinimalPrimes_iff I P).mp hP)) (hsource P hP)
      exact ⟨cdim, cdeg, fun _ ↦ ⟨hc, hm⟩⟩
    · exact ⟨fun _ ↦ 0, fun _ ↦ 0, fun h ↦ False.elim (hP h)⟩
  choose cdim cdeg hc using hdata
  let target := finiteMinimalPrimes (realProjectiveAffineChartIdeal I)
  have hexists (Q : Ideal (MvPolynomial (Fin N) ℝ)) (hQ : Q ∈ target) :
      ∃ P ∈ finiteMinimalPrimes I,
        Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal P) := by
    let f := (standardDehomogenizationHom ℝ N).comp (MvPolynomial.map (algebraMap ℚ ℝ))
    have hQmap : Q ∈ finiteMinimalPrimes (I.map f) := by
      simpa only [target, realProjectiveAffineChartIdeal, Ideal.map_map] using hQ
    obtain ⟨P, hP, hPQ⟩ := exists_sourceMinimalPrime_of_mem_minimalPrimes_map f I Q hQmap
    exact ⟨P, hP, by
      simpa only [realProjectiveAffineChartIdeal, Ideal.map_map] using hPQ⟩
  let source : Ideal (MvPolynomial (Fin N) ℝ) →
      Ideal (MvPolynomial (Fin (N + 1)) ℚ) := fun Q ↦
    if hQ : Q ∈ target then Classical.choose (hexists Q hQ) else ⊤
  have hsourceQ (Q : Ideal (MvPolynomial (Fin N) ℝ)) (hQ : Q ∈ target) :
      source Q ∈ finiteMinimalPrimes I ∧
        Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal (source Q)) := by
    simpa only [source, dif_pos hQ] using Classical.choose_spec (hexists Q hQ)
  refine ⟨source, fun Q ↦ cdim (source Q) Q, fun Q ↦ cdeg (source Q) Q, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨hP, hPQ⟩ := hsourceQ Q hQ
    exact ⟨hP, hPQ, (hc (source Q) hP).1 Q hPQ⟩
  · change ∑ Q ∈ target, cdeg (source Q) Q ≤ _
    calc
      ∑ Q ∈ target, cdeg (source Q) Q =
          ∑ P ∈ finiteMinimalPrimes I,
            ∑ Q ∈ target with source Q = P, cdeg (source Q) Q :=
        (Finset.sum_fiberwise_of_maps_to (fun Q hQ ↦ (hsourceQ Q hQ).1)
          (fun Q ↦ cdeg (source Q) Q)).symm
      _ ≤ ∑ P ∈ finiteMinimalPrimes I, sourceDegree P := by
        apply Finset.sum_le_sum
        intro P hP
        have hsub : (target.filter (fun Q ↦ source Q = P)) ⊆
            finiteMinimalPrimes (realProjectiveAffineChartIdeal P) := by
          intro Q hQ
          obtain ⟨hQt, hQP⟩ := Finset.mem_filter.mp hQ
          simpa only [hQP] using (hsourceQ Q hQt).2
        calc
          ∑ Q ∈ target with source Q = P, cdeg (source Q) Q =
              ∑ Q ∈ target with source Q = P, cdeg P Q := by
            apply Finset.sum_congr rfl
            intro Q hQ
            rw [(Finset.mem_filter.mp hQ).2]
          _ ≤ ∑ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal P), cdeg P Q :=
            Finset.sum_le_sum_of_subset hsub
          _ ≤ sourceDegree P := (hc P hP).2

/-- A bound for the source cone dimensions and rational degree sum gives
the corresponding bound for all actual real affine-chart components. -/
theorem realAffineChart_componentDimensionDegreeMass_le_of_rationalComponents
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass)
    {N r D : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (sourceDimension sourceDegree : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ)
    (hsource : ∀ P ∈ finiteMinimalPrimes I,
      HasAffineDimensionDegree P (sourceDimension P) (sourceDegree P))
    (hdimension : ∀ P ∈ finiteMinimalPrimes I, sourceDimension P ≤ r + 1)
    (hmass : ∑ P ∈ finiteMinimalPrimes I, sourceDegree P ≤ D) :
    ∃ chartDimension chartDegree : Ideal (MvPolynomial (Fin N) ℝ) → ℕ,
      (∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal I),
        chartDimension Q ≤ r ∧
        HasAffineDimensionDegree Q (chartDimension Q) (chartDegree Q)) ∧
      ∑ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal I), chartDegree Q ≤ D := by
  obtain ⟨source, cdim, cdeg, hc, hm⟩ :=
    realAffineChart_componentDegreeMass_of_rationalComponents
      hRealMass I hI sourceDimension sourceDegree hsource
  refine ⟨cdim, cdeg, ?_, hm.trans hmass⟩
  intro Q hQ
  obtain ⟨hP, _hPQ, hdim, hdeg⟩ := hc Q hQ
  have hbound := hdimension (source Q) hP
  exact ⟨by omega, hdeg⟩

end

end TranslatedDepthSeven
