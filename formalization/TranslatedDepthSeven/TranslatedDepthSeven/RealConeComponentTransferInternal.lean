import TranslatedDepthSeven.RealAffineChartComponentTransferInternal

/-!
# Real components of a union of homogeneous components over Q

Each target minimal prime is assigned one source minimal prime. The real
component theorem for a prime source then gives dimension and degree, and
summing over the disjoint assigned subsets avoids counting a target twice.
This does not assume the whole source ideal is reduced or equidimensional.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Transfer supplied projective component certificates over Q to all
actual real cone components. The source ideal need not be prime. -/
theorem realCone_componentDegreeMass_of_rationalComponents
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass)
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (sourceDimension sourceDegree : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ)
    (hsource : ∀ P ∈ finiteMinimalPrimes I,
      HasProjectiveDimensionDegree P (sourceDimension P) (sourceDegree P)) :
    ∃ source : Ideal (MvPolynomial (Fin (N + 1)) ℝ) →
        Ideal (MvPolynomial (Fin (N + 1)) ℚ),
      ∃ componentDegree : Ideal (MvPolynomial (Fin (N + 1)) ℝ) → ℕ,
        (∀ Q ∈ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal I),
          source Q ∈ finiteMinimalPrimes I ∧
          Q ∈ finiteMinimalPrimes
            (realCoefficientExtensionOfRationalIdeal (source Q)) ∧
          1 ≤ componentDegree Q ∧
          HasAffineDimensionDegree Q (sourceDimension (source Q) + 1)
            (componentDegree Q)) ∧
        ∑ Q ∈ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal I),
          componentDegree Q ≤ ∑ P ∈ finiteMinimalPrimes I, sourceDegree P := by
  classical
  have hdata (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
      ∃ cdeg : Ideal (MvPolynomial (Fin (N + 1)) ℝ) → ℕ,
        P ∈ finiteMinimalPrimes I →
          (∀ Q ∈ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal P),
            1 ≤ cdeg Q ∧
            HasAffineDimensionDegree Q (sourceDimension P + 1) (cdeg Q)) ∧
          ∑ Q ∈ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal P),
            cdeg Q ≤ sourceDegree P := by
    by_cases hP : P ∈ finiteMinimalPrimes I
    · obtain ⟨cdeg, hc, hm⟩ := hRealMass N (sourceDimension P) (sourceDegree P) P
        (isPrime_of_mem_finiteMinimalPrimes hP)
        (isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hI
          ((mem_finiteMinimalPrimes_iff I P).mp hP)) (hsource P hP)
      exact ⟨cdeg, fun _ ↦ ⟨hc, hm⟩⟩
    · exact ⟨fun _ ↦ 0, fun h ↦ False.elim (hP h)⟩
  choose cdeg hc using hdata
  let target := finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal I)
  have hexists (Q : Ideal (MvPolynomial (Fin (N + 1)) ℝ)) (hQ : Q ∈ target) :
      ∃ P ∈ finiteMinimalPrimes I,
        Q ∈ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal P) := by
    exact exists_sourceMinimalPrime_of_mem_minimalPrimes_map
      (MvPolynomial.map (algebraMap ℚ ℝ)) I Q hQ
  let source : Ideal (MvPolynomial (Fin (N + 1)) ℝ) →
      Ideal (MvPolynomial (Fin (N + 1)) ℚ) := fun Q ↦
    if hQ : Q ∈ target then Classical.choose (hexists Q hQ) else ⊤
  have hsourceQ (Q : Ideal (MvPolynomial (Fin (N + 1)) ℝ)) (hQ : Q ∈ target) :
      source Q ∈ finiteMinimalPrimes I ∧
        Q ∈ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal (source Q)) := by
    simpa only [source, dif_pos hQ] using Classical.choose_spec (hexists Q hQ)
  refine ⟨source, fun Q ↦ cdeg (source Q) Q, ?_, ?_⟩
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
            finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal P) := by
          intro Q hQ
          obtain ⟨hQt, hQP⟩ := Finset.mem_filter.mp hQ
          simpa only [hQP] using (hsourceQ Q hQt).2
        calc
          ∑ Q ∈ target with source Q = P, cdeg (source Q) Q =
              ∑ Q ∈ target with source Q = P, cdeg P Q := by
            apply Finset.sum_congr rfl
            intro Q hQ
            rw [(Finset.mem_filter.mp hQ).2]
          _ ≤ ∑ Q ∈ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal P),
              cdeg P Q := Finset.sum_le_sum_of_subset hsub
          _ ≤ sourceDegree P := (hc P hP).2

/-- An equidimensional source component list transfers with its total degree
bound. No uniqueness of the source of a real component is assumed. -/
theorem realCone_componentDegreeMass_of_equidimensional_rationalComponents
    (hRealMass : StandardAG.HomogeneousPrimeRealConeComponentDegreeMass)
    {N r D : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (sourceDegree : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ)
    (hsource : ∀ P ∈ finiteMinimalPrimes I,
      HasProjectiveDimensionDegree P r (sourceDegree P))
    (hmass : ∑ P ∈ finiteMinimalPrimes I, sourceDegree P ≤ D) :
    ∃ componentDegree : Ideal (MvPolynomial (Fin (N + 1)) ℝ) → ℕ,
      (∀ Q ∈ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal I),
        1 ≤ componentDegree Q ∧
        HasAffineDimensionDegree Q (r + 1) (componentDegree Q)) ∧
      ∑ Q ∈ finiteMinimalPrimes (realCoefficientExtensionOfRationalIdeal I),
        componentDegree Q ≤ D := by
  obtain ⟨source, cdeg, hc, hm⟩ := realCone_componentDegreeMass_of_rationalComponents
    hRealMass I hI (fun _ ↦ r) sourceDegree hsource
  exact ⟨cdeg, fun Q hQ ↦ (hc Q hQ).2.2, hm.trans hmass⟩

end

end TranslatedDepthSeven
