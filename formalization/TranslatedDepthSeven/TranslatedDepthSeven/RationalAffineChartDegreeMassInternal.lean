import TranslatedDepthSeven.RealAffineChartDegreeMassInternal

/-!
# Rational affine-chart degree mass

This is the rational, and entirely internal, counterpart of the existing
real affine-chart transfer.  A minimal component of the standard chart is
the chart of a minimal homogeneous cone component avoiding `X₀`.  The
projective Hilbert certificate passes to that chart with unchanged degree.
Choosing one source component for each chart component is injective, so the
sum of the chart degrees is bounded by the supplied projective degree mass.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Projective degree mass for the rational minimal components passes to
the actual minimal components of the first rational affine chart. -/
theorem rationalAffineChart_componentDegreeMass_of_projectiveComponents
    {N : ℕ} (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (sourceDegree : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ)
    (hsource : ∀ P ∈ finiteMinimalPrimes J,
      HasProjectiveDimensionDegree P 1 (sourceDegree P)) :
    ∃ chartDegree : Ideal (MvPolynomial (Fin N) ℚ) → ℕ,
      (∀ Q ∈ finiteMinimalPrimes
          (J.map (standardDehomogenizationHom ℚ N)),
        HasAffineHilbertDimensionDegree Q 1 (chartDegree Q)) ∧
      ∑ Q ∈ finiteMinimalPrimes
          (J.map (standardDehomogenizationHom ℚ N)), chartDegree Q ≤
        ∑ P ∈ finiteMinimalPrimes J, sourceDegree P := by
  classical
  let chart := finiteMinimalPrimes
    (J.map (standardDehomogenizationHom ℚ N))
  have hexists (Q : Ideal (MvPolynomial (Fin N) ℚ)) (hQ : Q ∈ chart) :
      ∃ P ∈ finiteMinimalPrimes J,
        X (0 : Fin (N + 1)) ∉ P ∧
        P.map (standardDehomogenizationHom ℚ N) = Q :=
    exists_minimalConeComponent_of_minimalStandardChartComponent
      J hJhom Q hQ
  let lift : Ideal (MvPolynomial (Fin N) ℚ) →
      Ideal (MvPolynomial (Fin (N + 1)) ℚ) := fun Q ↦
    if hQ : Q ∈ chart then Classical.choose (hexists Q hQ) else ⊤
  have hlift (Q : Ideal (MvPolynomial (Fin N) ℚ)) (hQ : Q ∈ chart) :
      lift Q ∈ finiteMinimalPrimes J ∧
        X (0 : Fin (N + 1)) ∉ lift Q ∧
        (lift Q).map (standardDehomogenizationHom ℚ N) = Q := by
    simpa only [lift, dif_pos hQ] using
      Classical.choose_spec (hexists Q hQ)
  have hchart (Q : Ideal (MvPolynomial (Fin N) ℚ)) (hQ : Q ∈ chart) :
      HasAffineHilbertDimensionDegree Q 1 (sourceDegree (lift Q)) := by
    obtain ⟨hP, hPX, hmap⟩ := hlift Q hQ
    have hPprime := isPrime_of_mem_finiteMinimalPrimes hP
    have hPhom := isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
      ((mem_finiteMinimalPrimes_iff J (lift Q)).mp hP)
    have hcone : HasAffineDimensionDegree (lift Q) 2
        (sourceDegree (lift Q)) :=
      hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
        (lift Q) hPhom hPprime 1 (sourceDegree (lift Q)) (hsource (lift Q) hP)
    obtain ⟨r, hr, haffine⟩ := exists_standardAffineChart_dimensionDegree
      (lift Q) hPhom hPX hcone
    have hre : r = 1 := by omega
    subst r
    rw [hmap] at haffine
    exact haffine.toHilbert
  refine ⟨fun Q ↦ sourceDegree (lift Q), hchart, ?_⟩
  have hinj : Set.InjOn lift
      (↑chart : Set (Ideal (MvPolynomial (Fin N) ℚ))) := by
    intro Q hQ Q' hQ' heq
    rw [← (hlift Q hQ).2.2, ← (hlift Q' hQ').2.2, heq]
  have hsubset : chart.image lift ⊆ finiteMinimalPrimes J := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact (hlift Q hQ).1
  calc
    ∑ Q ∈ chart, sourceDegree (lift Q) =
        ∑ P ∈ chart.image lift, sourceDegree P :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ P ∈ finiteMinimalPrimes J, sourceDegree P :=
      Finset.sum_le_sum_of_subset hsubset

end

end TranslatedDepthSeven
