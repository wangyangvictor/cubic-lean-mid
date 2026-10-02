import TranslatedDepthSeven.AffineChartPilaComponentCount
import TranslatedDepthSeven.PrimeProjectiveSaturation
import TranslatedDepthSeven.SalbergerAffinePacketMembership

/-!
# The literal Salberger--Pila terminal step for a rank-seven surface packet

Salberger's Corollary 3.7 is applied to one fixed rational projective
surface and to actual affine-chart representatives `(1,z)`.  Its auxiliary
homogeneous form is then dehomogenized, the actual minimal primes of the
real affine intersection are taken, and Pila's theorem is applied to every
nonlinear curve component.

The only downstream geometric input is written directly, after Salberger's
uniform degree bound `K` has been selected: every actual minimal prime of
every relevant chart intersection is either a degree-one affine curve or an
affine curve of a displayed degree between `2` and `D`.  This is not hidden
in an interface or in a preassembled branch estimate.  The conclusion keeps
both the literal degree-one point set and the actual number of nonlinear
minimal primes visible.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 1000000

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous prime component which survives projectivization and meets
the standard affine chart supplies Salberger's reduced, equidimensional,
saturated projective scheme and proper-infinity hypotheses directly from its
literal Hilbert dimension--degree statement. -/
theorem homogeneousPrime_salbergerProjectiveHypotheses
    {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hirrelevant : ¬ (projectiveIrrelevantIdeal ℚ N ≤ I))
    (hdimensionDegree : HasProjectiveDimensionDegree I r d)
    (hchart : MvPolynomial.X (0 : Fin (N + 1)) ∉ I) :
    IsReducedEquidimensionalProjectiveScheme I r d ∧
      InfinityHyperplaneMeetsProperly I := by
  letI : I.IsPrime := hprime
  have hsaturated : IsSaturatedByProjectiveIrrelevantIdeal I :=
    prime_isSaturatedByProjectiveIrrelevantIdeal hprime hirrelevant
  have hminimal : ∀ P ∈ I.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ P) = r + 1 := by
    intro P hP
    have hPI : P = I := by
      rw [Ideal.minimalPrimes_eq_subsingleton_self] at hP
      simpa using hP
    subst P
    exact hdimensionDegree.1
  have hinfinity : InfinityHyperplaneMeetsProperly I := by
    intro P hP
    have hPI : P = I := by
      rw [Ideal.minimalPrimes_eq_subsingleton_self] at hP
      simpa using hP
    simpa [hPI] using hchart
  exact ⟨⟨hhomogeneous, hsaturated, hprime.radical, hminimal,
    hdimensionDegree⟩, hinfinity⟩

/-- Exact terminal implication for one finite packet on a rational
projective surface in `P^13`.  The source points are integral affine
coordinates `z in Z^13`, hence Salberger's representatives are literally
`(1,z)` as required by his notation. -/
theorem rankSevenSurfacePacket_card_le_salbergerLines_add_pilaCurves
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    {d D : ℕ} {εSalberger εPila B : ℝ}
    (hεSalberger : 0 < εSalberger)
    (hεPila : 0 < εPila)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ))
    (hIprime : I.IsPrime)
    (hIirrelevant : ¬ (projectiveIrrelevantIdeal ℚ 13 ≤ I))
    (hIdimensionDegree : HasProjectiveDimensionDegree I 2 d)
    (hIchart : MvPolynomial.X (0 : Fin 14) ∉ I)
    (hB : 1 ≤ B)
    {index : Type} [Fintype index]
    (prime : index → ℕ)
    (hprime : ∀ i, (prime i).Prime)
    (hinjective : Function.Injective prime)
    (point : ∀ i, Fin 14 → ZMod (prime i))
    (hchart : ∀ i, point i 0 ≠ 0)
    (hmultiplicity : ∀ i,
      HasHilbertSamuelMultiplicityAt (hprime i)
        (projectiveSpecialFiberIdeal I) (point i) 2 1)
    (hproduct :
      B ^ (1 + εSalberger) ≤
        ∏ i, (prime i : ℝ) ^
          (((d : ℝ) / (1 : ℝ)) ^ ((2 : ℝ)⁻¹)))
    (X : Finset (IntVector 13))
    (hbox : ∀ z ∈ X, ∀ i, |(z i : ℝ)| ≤ B)
    (hzero : ∀ z ∈ X, ∀ f ∈ I,
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) f = 0)
    (hreduction : ∀ z ∈ X, ∀ j i,
      (z i : ZMod (prime j)) =
        (point j 0)⁻¹ * point j i.succ) :
    ∃ K : ℕ,
      (∀ (k : ℕ), k ≤ K →
        ∀ G : MvPolynomial (Fin 14) ℚ,
          G.IsHomogeneous k → G ∉ I →
          ∀ Q ∈ finiteMinimalPrimes
              (realAffineChartIntersectionIdeal I G),
            HasAffineHilbertDimensionDegree Q 1 1 ∨
              ∃ e : ℕ, 2 ≤ e ∧ e ≤ D ∧
                HasAffineHilbertDimensionDegree Q 1 e) →
      ∃ (k : ℕ) (G : MvPolynomial (Fin 14) ℚ) (C : ℝ),
        0 < C ∧ k ≤ K ∧ G.IsHomogeneous k ∧ G ∉ I ∧
        (∀ z ∈ X,
          MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
        (X.card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
              (realAffineChartIntersectionIdeal I G) X).card : ℝ) +
            ((nonlinearAffineComponents
              (realAffineChartIntersectionIdeal I G)).card : ℝ) *
              C * (B + 1) ^ ((1 / 2 : ℝ) + εPila) := by
  obtain ⟨hI, hinfinity⟩ :=
    homogeneousPrime_salbergerProjectiveHypotheses I hIhomogeneous
      hIprime hIirrelevant hIdimensionDegree hIchart
  obtain ⟨K, k, G, hk, hGhomogeneous, hGnot, hGsource⟩ :=
    salberger2007_corollary37_multiplicityOne
      hSalberger hεSalberger I (by omega) hI hinfinity hB
      prime hprime hinjective point hchart hmultiplicity hproduct
  refine ⟨K, ?_⟩
  intro hcomponents
  have hGzero : ∀ z ∈ X,
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0 := by
    intro z hz
    apply hGsource (integralAffineChartVector z)
    exact integralAffineChartVector_mem_InSalbergerSOne
      I B hB prime hprime point hchart z (hbox z hz)
        (hzero z hz) (hreduction z hz)
  let J := realAffineChartIntersectionIdeal I G
  have hJcomponents : ∀ Q ∈ finiteMinimalPrimes J,
      HasAffineHilbertDimensionDegree Q 1 1 ∨
        ∃ e : ℕ, 2 ≤ e ∧ e ≤ D ∧
          HasAffineHilbertDimensionDegree Q 1 e := by
    exact hcomponents k hk G hGhomogeneous hGnot
  have hXJ : ∀ z ∈ X,
      (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus J := by
    intro z hz
    apply intPoint_mem_realAffineChartIntersectionIdeal
    · intro f hf
      simpa [integralAffineChartVector] using hzero z hz f hf
    · simpa [integralAffineChartVector] using hGzero z hz
  have hU : 1 < B + 1 := by linarith only [hB]
  have hXbox : ∀ z ∈ X, ∀ i, |(z i : ℝ)| < B + 1 := by
    intro z hz i
    linarith only [hbox z hz i]
  obtain ⟨C, hC, hcount⟩ :=
    finiteSet_card_le_linearComponents_add_pilaCurveComponents
      hPila εPila hεPila J hJcomponents X hXJ (B + 1) hU hXbox
  refine ⟨k, G, C, hC, hk, hGhomogeneous, hGnot, hGzero, ?_⟩
  simpa [J] using hcount

end

end TranslatedDepthSeven
