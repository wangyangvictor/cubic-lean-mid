import CubicTenVariables.FixedIntegralSurfacePrimeCount
import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffectiveTwoCap
import TranslatedDepthSeven.QuantitativePrefixTerminalReservoirScale

/-!
# Fixed integral surfaces with separate root and terminal degree caps

The root determinant cut retains its empty-prefix degree, while every
full-depth terminal cut uses the sharper reservoir bound
`b + ceil (4 H^eta)`.  The fixed integral surface point-count theorem
supplies the prime-field input away from one positive exceptional factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

namespace TranslatedDepthSeven

open MvPolynomial Published
open HessianTheorem11
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The fixed-integral-surface endpoint with genuinely separate degree caps.
The empty root uses the uniform inverse-modulus bound, whereas terminal
vertices use the full-reservoir estimate `b + ceil (4 H^eta)`.  Rational
lines are closed at cutoff zero, so their displayed cost is exact for that
specialization. -/
theorem
    exists_fixedSurface_quantitativePrefixSurfaceCount_effective_twoCap_closedLines_of_integralSurface
    (integralityOpen : CubicTenVariables.Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : CubicTenVariables.Literature.AffinePlaneCurveWeil)
    (hCurve : CDHNV2025Corollary22)
    {d : ℕ} (hd : 2 ≤ d)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hchart : MvPolynomial.X 0 ∉ finiteEquationIdeal sourceEquations)
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F}))
    (Kred : ℝ) (hKred : 1 < Kred) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η) (ha0 : 0 ≤ a) (haUpper : a ≤ 5 / 7)
    (haDet : Real.sqrt Kred / Real.sqrt (d : ℝ) < a) :
    ∃ Dsurface b D A H₀ : ℕ, ∃ Cdet Ccurve : ℝ,
      0 < Dsurface ∧
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ Cdet ∧ 0 < Ccurve ∧
      ∀ (scale : Parameters) (P : Finset ℕ)
        (depth H Bpoint m Dex : ℕ)
        (u : IntVector 3) (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ) (z₀ : IntVector 3),
      Dsurface ∣ Dex →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      H₀ ≤ H →
      0 < Dex → Dex ≤ H ^ Aex → m * primeProduct P ∣ Dex →
      m ≠ 0 →
      (∀ q ∈ modulusReservoir P depth,
        manuscriptReservoirTarget normalizedSurfaceReservoirConstant
          scale.T (5 / 7) ≤ q) →
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ z ∈ X, ∀ i,
        (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
      (∀ z ∈ X, ∀ i,
        (z i).natAbs ≤ 2 * surfaceTangentNaturalSide scale) →
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∃ v, MvPolynomial.eval
        (fun i => u i + (m : ℤ) * z i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ v,
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
          (MvPolynomial.pderiv v
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      1 ≤ Bpoint →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ (Bpoint : ℝ)) →
      ∃ blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ,
        ∃ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ,
        (∀ v : PrimeSubsetPrefix.Vertex P depth,
          0 < blockDegree v ∧
          ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
            (1 + ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ^ a /
              (PrimeSubsetPrefix.modulus v : ℝ)) ∧
          (∀ ρ ∈ occupiedIntegralResidues
              (PrimeSubsetPrefix.modulus v) X,
            (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
              auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0) ∧
        let Baux := 2 * surfaceTangentNaturalSide scale
        let Lroot := b + quantitativePrefixUniformBlockDegree H Baux η a
        let Lterminal := b + ⌈4 * (H : ℝ) ^ η⌉₊
        (X.card : ℝ) ≤
          (((PrimeSubsetPrefix.directedEdges P depth).card *
            quantitativePrefixEdgeMajorant
              F P depth d b H Baux η a : ℕ) : ℝ) +
          ((quantitativePrefixEffectiveLineOccurrenceMassTwoCap
              d Lroot Lterminal +
            quantitativePrefixEffectiveLineOccurrenceMassTwoCap
              d Lroot Lterminal *
                (1 + ⌈2 * (Bpoint : ℝ)⌉₊ / m) : ℕ) : ℝ) +
          quantitativePrefixEffectiveCurveResidualTwoCap
            Ccurve d Lroot Lterminal Bpoint := by
  classical
  obtain ⟨Dsurface, hDsurface, hsurface⟩ :=
    exists_fixed_integral_surface_prime_count_of_multiple
      integralityOpen curveWeil hd F hF0 hF hgeom Kred hKred
  obtain ⟨Ccurve, hCcurve, hassembly⟩ :=
    exists_uniform_quantitativePrefixSurfaceCount_effective_twoCap_closedLines
      hCurve
  obtain ⟨b, D, A, H₀, Cdet, hD, hA, hH₀, hCdet, hchoice⟩ :=
    exists_fixedSurface_quantitative_prefixAuxiliaryChoice
      (by omega) (finiteEquationIdeal sourceEquations) hprime hhom hchart
        hdegree F Kred hKred.le Aex η a hη haDet
  refine ⟨Dsurface, b, D, A, H₀, Cdet, Ccurve,
    hDsurface, hD, hA, hH₀, hCdet, hCcurve, ?_⟩
  intro scale P depth H Bpoint m Dex u X allowed z₀ hDsurfaceDex hP hPm
    hH hDex hDexHeight hmPDex hm hlower hz₀ hallowed hroom hheight
    hboxAux hzero hgradient hsmooth hsource hBpoint hboxPoint
  let Baux : ℕ := 2 * surfaceTangentNaturalSide scale
  let Lroot : ℕ := b + quantitativePrefixUniformBlockDegree H Baux η a
  let Lterminal : ℕ := b + ⌈4 * (H : ℝ) ^ η⌉₊
  have hBaux : 1 ≤ Baux := by
    dsimp only [Baux]
    have hside := one_le_surfaceTangentNaturalSide scale
    omega
  obtain ⟨blockDegree, auxiliary, hauxiliary⟩ :=
    hchoice P depth H Baux m Dex u X hP hPm hH hBaux hDex hDexHeight
      hmPDex hm (hsurface Dex hDsurfaceDex) hheight
      (by simpa only [Baux] using hboxAux) hzero hgradient hsmooth
  have hblock : ∀ v,
      ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
        (1 + (Baux : ℝ) ^ a /
          (PrimeSubsetPrefix.modulus v : ℝ)) :=
    fun v => (hauxiliary v).2.1
  have hrootCap : b + blockDegree (PrimeSubsetPrefix.root P depth) ≤
      Lroot := by
    dsimp only [Lroot]
    exact Nat.add_le_add_left
      (blockDegree_le_quantitativePrefixUniformBlockDegree
        hP blockDegree hblock (PrimeSubsetPrefix.root P depth)) b
  have hterminalCap : ∀ z ∈ X, ∀ v ∈
      PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
      v.1.card = depth → b + blockDegree v ≤ Lterminal := by
    intro z hz v hv hvDepth
    dsimp only [Lterminal]
    exact terminalPrefix_totalDegree_le_add_ceil_four_heightPower
      scale blockDegree η a ha0 haUpper hlower
        (by simpa only [Baux] using hblock) v hvDepth
  have hclosed := hassembly
    (d := d) (b := b) (H := H) (Baux := Baux) (Bpoint := Bpoint)
      (Lroot := Lroot) (Lterminal := Lterminal) (η := η) (a := a)
      sourceEquations hprime hgeometricPrime hhom hdegree F P depth u m
      (Nat.pos_of_ne_zero hm) X allowed blockDegree auxiliary z₀ hz₀ hP hPm
      hallowed hroom hblock
      (fun v => (hauxiliary v).2.2.1) hrootCap hterminalCap
      (fun v => (hauxiliary v).2.2.2) hsource hzero hsmooth hBpoint
      hboxPoint
  dsimp only at hclosed
  obtain ⟨_representative, _terminalVertex, _terminalDegree, _terminalCut,
      _hrepresentative, _hterminalVertex, _hterminalDefs, _hactiveCard,
      _base, _direction, _parameter, _hfull, _hoccurrence, hcount⟩ := hclosed
  refine ⟨blockDegree, auxiliary, ?_, ?_⟩
  · simpa only [Baux] using hauxiliary
  · simpa only [Baux, Lroot, Lterminal] using hcount

end TranslatedDepthSeven
