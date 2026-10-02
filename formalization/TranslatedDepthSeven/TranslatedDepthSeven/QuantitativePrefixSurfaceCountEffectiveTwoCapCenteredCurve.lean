import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffectiveTwoCap
import TranslatedDepthSeven.QuantitativePrefixPersistentCellEffectiveTwoCapCentered

/-!
# Two-cap surface assembly with a centered nonlinear residual

The nonlinear component count is performed after dividing the common
progression class by its modulus. Its height is therefore
`2 * Rbox / m + 2`, independent of the absolute point height.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 800000

local instance quantitativePrefixTwoCapCenteredCurvePropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- Nonlinear residual in a real-centred progression box of radius `Rbox`. -/
def quantitativePrefixEffectiveCurveResidualTwoCapCentered
    (C : ℝ) (d Lroot Lterminal : ℕ) (Rbox : ℝ) (m : ℕ) : ℝ :=
  C * ((d * Lroot : ℕ) : ℝ) *
    ((d * Lterminal : ℕ) : ℝ) ^ (4 : ℕ) *
    (2 * Rbox / (m : ℝ) + 2) ^ (1 / 2 : ℝ) *
    (Real.log (2 * Rbox / (m : ℝ) + 2) +
      ((d * Lterminal : ℕ) : ℝ))

/-- Combine the two-cap persistent estimate with the exact same-family
geometric partition. -/
theorem exists_uniform_quantitativePrefixSurfaceCountAssembly_effective_twoCap_centeredCurve
    (hCurve : CDHNV2025Corollary22) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b Lroot Lterminal : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ) (hm : 0 < m)
        (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ)
        (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
        (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ)
        (z₀ : IntVector 3),
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        ∀ ρ ∈ occupiedIntegralResidues
          (PrimeSubsetPrefix.modulus v) X,
          (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
            auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) →
      b + blockDegree (PrimeSubsetPrefix.root P depth) ≤ Lroot →
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        v.1.card = depth → b + blockDegree v ≤ Lterminal) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        ∀ z ∈ X, MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m z i : ℚ))
            (auxiliary v (integralResidueVector z)) = 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      ∀ (center : RealVector 3) (Rbox : ℝ), 0 ≤ Rbox →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ) - center i| ≤ Rbox) →
      let root := PrimeSubsetPrefix.root P depth
      let G₀ := auxiliary root (integralResidueVector z₀)
      let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
        u m X allowed
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      ∃ (representative : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          IntVector 3)
        (terminalVertex : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          PrimeSubsetPrefix.Vertex P depth)
        (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
        (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          MvPolynomial (Fin 4) ℚ),
        (∀ o ∈ active, representative o ∈ cell o) ∧
        (∀ o ∈ active,
          terminalVertex o ∈ PrimeSubsetPrefix.survivingVertices P
            (allowed (representative o)) depth ∧
          (terminalVertex o).1.card = depth) ∧
        (∀ o,
          terminalDegree o = b + blockDegree (terminalVertex o) ∧
          terminalCut o = auxiliary (terminalVertex o)
            (integralResidueVector (representative o))) ∧
        active.card ≤ d * (b + blockDegree root) ∧
        (X.card : ℝ) ≤
          ((∑ v : PrimeSubsetPrefix.Vertex P depth,
            ∑ w : PrimeSubsetPrefix.Vertex P depth,
              (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
                u m X allowed v w).card : ℕ) : ℝ) +
          ((quantitativePrefixPersistentRationalLinearPointUnion
            (finiteEquationIdeal sourceEquations) active terminalCut
              u m cell).card : ℝ) +
          quantitativePrefixEffectiveCurveResidualTwoCapCentered
            C d Lroot Lterminal Rbox m := by
  classical
  obtain ⟨C, hC, hpersistent⟩ :=
    exists_uniform_quantitativePrefixPersistentCells_effective_twoCap_centered
      hCurve
  refine ⟨C, hC, ?_⟩
  intro d b Lroot Lterminal sourceEquations hprime hgeometricPrime hhom
    hdegree P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
    hroom hauxiliary hrootCap hterminalCap hauxZero hsource
      center Rbox hRbox hbox
  dsimp only
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    u m X allowed
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  obtain ⟨representative, terminalVertex, terminalDegree, terminalCut,
      hrepresentative, hterminalVertex, hterminalDefs, hactiveCard,
      hpersistentBound⟩ :=
    hpersistent sourceEquations hprime hgeometricPrime hhom hdegree
      P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
      hroom hauxiliary hrootCap hterminalCap center Rbox hRbox hbox
  have hpartition := quantitativePrefixAuxiliaries_geometricPartition
    sourceEquations hgeometricPrime hhom hdegree P depth X allowed u m
    blockDegree auxiliary z₀ hz₀ hallowed hauxiliary hauxZero hsource
  have hpersistentSum :
      (∑ o ∈ finiteEquationComponentOptions
          (finiteEquationFamilyUnion
            (qbarSurfaceEquationFamily sourceEquations)
            {MvPolynomial.map (algebraMap ℚ Qbar) G₀}),
        (X.filter fun z =>
          o ≠ none ∧ ∀ v ∈
            PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
            selectedFiniteEquationComponent
                (quantitativePrefixCutEquations sourceEquations auxiliary z v)
                (quantitativePrefixCoordinate u m z) = o).card) =
        (active.biUnion cell).card := by
    simpa only [qbarSurfaceCutEquationFamily, cell, active, G₀, root,
      quantitativePrefixPersistentCell] using
      (sum_quantitativePrefixPersistentCells_card_eq_activeUnion
        sourceEquations auxiliary u m X allowed z₀)
  have hpartitionNat : X.card ≤
      (∑ v : PrimeSubsetPrefix.Vertex P depth,
        ∑ w : PrimeSubsetPrefix.Vertex P depth,
          (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed v w).card) +
        (active.biUnion cell).card := by
    rw [← hpersistentSum]
    exact hpartition.1
  have hpartitionReal : (X.card : ℝ) ≤
      ((∑ v : PrimeSubsetPrefix.Vertex P depth,
        ∑ w : PrimeSubsetPrefix.Vertex P depth,
          (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed v w).card : ℕ) : ℝ) +
        ((active.biUnion cell).card : ℝ) := by
    exact_mod_cast hpartitionNat
  refine ⟨representative, terminalVertex, terminalDegree, terminalCut,
    hrepresentative, hterminalVertex, hterminalDefs, hactiveCard, ?_⟩
  dsimp only [active, cell, root, G₀,
    quantitativePrefixEffectiveCurveResidualTwoCapCentered]
    at hpersistentBound ⊢
  linarith


end

end TranslatedDepthSeven
