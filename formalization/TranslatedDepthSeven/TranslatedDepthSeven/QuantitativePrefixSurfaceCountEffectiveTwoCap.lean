import TranslatedDepthSeven.QuantitativePrefixPersistentCellEffectiveTwoCap
import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffectiveLineLedger
import TranslatedDepthSeven.FixedSurfaceQuantitativePrefixEdgeSum

/-!
# Effective surface assembly with separate root and terminal degree caps

The root cut controls the number of persistent components.  Full-depth
terminal cuts control the degree of the curves counted inside those
components.  Keeping those roles separate gives the nonlinear residual

`C (d Lroot) (d Lterminal)^4 (B+1)^(1/2)
   (log(B+1) + d Lterminal)`

and rational-line occurrence mass
`(d Lroot) (d Lterminal)`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 800000

local instance quantitativePrefixTwoCapPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- Nonlinear residual with separate root-component and terminal-curve
degree caps. -/
def quantitativePrefixEffectiveCurveResidualTwoCap
    (C : ℝ) (d Lroot Lterminal Bpoint : ℕ) : ℝ :=
  C * ((d * Lroot : ℕ) : ℝ) *
    ((d * Lterminal : ℕ) : ℝ) ^ (4 : ℕ) *
    ((Bpoint : ℝ) + 1) ^ (1 / 2 : ℝ) *
    (Real.log ((Bpoint : ℝ) + 1) + ((d * Lterminal : ℕ) : ℝ))

/-- The total rational degree-one occurrence mass: at most `d Lroot`
persistent components, each with degree mass at most `d Lterminal`. -/
def quantitativePrefixEffectiveLineOccurrenceMassTwoCap
    (d Lroot Lterminal : ℕ) : ℕ :=
  (d * Lroot) * (d * Lterminal)

/-- Combine the two-cap persistent estimate with the exact same-family
geometric partition. -/
theorem exists_uniform_quantitativePrefixSurfaceCountAssembly_effective_twoCap
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
      ∀ B : ℝ, 1 ≤ B →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ B) →
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
          C * ((d * Lroot : ℕ) : ℝ) *
            ((d * Lterminal : ℕ) : ℝ) ^ (4 : ℕ) *
            (B + 1) ^ (1 / 2 : ℝ) *
            (Real.log (B + 1) + ((d * Lterminal : ℕ) : ℝ)) := by
  classical
  obtain ⟨C, hC, hpersistent⟩ :=
    exists_uniform_quantitativePrefixPersistentCells_effective_twoCap hCurve
  refine ⟨C, hC, ?_⟩
  intro d b Lroot Lterminal sourceEquations hprime hgeometricPrime hhom
    hdegree P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
    hroom hauxiliary hrootCap hterminalCap hauxZero hsource B hB hbox
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
      hroom hauxiliary hrootCap hterminalCap B hB hbox
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
  dsimp only [active, cell, root, G₀] at hpersistentBound ⊢
  linarith

/-- Replace the exact changed-edge sum while retaining separate root and
terminal caps. -/
theorem exists_uniform_quantitativePrefixSurfaceCount_effective_twoCap_globalEdge
    (hCurve : CDHNV2025Corollary22) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b H Baux Bpoint Lroot Lterminal : ℕ} {η a : ℝ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (F : MvPolynomial (Fin 4) ℤ)
        (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ) (hm : 0 < m)
        (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ)
        (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
        (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ)
        (z₀ : IntVector 3),
      z₀ ∈ X →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ v,
        ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
          (1 + (Baux : ℝ) ^ a /
            (PrimeSubsetPrefix.modulus v : ℝ))) →
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
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ i,
        (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
          (MvPolynomial.pderiv i
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      1 ≤ Bpoint →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ (Bpoint : ℝ)) →
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
          (((PrimeSubsetPrefix.directedEdges P depth).card *
            quantitativePrefixEdgeMajorant
              F P depth d b H Baux η a : ℕ) : ℝ) +
          ((quantitativePrefixPersistentRationalLinearPointUnion
            (finiteEquationIdeal sourceEquations) active terminalCut
              u m cell).card : ℝ) +
          quantitativePrefixEffectiveCurveResidualTwoCap
            C d Lroot Lterminal Bpoint := by
  classical
  obtain ⟨C, hC, hassembly⟩ :=
    exists_uniform_quantitativePrefixSurfaceCountAssembly_effective_twoCap
      hCurve
  refine ⟨C, hC, ?_⟩
  intro d b H Baux Bpoint Lroot Lterminal η a sourceEquations hprime
    hgeometricPrime hhom hdegree F P depth u m hm X allowed blockDegree
    auxiliary z₀ hz₀ hP hPm hallowed hroom hblock hauxiliary hrootCap
    hterminalCap hauxZero hsource hzero hsmooth hBpoint hbox
  dsimp only
  obtain ⟨representative, terminalVertex, terminalDegree, terminalCut,
      hrepresentative, hterminalVertex, hterminalDefs, hactiveCard,
      hcount⟩ :=
    hassembly sourceEquations hprime hgeometricPrime hhom hdegree P depth
      u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed hroom
      hauxiliary hrootCap hterminalCap hauxZero hsource (Bpoint : ℝ)
      (by exact_mod_cast hBpoint) hbox
  have hedgeNat := sum_card_quantitativePrefixChangedEdgeCell_le_squarefree
    sourceEquations hgeometricPrime hhom hdegree F P depth hP m hm hPm
      u X allowed blockDegree auxiliary hblock hauxiliary hauxZero hsource
      hzero hsmooth
  have hedgeReal :
      (((∑ v : PrimeSubsetPrefix.Vertex P depth,
        ∑ w : PrimeSubsetPrefix.Vertex P depth,
          (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed v w).card) : ℕ) : ℝ) ≤
        (((PrimeSubsetPrefix.directedEdges P depth).card *
          quantitativePrefixEdgeMajorant
            F P depth d b H Baux η a : ℕ) : ℝ) := by
    exact_mod_cast hedgeNat
  refine ⟨representative, terminalVertex, terminalDegree, terminalCut,
    hrepresentative, hterminalVertex, hterminalDefs, hactiveCard, ?_⟩
  dsimp only [quantitativePrefixEffectiveCurveResidualTwoCap] at hcount ⊢
  linarith

/-- Close every rational degree-one occurrence at cutoff zero.  The final
bound has no residual line-union or synthetic line-count premise. -/
theorem exists_uniform_quantitativePrefixSurfaceCount_effective_twoCap_closedLines
    (hCurve : CDHNV2025Corollary22) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b H Baux Bpoint Lroot Lterminal : ℕ} {η a : ℝ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (F : MvPolynomial (Fin 4) ℤ)
        (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ) (hm : 0 < m)
        (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ)
        (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
        (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ)
        (z₀ : IntVector 3),
      z₀ ∈ X →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ v,
        ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
          (1 + (Baux : ℝ) ^ a /
            (PrimeSubsetPrefix.modulus v : ℝ))) →
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
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ i,
        (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
          (MvPolynomial.pderiv i
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      1 ≤ Bpoint →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ (Bpoint : ℝ)) →
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
        let J := fun o : {o // o ∈ active} ↦
          rationalAffineChartIntersectionIdeal
            (finiteEquationIdeal sourceEquations) (terminalCut o.1)
        let Y := fun o : {o // o ∈ active} ↦
          quantitativePrefixPersistentAffineCell u m cell o.1
        ∃ (base direction : RationalLinearOccurrence J → IntVector 3)
          (parameter : RationalLinearOccurrence J → IntVector 3 → ℤ),
          (∀ o ∈ activeRationalLinearOccurrences J Y,
            PrimitiveDirection (direction o) ∧
            Set.InjOn (parameter o)
              (↑(rationalLinearOccurrencePoints J Y o) : Set (IntVector 3)) ∧
            (∀ z ∈ rationalLinearOccurrencePoints J Y o,
              z = fun i ↦ base o i + parameter o z * direction o i) ∧
            affineIdealZeroLocus o.2.1 =
              Set.range (fun t : ℚ ↦
                fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ∧
            Set.range (fun t : ℚ ↦
              fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ⊆
                affineIdealZeroLocus (J o.1)) ∧
          Fintype.card (RationalLinearOccurrence J) ≤
            quantitativePrefixEffectiveLineOccurrenceMassTwoCap
              d Lroot Lterminal ∧
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
              C d Lroot Lterminal Bpoint := by
  classical
  obtain ⟨C, hC, hassembly⟩ :=
    exists_uniform_quantitativePrefixSurfaceCount_effective_twoCap_globalEdge
      hCurve
  refine ⟨C, hC, ?_⟩
  intro d b H Baux Bpoint Lroot Lterminal η a sourceEquations hprime
    hgeometricPrime hhom hdegree F P depth u m hm X allowed blockDegree
    auxiliary z₀ hz₀ hP hPm hallowed hroom hblock hauxiliary hrootCap
    hterminalCap hauxZero hsource hzero hsmooth hBpoint hbox
  dsimp only
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    u m X allowed
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  obtain ⟨representative, terminalVertex, terminalDegree, terminalCut,
      hrepresentative, hterminalVertex, hterminalDefs, hactiveCard, hcount⟩ :=
    hassembly sourceEquations hprime hgeometricPrime hhom hdegree F P depth
      u m hm X allowed blockDegree auxiliary z₀ hz₀ hP hPm hallowed hroom
      hblock hauxiliary hrootCap hterminalCap hauxZero hsource hzero hsmooth
      hBpoint hbox
  have hrepresentativeX : ∀ o ∈ active, representative o ∈ X := by
    intro o ho
    exact (Finset.mem_filter.mp (hrepresentative o ho)).1
  have hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ finiteEquationIdeal sourceEquations := by
    intro o ho
    have hρ : integralResidueVector (representative o) ∈
        occupiedIntegralResidues
          (PrimeSubsetPrefix.modulus (terminalVertex o)) X :=
      mem_occupiedIntegralResidues_iff.mpr
        ⟨representative o, hrepresentativeX o ho, rfl⟩
    have haux := hauxiliary (terminalVertex o)
      (integralResidueVector (representative o)) hρ
    rw [(hterminalDefs o).1, (hterminalDefs o).2]
    exact haux
  obtain ⟨base, direction, parameter, hfull, hoccurrence, hlineCount⟩ :=
    exists_quantitativePrefixPersistent_rationalLineCount
      (finiteEquationIdeal sourceEquations) hprime hhom hdegree active
        terminalDegree terminalCut hterminal u m hm cell (Bpoint : ℝ)
        (by
          intro o _ho z hz i
          apply hbox z
          exact (Finset.mem_filter.mp hz).1)
  have hterminalDegree : ∀ o ∈ active, terminalDegree o ≤ Lterminal := by
    intro o ho
    rw [(hterminalDefs o).1]
    exact hterminalCap (representative o) (hrepresentativeX o ho)
      (terminalVertex o) (hterminalVertex o ho).1 (hterminalVertex o ho).2
  have hdegreeSum : (∑ o ∈ active, d * terminalDegree o) ≤
      quantitativePrefixEffectiveLineOccurrenceMassTwoCap
        d Lroot Lterminal := by
    have hsum : (∑ o ∈ active, d * terminalDegree o) ≤
        active.card * (d * Lterminal) := by
      calc
        (∑ o ∈ active, d * terminalDegree o) ≤
            ∑ _o ∈ active, d * Lterminal := by
          apply Finset.sum_le_sum
          intro o ho
          exact Nat.mul_le_mul_left d (hterminalDegree o ho)
        _ = active.card * (d * Lterminal) := by simp
    have hactive : active.card ≤ d * Lroot :=
      hactiveCard.trans (Nat.mul_le_mul_left d hrootCap)
    exact hsum.trans (by
      simpa only [quantitativePrefixEffectiveLineOccurrenceMassTwoCap] using
        Nat.mul_le_mul_right (d * Lterminal) hactive)
  have hoccurrence' := hoccurrence.trans hdegreeSum
  have hlineCount' :
      (quantitativePrefixPersistentRationalLinearPointUnion
          (finiteEquationIdeal sourceEquations) active terminalCut
            u m cell).card ≤
        quantitativePrefixEffectiveLineOccurrenceMassTwoCap
            d Lroot Lterminal +
          quantitativePrefixEffectiveLineOccurrenceMassTwoCap
            d Lroot Lterminal *
            (1 + ⌈2 * (Bpoint : ℝ)⌉₊ / m) :=
    hlineCount.trans (Nat.add_le_add hdegreeSum
      (Nat.mul_le_mul_right _ hdegreeSum))
  have hlineCountReal :
      (((quantitativePrefixPersistentRationalLinearPointUnion
          (finiteEquationIdeal sourceEquations) active terminalCut
            u m cell).card : ℕ) : ℝ) ≤
        ((quantitativePrefixEffectiveLineOccurrenceMassTwoCap
              d Lroot Lterminal +
            quantitativePrefixEffectiveLineOccurrenceMassTwoCap
              d Lroot Lterminal *
              (1 + ⌈2 * (Bpoint : ℝ)⌉₊ / m) : ℕ) : ℝ) := by
    exact_mod_cast hlineCount'
  refine ⟨representative, terminalVertex, terminalDegree, terminalCut,
    hrepresentative, hterminalVertex, hterminalDefs, hactiveCard, ?_⟩
  dsimp only
  refine ⟨base, direction, parameter, hfull, hoccurrence', ?_⟩
  linarith

end

end TranslatedDepthSeven
