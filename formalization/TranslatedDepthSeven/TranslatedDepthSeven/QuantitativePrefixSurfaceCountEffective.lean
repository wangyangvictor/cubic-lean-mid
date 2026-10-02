import TranslatedDepthSeven.QuantitativePrefixPersistentCellEffective
import TranslatedDepthSeven.FixedSurfaceQuantitativePrefixEdgeSum

/-!
# Surface-count assembly with a varying terminal degree

This file combines the degree-effective persistent-cell theorem with the
same-family geometric partition and the exact changed-edge estimate.  It
removes the fixed terminal-degree condition required by the older Pila
assembly.  The only counting premise is `Published.CDHNV2025Corollary22`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 700000

local instance quantitativePrefixSurfaceEffectivePropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The closed nonlinear residual obtained from the uniform determinant
block-degree majorant. -/
def quantitativePrefixEffectiveCurveResidual
    (C : ℝ) (d b H Baux Bpoint : ℕ) (η a : ℝ) : ℝ :=
  let L := b + quantitativePrefixUniformBlockDegree H Baux η a
  C * ((d * L : ℕ) : ℝ) ^ (5 : ℕ) *
    ((Bpoint : ℝ) + 1) ^ (1 / 2 : ℝ) *
    (Real.log ((Bpoint : ℝ) + 1) + ((d * L : ℕ) : ℝ))

/-- Combine the rooted geometric partition with the degree-effective
persistent-cell estimate for the same literal auxiliary family. -/
theorem exists_uniform_quantitativePrefixSurfaceCountAssembly_effective
    (hCurve : CDHNV2025Corollary22) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b L : ℕ}
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
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        ∀ z ∈ X, MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m z i : ℚ))
            (auxiliary v (integralResidueVector z)) = 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        b + blockDegree v ≤ L) →
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
          C * ((d * L : ℕ) : ℝ) ^ (5 : ℕ) *
            (B + 1) ^ (1 / 2 : ℝ) *
            (Real.log (B + 1) + ((d * L : ℕ) : ℝ)) := by
  classical
  obtain ⟨C, hC, hpersistent⟩ :=
    exists_uniform_quantitativePrefixPersistentCells_effective hCurve
  refine ⟨C, hC, ?_⟩
  intro d b L sourceEquations hprime hgeometricPrime hhom hdegree
    P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
    hroom hauxiliary hauxZero hsource hdegreeCap B hB hbox
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
      hroom hauxiliary hdegreeCap B hB hbox
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

/-- For an actual fixed-surface auxiliary family, eliminate the exact
changed-edge sum and substitute the height-dependent terminal-degree
majorant.  There is no fixed terminal-degree parameter. -/
theorem exists_uniform_quantitativePrefixSurfaceCountAssembly_effective_globalEdgeBound
    (hCurve : CDHNV2025Corollary22) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b H Baux Bpoint : ℕ} {η a : ℝ}
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
          quantitativePrefixEffectiveCurveResidual
            C d b H Baux Bpoint η a := by
  classical
  obtain ⟨C, hC, hassembly⟩ :=
    exists_uniform_quantitativePrefixSurfaceCountAssembly_effective hCurve
  refine ⟨C, hC, ?_⟩
  intro d b H Baux Bpoint η a sourceEquations hprime hgeometricPrime hhom
    hdegree F P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hP
    hPm hallowed hroom hblock hauxiliary hauxZero hsource hzero hsmooth
    hBpoint hbox
  dsimp only
  let L := b + quantitativePrefixUniformBlockDegree H Baux η a
  have hdegreeCap : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      b + blockDegree v ≤ L := by
    intro v
    exact Nat.add_le_add_left
      (blockDegree_le_quantitativePrefixUniformBlockDegree
        hP blockDegree hblock v) b
  obtain ⟨representative, terminalVertex, terminalDegree, terminalCut,
      hrepresentative, hterminalVertex, hterminalDefs, hactiveCard,
      hcount⟩ :=
    hassembly sourceEquations hprime hgeometricPrime hhom hdegree
      P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed hroom
      hauxiliary hauxZero hsource hdegreeCap (Bpoint : ℝ)
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
  dsimp only [quantitativePrefixEffectiveCurveResidual, L] at hcount ⊢
  linarith

/-- Direct fixed-surface endpoint.  The determinant method constructs the
auxiliary family, the persistence argument leaves one rational degree-one
union, and the changed-edge sum is eliminated.  Unlike the older endpoint,
there is no fixed terminal-degree parameter or terminal-cap hypothesis. -/
theorem exists_fixedSurface_quantitativePrefixSurfaceCount_effective_globalEdgeBound
    (hCurve : CDHNV2025Corollary22)
    {d : ℕ} (hd : 0 < d)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hchart : MvPolynomial.X 0 ∉ finiteEquationIdeal sourceEquations)
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (Kred : ℝ) (hKred : 1 ≤ Kred) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η)
    (ha : Real.sqrt Kred / Real.sqrt (d : ℝ) < a) :
    ∃ b D A H₀ : ℕ, ∃ Cdet Ccurve : ℝ,
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ Cdet ∧ 0 < Ccurve ∧
      ∀ (P : Finset ℕ) (depth H Baux Bpoint m Dex : ℕ)
        (u : IntVector 3) (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ) (z₀ : IntVector 3),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      H₀ ≤ H → 1 ≤ Baux →
      0 < Dex → Dex ≤ H ^ Aex → m * primeProduct P ∣ Dex →
      m ≠ 0 →
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            Kred * (p : ℝ) ^ 2) →
      (∀ z ∈ X, ∀ i,
        (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
      (∀ z ∈ X, ∀ i, (z i).natAbs ≤ Baux) →
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
            (1 + (Baux : ℝ) ^ a /
              (PrimeSubsetPrefix.modulus v : ℝ)) ∧
          (∀ ρ ∈ occupiedIntegralResidues
              (PrimeSubsetPrefix.modulus v) X,
            (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
              auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0) ∧
        (let root := PrimeSubsetPrefix.root P depth
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
              quantitativePrefixEffectiveCurveResidual
                Ccurve d b H Baux Bpoint η a) := by
  classical
  obtain ⟨Ccurve, hCcurve, hassembly⟩ :=
    exists_uniform_quantitativePrefixSurfaceCountAssembly_effective_globalEdgeBound
      hCurve
  obtain ⟨b, D, A, H₀, Cdet, hD, hA, hH₀, hCdet, hchoice⟩ :=
    exists_fixedSurface_quantitative_prefixAuxiliaryChoice
      hd (finiteEquationIdeal sourceEquations) hprime hhom hchart hdegree
        F Kred hKred Aex η a hη ha
  refine ⟨b, D, A, H₀, Cdet, Ccurve,
    hD, hA, hH₀, hCdet, hCcurve, ?_⟩
  intro P depth H Baux Bpoint m Dex u X allowed z₀ hP hPm hH hBaux
    hDex hDexHeight hmPDex hm hz₀ hallowed hroom hpoints hheight hboxAux
    hzero hgradient hsmooth hsource hBpoint hboxPoint
  obtain ⟨blockDegree, auxiliary, hauxiliary⟩ :=
    hchoice P depth H Baux m Dex u X hP hPm hH hBaux hDex hDexHeight
      hmPDex hm hpoints hheight hboxAux hzero hgradient hsmooth
  obtain ⟨representative, terminalVertex, terminalDegree, terminalCut,
      hrepresentative, hterminalVertex, hterminalDefs, hactiveCard,
      hcount⟩ :=
    hassembly sourceEquations hprime hgeometricPrime hhom hdegree
      F P depth u m (Nat.pos_of_ne_zero hm) X allowed blockDegree
      auxiliary z₀ hz₀ hP hPm hallowed hroom (fun v ↦ (hauxiliary v).2.1)
      (fun v ↦ (hauxiliary v).2.2.1)
      (fun v ↦ (hauxiliary v).2.2.2) hsource hzero hsmooth
      hBpoint hboxPoint
  refine ⟨blockDegree, auxiliary, hauxiliary, ?_⟩
  dsimp only
  exact ⟨representative, terminalVertex, terminalDegree, terminalCut,
    hrepresentative, hterminalVertex, hterminalDefs, hactiveCard, hcount⟩

end

end TranslatedDepthSeven
