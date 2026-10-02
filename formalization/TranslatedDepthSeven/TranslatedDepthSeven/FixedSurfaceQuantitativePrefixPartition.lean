import TranslatedDepthSeven.QuantitativeSurfacePrefixGeometricPartition

/-!
# One fixed-surface quantitative prefix endpoint

This file composes the determinant construction with the literal rooted
geometric partition and the changed-edge residual theorem.  Thus the output
is one actual family of rational auxiliary forms; the geometric labels and
all edge cells in the conclusion are formed from that same family.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 7000000
set_option synthInstance.maxHeartbeats 500000

local instance fixedSurfacePrefixPartitionPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- A single fixed-surface theorem producing the quantitative auxiliary
family, its common-root geometric partition, and a squarefree residual bound
for every exact changed-edge cell. -/
theorem exists_fixedSurface_quantitative_prefixGeometricPartition
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
    (K : ℝ) (hK : 1 ≤ K) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ b D A H₀ : ℕ, ∃ C : ℝ,
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ C ∧
      ∀ (P : Finset ℕ) (depth H B m Dex : ℕ)
        (u : Fin 3 → ℤ) (X : Finset (Fin 3 → ℤ))
        (allowed : (Fin 3 → ℤ) → Finset ℕ) (z₀ : Fin 3 → ℤ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      H₀ ≤ H → 1 ≤ B →
      0 < Dex → Dex ≤ H ^ Aex → m * primeProduct P ∣ Dex →
      m ≠ 0 →
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            K * (p : ℝ) ^ 2) →
      (∀ z ∈ X, ∀ i,
        (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
      (∀ z ∈ X, ∀ i, (z i).natAbs ≤ B) →
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
      ∃ blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ,
        ∃ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ,
        (∀ v : PrimeSubsetPrefix.Vertex P depth,
          0 < blockDegree v ∧
          ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
            (1 + (B : ℝ) ^ a /
              (PrimeSubsetPrefix.modulus v : ℝ)) ∧
          (∀ ρ ∈ occupiedIntegralResidues
              (PrimeSubsetPrefix.modulus v) X,
            (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
              auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0) ∧
        (let root := PrimeSubsetPrefix.root P depth
         let G₀ := MvPolynomial.map (algebraMap ℚ Qbar)
           (auxiliary root (integralResidueVector z₀))
         X.card ≤
            (∑ v : PrimeSubsetPrefix.Vertex P depth,
              ∑ w : PrimeSubsetPrefix.Vertex P depth,
                (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
                  u m X allowed v w).card) +
            (∑ o ∈ finiteEquationComponentOptions
                (finiteEquationFamilyUnion
                  (qbarSurfaceEquationFamily sourceEquations) {G₀}),
              (X.filter fun z =>
                o ≠ none ∧ ∀ v ∈
                  PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
                  selectedFiniteEquationComponent
                      (quantitativePrefixCutEquations
                        sourceEquations auxiliary z v)
                      (quantitativePrefixCoordinate u m z) = o).card) ∧
          (finiteEquationComponentOptions
            (finiteEquationFamilyUnion
              (qbarSurfaceEquationFamily sourceEquations) {G₀})).card ≤
            d * (b + blockDegree root)) ∧
        ∀ v w : PrimeSubsetPrefix.Vertex P depth,
          (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed v w).card ≤
            ((surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ^
              (Nat.lcm (PrimeSubsetPrefix.modulus v)
                (PrimeSubsetPrefix.modulus w)).primeFactors.card *
              (Nat.lcm (PrimeSubsetPrefix.modulus v)
                (PrimeSubsetPrefix.modulus w)) ^ 2) *
              ((d * (b + blockDegree v)) *
                (d * (b + blockDegree w))) := by
  classical
  obtain ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, hchoice⟩ :=
    exists_fixedSurface_quantitative_prefixAuxiliaryChoice
      hd (finiteEquationIdeal sourceEquations) hprime hhom hchart hdegree
        F K hK Aex η a hη ha
  refine ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, ?_⟩
  intro P depth H B m Dex u X allowed z₀ hP hPm hH hB hDex
    hDexHeight hmPDex hm hz₀ hallowed hpoints hheight hbox hzero
    hgradient hsmooth hsource
  obtain ⟨blockDegree, auxiliary, hauxiliary⟩ :=
    hchoice P depth H B m Dex u X hP hPm hH hB hDex hDexHeight
      hmPDex hm hpoints hheight hbox hzero hgradient hsmooth
  have hpartition := quantitativePrefixAuxiliaries_geometricPartition
    sourceEquations hgeometricPrime hhom hdegree
    P depth X allowed u m blockDegree auxiliary z₀ hz₀ hallowed
    (fun v => (hauxiliary v).2.2.1)
    (fun v => (hauxiliary v).2.2.2) hsource
  refine ⟨blockDegree, auxiliary, hauxiliary, hpartition, ?_⟩
  intro v w
  exact card_quantitativePrefixChangedEdgeCell_le_squarefree
    sourceEquations hgeometricPrime hhom hdegree F P depth hP m
    (Nat.pos_of_ne_zero hm) hPm u X allowed blockDegree auxiliary
    (fun t => (hauxiliary t).2.2.1)
    (fun t => (hauxiliary t).2.2.2)
    hsource hzero hsmooth v w

end

end TranslatedDepthSeven
