import CubicTenVariables.FixedLeadingSurfaceSurvivorDegreeSplitCount
import CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplitInternal

/-! Survivor aggregation using the internal bounded-degree curve count. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceSurvivorDegreeSplitCountInternal
open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfacePersistentRootDegreeSplit
attribute [local instance] MvPolynomial.gradedAlgebra
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem exists_uniform_surfaceCount_rootDegreeSplit_of_survivor_auxiliaries
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b Lroot : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ), 0 < m →
      ∀ (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ)
        (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
        (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ)
        (z₀ : IntVector 3),
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
          (auxiliary v (integralResidueVector z)).IsHomogeneous
              (b + blockDegree v) ∧
            auxiliary v (integralResidueVector z) ∉
              finiteEquationIdeal sourceEquations) →
      b + blockDegree (PrimeSubsetPrefix.root P depth) ≤ Lroot →
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        MvPolynomial.eval
          (fun i ↦ (progressionHomogeneousPoint u m z i : ℚ))
            (auxiliary v (integralResidueVector z)) = 0) →
      (∀ z ∈ X,
        (fun i ↦ (progressionHomogeneousPoint u m z i : ℚ)) ∈
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
      ∃ degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ,
        (∀ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀),
          Q.IsPrime ∧
          Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
          finiteEquationIdeal (qbarSurfaceEquationFamily sourceEquations) ≤ Q ∧
          HasProjectiveDimensionDegree Q 1 (degree Q)) ∧
        (∑ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q) ≤
          d * (b + blockDegree root) ∧
        active.card ≤ d * Lroot ∧
        ∀ (highConstant : ℕ → ℝ),
          Salberger2023Lemma313PersistentRootCallback sourceEquations G₀
            cell degree cutoff highConstant
              ((2 * Rbox / (m : ℝ) + 2) ^ (3 : ℕ)) →
          (X.card : ℝ) ≤
            ((∑ v : PrimeSubsetPrefix.Vertex P depth,
              ∑ w : PrimeSubsetPrefix.Vertex P depth,
                (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
                  u m X allowed v w).card : ℕ) : ℝ) +
            ((persistentRootLinePointUnion degree active cell).card : ℝ) +
            ∑ o ∈ active,
              persistentRootDegreeSplitError degree cutoff
                ((cutoff : ℝ) ^ 2 +
                  C * (2 * Rbox / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
                highConstant
                  ((2 * Rbox / (m : ℝ) + 2) ^ (3 : ℕ)) o := by
  classical
  obtain ⟨C, hC, hrootSplit⟩ :=
    FixedLeadingSurfacePersistentRootDegreeSplitInternal.exists_uniform_persistentRoot_degreeSplit
      hConjugate cutoff ε hε
  refine ⟨C, hC, ?_⟩
  intro d b Lroot sourceEquations hprime hgeometricPrime hhom hdegree
    P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
    hroom hauxiliary hrootCap hauxZero hsource center Rbox hRbox hbox
  dsimp only
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    u m X allowed
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  have hG₀data := hauxiliary z₀ hz₀ root
    (PrimeSubsetPrefix.root_mem_surviving P (allowed z₀) depth)
  have hrootEquation : ∀ z ∈ X,
      quantitativePrefixCutEquations sourceEquations auxiliary z root =
        qbarSurfaceCutEquationFamily sourceEquations G₀ := by
    intro z _hz
    have hresidue :
        (integralResidueVector z :
          Fin 3 → ZMod (PrimeSubsetPrefix.modulus root)) =
            integralResidueVector z₀ := by
      rw [show PrimeSubsetPrefix.modulus root = 1 by
        exact PrimeSubsetPrefix.modulus_root P depth]
      exact Subsingleton.elim _ _
    simp only [quantitativePrefixCutEquations, G₀]
    rw [hresidue]
  have hrootSelected : ∀ o ∈ active, ∀ z ∈ cell o,
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations G₀)
        (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) = o := by
    intro o _ho z hz
    have hzData := (Finset.mem_filter.mp hz).2
    have hlabel := hzData.2 root
      (PrimeSubsetPrefix.root_mem_surviving P (allowed z) depth)
    rw [hrootEquation z (Finset.filter_subset _ _ hz)] at hlabel
    exact hlabel
  have hcellBox : ∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
      |(integralAffineMap u z m i : ℝ) - center i| ≤ Rbox := by
    intro o _ho z hz i
    exact hbox z (Finset.filter_subset _ _ hz) i
  obtain ⟨degree, hrootData, hrootMass, hactiveCard, hpersistentBound⟩ :=
    hrootSplit sourceEquations hprime hgeometricPrime hhom hdegree
      G₀ hG₀data.1 hG₀data.2 cell u m hm hrootSelected
      center Rbox hRbox hcellBox
  have hpartition :=
    FixedLeadingSurfaceSurvivorResidual.geometricPartition_of_survivor_auxiliaries
      sourceEquations hgeometricPrime hhom hdegree P depth X allowed u m
      blockDegree auxiliary z₀ hz₀ hallowed hauxiliary hauxZero hsource
  have hpersistentSum :
      (∑ o ∈ finiteEquationComponentOptions
          (finiteEquationFamilyUnion
            (qbarSurfaceEquationFamily sourceEquations)
            {MvPolynomial.map (algebraMap ℚ Qbar) G₀}),
        (X.filter fun z ↦
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
  refine ⟨degree, hrootData, hrootMass,
    hactiveCard.trans (Nat.mul_le_mul_left d hrootCap), ?_⟩
  intro highConstant hHigh
  have hpersistent := hpersistentBound highConstant hHigh
  dsimp only [active, cell, root, G₀] at hpersistent ⊢
  linarith

/-- Full survivor-count endpoint with the genuinely uniform Salberger 3.16
high-degree callback.  The high constant is selected before the surface,
auxiliary equations, height, and active degrees.  Its height parameter is the
product of projective coordinate bounds, represented by the cube of the
three-dimensional affine side. -/
theorem exists_uniform_surfaceCount_rootDegreeSplit_uniformHigh_of_survivor_auxiliaries
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (highConstant : ℝ),
      ∀ {d b Lroot : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ), 0 < m →
      ∀ (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ)
        (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
        (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ)
        (z₀ : IntVector 3),
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
          (auxiliary v (integralResidueVector z)).IsHomogeneous
              (b + blockDegree v) ∧
            auxiliary v (integralResidueVector z) ∉
              finiteEquationIdeal sourceEquations) →
      b + blockDegree (PrimeSubsetPrefix.root P depth) ≤ Lroot →
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        MvPolynomial.eval
          (fun i ↦ (progressionHomogeneousPoint u m z i : ℚ))
            (auxiliary v (integralResidueVector z)) = 0) →
      (∀ z ∈ X,
        (fun i ↦ (progressionHomogeneousPoint u m z i : ℚ)) ∈
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
      ∃ degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ,
        (∀ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀),
          Q.IsPrime ∧
          Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
          finiteEquationIdeal (qbarSurfaceEquationFamily sourceEquations) ≤ Q ∧
          HasProjectiveDimensionDegree Q 1 (degree Q)) ∧
        (∑ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q) ≤
          d * (b + blockDegree root) ∧
        active.card ≤ d * Lroot ∧
        (Salberger2023Theorem316PersistentRootCallback sourceEquations G₀
          cell degree cutoff highConstant ε
            ((2 * Rbox / (m : ℝ) + 2) ^ (3 : ℕ)) →
          (X.card : ℝ) ≤
            ((∑ v : PrimeSubsetPrefix.Vertex P depth,
              ∑ w : PrimeSubsetPrefix.Vertex P depth,
                (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
                  u m X allowed v w).card : ℕ) : ℝ) +
            ((persistentRootLinePointUnion degree active cell).card : ℝ) +
            ∑ o ∈ active,
              persistentRootUniformDegreeSplitError degree cutoff
                ((cutoff : ℝ) ^ 2 +
                  C * (2 * Rbox / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
                highConstant ε
                  ((2 * Rbox / (m : ℝ) + 2) ^ (3 : ℕ)) o) := by
  classical
  obtain ⟨C, hC, hrootSplit⟩ :=
    FixedLeadingSurfacePersistentRootDegreeSplitInternal.exists_uniform_persistentRoot_degreeSplit_uniformHigh
      hConjugate cutoff ε hε
  refine ⟨C, hC, ?_⟩
  intro highConstant d b Lroot sourceEquations hprime hgeometricPrime hhom
    hdegree P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
    hroom hauxiliary hrootCap hauxZero hsource center Rbox hRbox hbox
  dsimp only
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    u m X allowed
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  have hG₀data := hauxiliary z₀ hz₀ root
    (PrimeSubsetPrefix.root_mem_surviving P (allowed z₀) depth)
  have hrootEquation : ∀ z ∈ X,
      quantitativePrefixCutEquations sourceEquations auxiliary z root =
        qbarSurfaceCutEquationFamily sourceEquations G₀ := by
    intro z _hz
    have hresidue :
        (integralResidueVector z :
          Fin 3 → ZMod (PrimeSubsetPrefix.modulus root)) =
            integralResidueVector z₀ := by
      rw [show PrimeSubsetPrefix.modulus root = 1 by
        exact PrimeSubsetPrefix.modulus_root P depth]
      exact Subsingleton.elim _ _
    simp only [quantitativePrefixCutEquations, G₀]
    rw [hresidue]
  have hrootSelected : ∀ o ∈ active, ∀ z ∈ cell o,
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations G₀)
        (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) = o := by
    intro o _ho z hz
    have hzData := (Finset.mem_filter.mp hz).2
    have hlabel := hzData.2 root
      (PrimeSubsetPrefix.root_mem_surviving P (allowed z) depth)
    rw [hrootEquation z (Finset.filter_subset _ _ hz)] at hlabel
    exact hlabel
  have hcellBox : ∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
      |(integralAffineMap u z m i : ℝ) - center i| ≤ Rbox := by
    intro o _ho z hz i
    exact hbox z (Finset.filter_subset _ _ hz) i
  obtain ⟨degree, hrootData, hrootMass, hactiveCard, hpersistentBound⟩ :=
    hrootSplit highConstant sourceEquations hprime hgeometricPrime hhom hdegree
      G₀ hG₀data.1 hG₀data.2 cell u m hm hrootSelected
      center Rbox hRbox hcellBox
  have hpartition :=
    FixedLeadingSurfaceSurvivorResidual.geometricPartition_of_survivor_auxiliaries
      sourceEquations hgeometricPrime hhom hdegree P depth X allowed u m
      blockDegree auxiliary z₀ hz₀ hallowed hauxiliary hauxZero hsource
  have hpersistentSum :
      (∑ o ∈ finiteEquationComponentOptions
          (finiteEquationFamilyUnion
            (qbarSurfaceEquationFamily sourceEquations)
            {MvPolynomial.map (algebraMap ℚ Qbar) G₀}),
        (X.filter fun z ↦
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
  refine ⟨degree, hrootData, hrootMass,
    hactiveCard.trans (Nat.mul_le_mul_left d hrootCap), ?_⟩
  intro hHigh
  have hpersistent := hpersistentBound hHigh
  dsimp only [active, cell, root, G₀] at hpersistent ⊢
  linarith

end CubicTenVariables.FixedLeadingSurfaceSurvivorDegreeSplitCountInternal
