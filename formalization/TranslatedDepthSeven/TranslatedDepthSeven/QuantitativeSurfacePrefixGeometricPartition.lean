import TranslatedDepthSeven.QuantitativeSurfacePrefixAuxiliaryChoice
import TranslatedDepthSeven.RootedGeometricComponentPersistence
import TranslatedDepthSeven.SurfaceProgressionResiduePairRecords

/-!
# The quantitative prefix auxiliaries as literal geometric cuts

The determinant construction produces a rational auxiliary for every
occupied residue at every vertex of the prime-prefix graph.  Here those
forms are inserted into the actual geometric minimal-prime partition over
`Qbar`.  The modulus-one root residue is unique, so its cut is independent
of the point.  Every changed-edge cell is simultaneously connected to the
existing squarefree residual-count theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 400000

local instance quantitativePrefixGeometricPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual geometric source equations together with the rational
auxiliary selected by the displacement residue at a prefix vertex. -/
def quantitativePrefixCutEquations
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (z : Fin 3 → ℤ) (v : PrimeSubsetPrefix.Vertex P depth) :
    Finset (MvPolynomial (Fin 4) Qbar) :=
  qbarSurfaceCutEquationFamily sourceEquations
    (auxiliary v (integralResidueVector z))

/-- The corresponding homogeneous progression point over `Qbar`. -/
def quantitativePrefixCoordinate
    (u : Fin 3 → ℤ) (m : ℕ) (z : Fin 3 → ℤ) : Fin 4 → Qbar :=
  fun i => (progressionHomogeneousPoint u m z i : Qbar)

/-- The changed-label cell appearing in the rooted graph partition. -/
def quantitativePrefixChangedEdgeCell
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (v w : PrimeSubsetPrefix.Vertex P depth) : Finset (Fin 3 → ℤ) :=
  X.filter fun z =>
    v ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth ∧
    w ∈ PrimeSubsetPrefix.survivingVertices P (allowed z) depth ∧
    (PrimeSubsetPrefix.graph P depth).Adj v w ∧
    selectedFiniteEquationComponent
        (quantitativePrefixCutEquations sourceEquations auxiliary z v)
        (quantitativePrefixCoordinate u m z) ≠
      selectedFiniteEquationComponent
        (quantitativePrefixCutEquations sourceEquations auxiliary z w)
        (quantitativePrefixCoordinate u m z)

/-- The actual prefix cuts satisfy the common-root geometric partition.
The displayed root form is one of the determinant auxiliaries and its
component-option set is bounded by the literal Bezout degree product. -/
theorem quantitativePrefixAuxiliaries_geometricPartition
    {d b : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (P : Finset ℕ) (depth : ℕ)
    (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (u : Fin 3 → ℤ) (m : ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (z₀ : Fin 3 → ℤ) (hz₀ : z₀ ∈ X)
    (hallowed : ∀ z ∈ X, allowed z ⊆ P)
    (hauxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∀ ρ ∈ occupiedIntegralResidues (PrimeSubsetPrefix.modulus v) X,
        (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
          auxiliary v ρ ∉ finiteEquationIdeal sourceEquations)
    (hauxZero : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∀ z ∈ X, MvPolynomial.eval
        (fun i => (progressionHomogeneousPoint u m z i : ℚ))
          (auxiliary v (integralResidueVector z)) = 0)
    (hsource : ∀ z ∈ X,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations) :
    let root := PrimeSubsetPrefix.root P depth
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
                  (quantitativePrefixCutEquations sourceEquations auxiliary z v)
                  (quantitativePrefixCoordinate u m z) = o).card) ∧
      (finiteEquationComponentOptions
        (finiteEquationFamilyUnion
          (qbarSurfaceEquationFamily sourceEquations) {G₀})).card ≤
        d * (b + blockDegree root) := by
  classical
  dsimp only
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := MvPolynomial.map (algebraMap ℚ Qbar)
    (auxiliary root (integralResidueVector z₀))
  have hrootOccupied : integralResidueVector z₀ ∈
      occupiedIntegralResidues (PrimeSubsetPrefix.modulus root) X :=
    mem_occupiedIntegralResidues_iff.mpr ⟨z₀, hz₀, rfl⟩
  have hrootData := hauxiliary root _ hrootOccupied
  have hprimeE : (finiteEquationIdeal
      (qbarSurfaceEquationFamily sourceEquations)).IsPrime := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact hgeometricPrime
  have hhomE : (finiteEquationIdeal
      (qbarSurfaceEquationFamily sourceEquations)).IsHomogeneous
        (homogeneousSubmodule (Fin 4) Qbar) := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) _ hhom
  have hdegreeE : HasProjectiveDimensionDegree
      (finiteEquationIdeal (qbarSurfaceEquationFamily sourceEquations)) 2 d := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarHasProjectiveDimensionDegree_of_rational _ hdegree hgeometricPrime
  have hG₀hom : G₀.IsHomogeneous (b + blockDegree root) := by
    exact hrootData.1.map (algebraMap ℚ Qbar)
  have hG₀not : G₀ ∉ finiteEquationIdeal
      (qbarSurfaceEquationFamily sourceEquations) := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarMap_not_mem_extendedIdeal_of_not_mem _ _ hrootData.2
  have hrootEquations : ∀ z ∈ X,
      quantitativePrefixCutEquations sourceEquations auxiliary z root =
        finiteEquationFamilyUnion
          (qbarSurfaceEquationFamily sourceEquations) {G₀} := by
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
    rfl
  have hzero : ∀ z ∈ X, ∀ v ∈
      PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
      quantitativePrefixCoordinate u m z ∈
        finiteAffineCommonZeroLocus
          (quantitativePrefixCutEquations sourceEquations auxiliary z v) := by
    intro z hz v _hv f hf
    change MvPolynomial.eval
      (fun i => (progressionHomogeneousPoint u m z i : Qbar)) f = 0
    unfold quantitativePrefixCutEquations at hf
    unfold qbarSurfaceCutEquationFamily at hf
    rw [mem_finiteEquationFamilyUnion] at hf
    rcases hf with hf | hf
    · obtain ⟨g, hg, rfl⟩ :=
        (mem_qbarSurfaceEquationFamily sourceEquations f).mp hf
      rw [eval_qbarMap_progression, hsource z hz g hg, map_zero]
    · have hf' : f = MvPolynomial.map (algebraMap ℚ Qbar)
          (auxiliary v (integralResidueVector z)) := by
        simpa using hf
      subst f
      rw [eval_qbarMap_progression, hauxZero v z hz, map_zero]
  have hpartition := geometricSurface_prefix_partition_with_rootLabelBound
    (K := Qbar) (N := 3) (d := d)
    (e₀ := b + blockDegree root)
    (qbarSurfaceEquationFamily sourceEquations)
    hprimeE hhomE hdegreeE G₀ hG₀hom hG₀not
    P depth X allowed
    (quantitativePrefixCutEquations sourceEquations auxiliary)
    (quantitativePrefixCoordinate u m)
    hallowed hrootEquations hzero
  simpa only [quantitativePrefixChangedEdgeCell, root, G₀] using hpartition

/-- Every literal changed-edge cell from the preceding partition satisfies
the squarefree residual estimate.  The endpoint moduli inherit all modular
hypotheses from their prime subsets; no record-count premise remains. -/
theorem card_quantitativePrefixChangedEdgeCell_le_squarefree
    {d b : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (P : Finset ℕ) (depth : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (hm : 0 < m) (hPm : ∀ p ∈ P, ¬ p ∣ m)
    (u : Fin 3 → ℤ) (X : Finset (Fin 3 → ℤ))
    (allowed : (Fin 3 → ℤ) → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hauxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∀ ρ ∈ occupiedIntegralResidues (PrimeSubsetPrefix.modulus v) X,
        (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
          auxiliary v ρ ∉ finiteEquationIdeal sourceEquations)
    (hauxZero : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      ∀ z ∈ X, MvPolynomial.eval
        (fun i => (progressionHomogeneousPoint u m z i : ℚ))
          (auxiliary v (integralResidueVector z)) = 0)
    (hsource : ∀ z ∈ X,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        finiteAffineCommonZeroLocus sourceEquations)
    (hzero : ∀ z ∈ X,
      MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0)
    (hsmooth : ∀ z ∈ X, ∀ p ∈ P, ∃ i,
      (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
        (MvPolynomial.pderiv i
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0)
    (v w : PrimeSubsetPrefix.Vertex P depth) :
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
  let S := quantitativePrefixChangedEdgeCell sourceEquations auxiliary
    u m X allowed v w
  have hsubset : S ⊆ X := Finset.filter_subset _ _
  have hvP : v.1 ⊆ P := (PrimeSubsetPrefix.mem_vertices.mp v.2).1
  have hwP : w.1 ⊆ P := (PrimeSubsetPrefix.mem_vertices.mp w.2).1
  have hvPrime : ∀ p ∈ v.1, p.Prime := fun p hp => hP p (hvP hp)
  have hwPrime : ∀ p ∈ w.1, p.Prime := fun p hp => hP p (hwP hp)
  have hvSquarefree : Squarefree (PrimeSubsetPrefix.modulus v) :=
    primeProduct_squarefree hvPrime
  have hwSquarefree : Squarefree (PrimeSubsetPrefix.modulus w) :=
    primeProduct_squarefree hwPrime
  have hvm : Nat.Coprime (PrimeSubsetPrefix.modulus v) m := by
    rw [PrimeSubsetPrefix.modulus, primeProduct, Nat.coprime_prod_left_iff]
    intro p hp
    exact (hvPrime p hp).coprime_iff_not_dvd.mpr (hPm p (hvP hp))
  have hwm : Nat.Coprime (PrimeSubsetPrefix.modulus w) m := by
    rw [PrimeSubsetPrefix.modulus, primeProduct, Nat.coprime_prod_left_iff]
    intro p hp
    exact (hwPrime p hp).coprime_iff_not_dvd.mpr (hPm p (hwP hp))
  have hvSmooth : ∀ z ∈ S, ∀ p, p.Prime →
      p ∣ PrimeSubsetPrefix.modulus v → ∃ i,
        (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
          (MvPolynomial.pderiv i
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0 := by
    intro z hz p hp hpmod
    have hpv : p ∈ v.1 := by
      rw [← primeFactors_primeProduct hvPrime]
      exact Nat.mem_primeFactors.mpr
        ⟨hp, hpmod, primeProduct_ne_zero hvPrime⟩
    exact hsmooth z (hsubset hz) p (hvP hpv)
  have hwSmooth : ∀ z ∈ S, ∀ p, p.Prime →
      p ∣ PrimeSubsetPrefix.modulus w → ∃ i,
        (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
          (MvPolynomial.pderiv i
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0 := by
    intro z hz p hp hpmod
    have hpw : p ∈ w.1 := by
      rw [← primeFactors_primeProduct hwPrime]
      exact Nat.mem_primeFactors.mpr
        ⟨hp, hpmod, primeProduct_ne_zero hwPrime⟩
    exact hsmooth z (hsubset hz) p (hwP hpw)
  apply card_rationalSurfaceProgression_changed_residueAuxiliaries_le_squarefree
    hm sourceEquations hgeometricPrime hhom hdegree F
    hvSquarefree hwSquarefree hvm hwm u S
    (auxiliary v) (auxiliary w)
  · intro ρ hρ
    exact hauxiliary v ρ (occupiedIntegralResidues_mono hsubset hρ)
  · intro ρ hρ
    exact hauxiliary w ρ (occupiedIntegralResidues_mono hsubset hρ)
  · intro z hz
    exact hsource z (hsubset hz)
  · intro z hz
    exact hzero z (hsubset hz)
  · exact hvSmooth
  · exact hwSmooth
  · intro z hz
    exact hauxZero v z (hsubset hz)
  · intro z hz
    exact hauxZero w z (hsubset hz)
  · intro z hz
    exact (Finset.mem_filter.mp hz).2.2.2.2

end

end TranslatedDepthSeven
