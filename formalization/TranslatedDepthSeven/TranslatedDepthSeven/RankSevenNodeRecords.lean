import TranslatedDepthSeven.RankSevenQualifiedSurfacePartition
import TranslatedDepthSeven.FiniteComponentFrontier

/-!
# Finite node and edge records for the rank-seven reservoir

The source-section equations selected at a reservoir modulus are indexed by
the residue vector, rather than by an integral lift.  This file records the
resulting finite algebraic data explicitly.  A node record is one minimal
prime over the equations attached to `(q, rho)`.  For two moduli `q,r`, an
edge record consists of one residue modulo `lcm(q,r)` and one surface
component from each of the two reduced node records.

Thus the list of possible edge records is finite before any rational points
are counted.  If a point has two distinct nonempty surface labels at the
ends of an edge, it belongs to the intersection of the two components in
one of these records.  Every irreducible component of that intersection has
affine-cone dimension strictly less than three.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Coordinatewise reduction of a residue vector along a divisibility
`q ∣ R`. -/
def reduceResidueVector {N q R : ℕ} (h : q ∣ R)
    (rho : Fin N → ZMod R) : Fin N → ZMod q :=
  fun i ↦ ZMod.castHom h (ZMod q) (rho i)

/-- Reducing an integral residue vector along `q ∣ R` gives the integral
residue vector modulo `q`. -/
@[simp]
theorem reduceResidueVector_integralResidueVector
    {N q R : ℕ} (h : q ∣ R) (z : IntVector N) :
    reduceResidueVector h
        (integralResidueVector z : Fin N → ZMod R) =
      (integralResidueVector z : Fin N → ZMod q) := by
  funext i
  simp [reduceResidueVector, integralResidueVector]

/-- The literal ideal of the source-section equations at one residue node. -/
def rankSevenNodeEquationIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    Ideal (MvPolynomial (Fin 14) ℚ) :=
  finiteEquationIdeal
    (rankSevenSourceSectionEquationsAtResidue
      p x₀ equations CF C q rho)

/-- The finite list of actual minimal-prime components at the node
`(q,rho)`. -/
def rankSevenNodeComponents
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    Finset (Ideal (MvPolynomial (Fin 14) ℚ)) :=
  finiteMinimalPrimes
    (rankSevenNodeEquationIdeal p x₀ equations CF C q rho)

/-- The node components whose homogeneous Hilbert data have projective
dimension two. -/
def rankSevenSurfaceNodeComponents
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    Finset (Ideal (MvPolynomial (Fin 14) ℚ)) := by
  classical
  exact (rankSevenNodeComponents p x₀ equations CF C q rho).filter
    fun I ↦ ∃ d : ℕ, HasProjectiveDimensionDegree I 2 d

@[simp]
theorem mem_rankSevenSurfaceNodeComponents_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q)
    (I : Ideal (MvPolynomial (Fin 14) ℚ)) :
    I ∈ rankSevenSurfaceNodeComponents p x₀ equations CF C q rho ↔
      I ∈ rankSevenNodeComponents p x₀ equations CF C q rho ∧
        ∃ d : ℕ, HasProjectiveDimensionDegree I 2 d := by
  classical
  simp [rankSevenSurfaceNodeComponents]

/-- A selected component is a member of the node list determined solely by
the displayed residue vector. -/
theorem rankSevenStaticSelectedComponent_mem_nodeComponents
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q : ReservoirModulus P k)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : rankSevenStaticSelectedComponent
      p x₀ equations CF C denominator P k hP hlower z q = some I) :
    I ∈ rankSevenNodeComponents p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1) := by
  have hspec := (selectedFiniteEquationComponent_spec
    (rankSevenStaticSourceSectionEquations
      p x₀ equations CF C denominator P k hP hlower q z)
    (fun i ↦ (integralAffineChartVector z i : ℚ)) hI).1
  simpa [rankSevenStaticSelectedComponent,
    rankSevenStaticSourceSectionEquations,
    rankSevenNodeComponents, rankSevenNodeEquationIdeal,
    finiteEquationMinimalPrimes] using hspec

/-- A selected projective surface component belongs to the surface-filtered
node list determined by the residue vector. -/
theorem rankSevenStaticSelectedSurfaceComponent_mem_nodeComponents
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q : ReservoirModulus P k)
    (I : Ideal (MvPolynomial (Fin 14) ℚ)) (d : ℕ)
    (hI : rankSevenStaticSelectedComponent
      p x₀ equations CF C denominator P k hP hlower z q = some I)
    (hd : HasProjectiveDimensionDegree I 2 d) :
    I ∈ rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1) := by
  exact (mem_rankSevenSurfaceNodeComponents_iff
    p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1) I).2
    ⟨rankSevenStaticSelectedComponent_mem_nodeComponents
      p x₀ equations CF C denominator P k hP hlower z q I hI,
      ⟨d, hd⟩⟩

/-- The data retained in one finite edge record. -/
structure RankSevenEdgeRecord (R : ℕ) where
  residue : Fin 13 → ZMod R
  leftComponent : Ideal (MvPolynomial (Fin 14) ℚ)
  rightComponent : Ideal (MvPolynomial (Fin 14) ℚ)

/-- All distinct pairs of projective surface components arising from the
two reductions of a residue modulo `lcm(q,r)`. -/
def rankSevenSurfaceEdgeRecords
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ}
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime) :
    Finset (RankSevenEdgeRecord (Nat.lcm q.1 r.1)) := by
  classical
  have hqSpec := primeFactors_spec_of_mem_modulusReservoir hP q.2
  have hrSpec := primeFactors_spec_of_mem_modulusReservoir hP r.2
  have hqPos : 0 < q.1 := by
    rw [← hqSpec.2.2]
    exact Nat.pos_of_ne_zero
      (primeProduct_ne_zero fun s hs ↦ hP s (hqSpec.1 hs))
  have hrPos : 0 < r.1 := by
    rw [← hrSpec.2.2]
    exact Nat.pos_of_ne_zero
      (primeProduct_ne_zero fun s hs ↦ hP s (hrSpec.1 hs))
  letI : NeZero (Nat.lcm q.1 r.1) :=
    ⟨Nat.ne_of_gt (Nat.lcm_pos hqPos hrPos)⟩
  exact (Finset.univ : Finset
      (Fin 13 → ZMod (Nat.lcm q.1 r.1))).biUnion fun rho ↦
    (rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
      (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).biUnion
        fun Iq ↦
      ((rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
        (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).filter
          fun Ir ↦ Iq ≠ Ir).image fun Ir ↦
        { residue := rho, leftComponent := Iq, rightComponent := Ir }

@[simp]
theorem mem_rankSevenSurfaceEdgeRecords_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ}
    (q r : ReservoirModulus P k)
    (hP : ∀ s ∈ P, s.Prime)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :
    record ∈ rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP ↔
      record.leftComponent ∈ rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1
          (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1)
            record.residue) ∧
      record.rightComponent ∈ rankSevenSurfaceNodeComponents
        p x₀ equations CF C r.1
          (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1)
            record.residue) ∧
      record.leftComponent ≠ record.rightComponent := by
  classical
  have hqSpec := primeFactors_spec_of_mem_modulusReservoir hP q.2
  have hrSpec := primeFactors_spec_of_mem_modulusReservoir hP r.2
  have hqPos : 0 < q.1 := by
    rw [← hqSpec.2.2]
    exact Nat.pos_of_ne_zero
      (primeProduct_ne_zero fun s hs ↦ hP s (hqSpec.1 hs))
  have hrPos : 0 < r.1 := by
    rw [← hrSpec.2.2]
    exact Nat.pos_of_ne_zero
      (primeProduct_ne_zero fun s hs ↦ hP s (hrSpec.1 hs))
  letI : NeZero (Nat.lcm q.1 r.1) :=
    ⟨Nat.ne_of_gt (Nat.lcm_pos hqPos hrPos)⟩
  constructor
  · intro hrecord
    simp only [rankSevenSurfaceEdgeRecords, Finset.mem_biUnion] at hrecord
    obtain ⟨rho, _hrho, Iq, hIq, hrecord⟩ := hrecord
    obtain ⟨Ir, hIr, hEq⟩ := Finset.mem_image.mp hrecord
    have hIrSpec := Finset.mem_filter.mp hIr
    cases hEq
    exact ⟨hIq, hIrSpec.1, hIrSpec.2⟩
  · rintro ⟨hIq, hIr, hne⟩
    simp only [rankSevenSurfaceEdgeRecords, Finset.mem_biUnion]
    refine ⟨record.residue, Finset.mem_univ _, record.leftComponent, hIq,
      ?_⟩
    exact Finset.mem_image.mpr
      ⟨record.rightComponent, Finset.mem_filter.mpr ⟨hIr, hne⟩, rfl⟩

/-- Every unequal nonempty surface-labelled edge point determines one of
the finite lcm-indexed records, and the point lies on the literal
intersection of the two recorded components. -/
theorem exists_rankSevenSurfaceEdgeRecord_of_edge
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q r : ReservoirModulus P k)
    (hz : z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C)
    (hqSurvives : survivesTwoCertificates q ((p.m : ℤ) * denominator)
      (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant))
    (hrSurvives : survivesTwoCertificates r ((p.m : ℤ) * denominator)
      (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant))
    (hqr : (modulusReservoirGraph P k hP).Adj q r)
    (hne : rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z q ≠
      rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z r)
    (hqne : rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower z q ≠ none)
    (hrne : rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower z r ≠ none) :
    ∃ record ∈ rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP,
      record.residue =
          (integralResidueVector z : Fin 13 → ZMod (Nat.lcm q.1 r.1)) ∧
        (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
          affineIdealZeroLocus
            (record.leftComponent ⊔ record.rightComponent) := by
  obtain ⟨Iq, Ir, dq, dr, hdistinct, hqSelected, hrSelected,
      hIq, hIr, hzero⟩ :=
    exists_distinct_rankSevenSurfaceComponents_of_edge
      p x₀ equations CF C denominator P k hP hlower z q r
      hz hqSurvives hrSurvives hqr hne hqne hrne
  let R := Nat.lcm q.1 r.1
  let rho : Fin 13 → ZMod R := integralResidueVector z
  let record : RankSevenEdgeRecord R :=
    { residue := rho, leftComponent := Iq, rightComponent := Ir }
  have hqNode : Iq ∈ rankSevenSurfaceNodeComponents
      p x₀ equations CF C q.1
        (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho) := by
    rw [reduceResidueVector_integralResidueVector]
    exact rankSevenStaticSelectedSurfaceComponent_mem_nodeComponents
      p x₀ equations CF C denominator P k hP hlower z q Iq dq
      hqSelected hIq
  have hrNode : Ir ∈ rankSevenSurfaceNodeComponents
      p x₀ equations CF C r.1
        (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho) := by
    rw [reduceResidueVector_integralResidueVector]
    exact rankSevenStaticSelectedSurfaceComponent_mem_nodeComponents
      p x₀ equations CF C denominator P k hP hlower z r Ir dr
      hrSelected hIr
  refine ⟨record, ?_, rfl, ?_⟩
  · exact (mem_rankSevenSurfaceEdgeRecords_iff
      p x₀ equations CF C q r hP record).2
      ⟨hqNode, hrNode, hdistinct⟩
  · exact hzero

/-- Every minimal prime over the intersection in a finite edge record has
affine-cone Krull dimension strictly below three. -/
theorem rankSevenSurfaceEdgeRecord_frontier_dimension_lt_three
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ}
    (q r : ReservoirModulus P k)
    (hP : ∀ s ∈ P, s.Prime)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈
      rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP)
    (L : Ideal (MvPolynomial (Fin 14) ℚ))
    (hL : L ∈ finiteMinimalPrimes
      (record.leftComponent ⊔ record.rightComponent)) :
    ringKrullDim (MvPolynomial (Fin 14) ℚ ⧸ L) < 3 := by
  obtain ⟨hleft, hright, hne⟩ :=
    (mem_rankSevenSurfaceEdgeRecords_iff
      p x₀ equations CF C q r hP record).1 hrecord
  obtain ⟨hleftNode, dleft, hleftDegree⟩ :=
    (mem_rankSevenSurfaceNodeComponents_iff
      p x₀ equations CF C q.1
        (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1)
          record.residue) record.leftComponent).1 hleft
  obtain ⟨hrightNode, dright, hrightDegree⟩ :=
    (mem_rankSevenSurfaceNodeComponents_iff
      p x₀ equations CF C r.1
        (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1)
          record.residue) record.rightComponent).1 hright
  letI : record.leftComponent.IsPrime :=
    isPrime_of_mem_finiteMinimalPrimes hleftNode
  letI : record.rightComponent.IsPrime :=
    isPrime_of_mem_finiteMinimalPrimes hrightNode
  have hleftDim : ringKrullDim
      (MvPolynomial (Fin 14) ℚ ⧸ record.leftComponent) = 3 := by
    simpa using hleftDegree.1
  have hrightDim : ringKrullDim
      (MvPolynomial (Fin 14) ℚ ⧸ record.rightComponent) = 3 := by
    simpa using hrightDegree.1
  exact (strict_frontier_and_dimension_drop_of_distinct_primes_same_dimension
    hne hleftDim hrightDim hL).2.2.2.2

end

end TranslatedDepthSeven
