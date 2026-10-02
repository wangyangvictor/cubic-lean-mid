import TranslatedDepthSeven.RankSevenNodeRecords

/-!
# The finite non-surface node-record cover

At a surviving modulus, every point of the normalized rank-seven chart lies
on its residue-indexed source section.  Consequently its selected actual
minimal-prime component is nonempty.  If the surface label is `none`, that
selected component therefore has no projective dimension-two Hilbert
certificate.

This file packages that observation as a literal finite cover.  Its indices
are an occupied residue modulo the fixed reservoir modulus and a non-surface
minimal prime from the source section at that residue.  No bound for the
number, degree, dimension, or rational points of these components is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance rankSevenNodeRecordPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The actual minimal-prime components at a residue node which do not have
projective dimension two. -/
def rankSevenNonSurfaceNodeComponents
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    Finset (Ideal (MvPolynomial (Fin 14) ℚ)) := by
  classical
  exact (rankSevenNodeComponents p x₀ equations CF C q rho).filter
    fun I ↦ ¬ ∃ d : ℕ, HasProjectiveDimensionDegree I 2 d

@[simp]
theorem mem_rankSevenNonSurfaceNodeComponents_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q)
    (I : Ideal (MvPolynomial (Fin 14) ℚ)) :
    I ∈ rankSevenNonSurfaceNodeComponents p x₀ equations CF C q rho ↔
      I ∈ rankSevenNodeComponents p x₀ equations CF C q rho ∧
      ¬ ∃ d : ℕ, HasProjectiveDimensionDegree I 2 d := by
  classical
  simp [rankSevenNonSurfaceNodeComponents]

/-- At a surviving chart point the selected minimal-prime component cannot
be empty, because the point lies on the complete source-section equation
family. -/
theorem rankSevenStaticSelectedComponent_ne_none_of_mem_reservoirCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q : ReservoirModulus P k)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1) :
    rankSevenStaticSelectedComponent
      p x₀ equations CF C denominator P k hP hlower z q ≠ none := by
  intro hnone
  have hzero :=
    integralAffineChartVector_mem_rankSevenStaticSourceSectionEquations
      p x₀ equations CF hhomogeneous C denominator P k hP hlower q z hz
  change selectedFiniteEquationComponent
      (rankSevenStaticSourceSectionEquations
        p x₀ equations CF C denominator P k hP hlower q z)
      (fun i ↦ (integralAffineChartVector z i : ℚ)) = none at hnone
  have hoff := (selectedFiniteEquationComponent_eq_none_iff
    (rankSevenStaticSourceSectionEquations
      p x₀ equations CF C denominator P k hP hlower q z)
    (fun i ↦ (integralAffineChartVector z i : ℚ))).1 hnone
  exact hoff hzero

/-- On the surviving node branch, `surfaceLabel = none` produces an actual
selected minimal-prime component with no projective dimension-two
certificate. -/
theorem exists_nonSurfaceSelectedComponent_of_surfaceLabel_eq_none
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (z : IntVector 13) (q : ReservoirModulus P k)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1)
    (hlabel : rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower z q = none) :
    ∃ I : Ideal (MvPolynomial (Fin 14) ℚ),
      rankSevenStaticSelectedComponent
          p x₀ equations CF C denominator P k hP hlower z q = some I ∧
      I ∈ rankSevenNonSurfaceNodeComponents p x₀ equations CF C q.1
        (integralResidueVector z : Fin 13 → ZMod q.1) ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus I := by
  have hselectedNe :=
    rankSevenStaticSelectedComponent_ne_none_of_mem_reservoirCell
      p x₀ equations CF hhomogeneous C denominator P k hP hlower z q hz
  obtain hselectedNone | ⟨I, hselected, hnonSurface⟩ :=
    (rankSevenStaticSurfaceLabel_eq_none_iff
      p x₀ equations CF C denominator P k hP hlower z q).1 hlabel
  · exact (hselectedNe hselectedNone).elim
  · have hnode : I ∈ rankSevenNodeComponents p x₀ equations CF C q.1
        (integralResidueVector z : Fin 13 → ZMod q.1) :=
      rankSevenStaticSelectedComponent_mem_nodeComponents
        p x₀ equations CF C denominator P k hP hlower z q I hselected
    have hnonSurfaceNode : I ∈ rankSevenNonSurfaceNodeComponents
        p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1) :=
      (mem_rankSevenNonSurfaceNodeComponents_iff
        p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1) I).2
        ⟨hnode, hnonSurface⟩
    have hpoint := (selectedFiniteEquationComponent_spec
      (rankSevenStaticSourceSectionEquations
        p x₀ equations CF C denominator P k hP hlower q z)
      (fun i ↦ (integralAffineChartVector z i : ℚ)) hselected).2
    exact ⟨I, hselected, hnonSurfaceNode, fun f hf ↦
      RingHom.mem_ker.mp (hpoint hf)⟩

/-- The finite datum retained at one non-surface node. -/
structure RankSevenNonSurfaceNodeRecord (q : ℕ) where
  residue : Fin 13 → ZMod q
  component : Ideal (MvPolynomial (Fin 14) ℚ)

/-- All non-surface component records over occupied residues modulo one
reservoir modulus. -/
def occupiedRankSevenNonSurfaceNodeRecords
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (q : ReservoirModulus P k) :
    Finset (RankSevenNonSurfaceNodeRecord q.1) := by
  classical
  exact (occupiedIntegralResidues q.1
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)).biUnion
      fun rho ↦
    (rankSevenNonSurfaceNodeComponents
      p x₀ equations CF C q.1 rho).image fun I ↦
        { residue := rho, component := I }

@[simp]
theorem mem_occupiedRankSevenNonSurfaceNodeRecords_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (q : ReservoirModulus P k)
    (record : RankSevenNonSurfaceNodeRecord q.1) :
    record ∈ occupiedRankSevenNonSurfaceNodeRecords
        p x₀ equations CF C q ↔
      record.residue ∈ occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) ∧
      record.component ∈ rankSevenNonSurfaceNodeComponents
        p x₀ equations CF C q.1 record.residue := by
  classical
  constructor
  · intro hrecord
    obtain ⟨rho, hoccupied, himage⟩ := Finset.mem_biUnion.mp hrecord
    obtain ⟨I, hI, hEq⟩ := Finset.mem_image.mp himage
    cases hEq
    exact ⟨hoccupied, hI⟩
  · rintro ⟨hoccupied, hcomponent⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨record.residue, hoccupied, Finset.mem_image.mpr ?_⟩
    exact ⟨record.component, hcomponent, rfl⟩

/-- The points contributing to `surfaceLabel = none` at one surviving
reservoir modulus. -/
def rankSevenNonSurfaceNodeCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) : Finset (IntVector 13) :=
  (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
    fun z ↦
      survivesTwoCertificates q ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) ∧
      rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z q = none

/-- The points in the occupied residue of a node record which lie on its
recorded component. -/
def rankSevenNonSurfaceNodeRecordPointCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} {q : ReservoirModulus P k}
    (record : RankSevenNonSurfaceNodeRecord q.1) :
    Finset (IntVector 13) :=
  (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
    fun z ↦
      (integralResidueVector z : Fin 13 → ZMod q.1) = record.residue ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus record.component

@[simp]
theorem mem_rankSevenNonSurfaceNodeRecordPointCell_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} {q : ReservoirModulus P k}
    (record : RankSevenNonSurfaceNodeRecord q.1) (z : IntVector 13) :
    z ∈ rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF C record ↔
      z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C ∧
      (integralResidueVector z : Fin 13 → ZMod q.1) = record.residue ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus record.component := by
  classical
  simp [rankSevenNonSurfaceNodeRecordPointCell]

/-- Every point of the actual non-surface node branch belongs to one finite
occupied residue/component record cell. -/
theorem rankSevenNonSurfaceNodeCell_subset_recordUnion
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) :
    rankSevenNonSurfaceNodeCell
        p x₀ equations CF C denominator P k hP hlower q ⊆
      (occupiedRankSevenNonSurfaceNodeRecords
        p x₀ equations CF C q).biUnion fun record ↦
          rankSevenNonSurfaceNodeRecordPointCell
            p x₀ equations CF C record := by
  classical
  intro z hz
  obtain ⟨hzChart, hsurvives, hlabel⟩ := Finset.mem_filter.mp hz
  have hzReservoir : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1 :=
    Finset.mem_filter.mpr ⟨hzChart, hsurvives⟩
  obtain ⟨I, _hselected, hI, hpoint⟩ :=
    exists_nonSurfaceSelectedComponent_of_surfaceLabel_eq_none
      p x₀ equations CF hhomogeneous C denominator P k hP hlower
      z q hzReservoir hlabel
  let record : RankSevenNonSurfaceNodeRecord q.1 :=
    { residue := integralResidueVector z, component := I }
  have hoccupied : record.residue ∈ occupiedIntegralResidues q.1
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) :=
    mem_occupiedIntegralResidues_iff.mpr ⟨z, hzChart, rfl⟩
  have hrecord : record ∈ occupiedRankSevenNonSurfaceNodeRecords
      p x₀ equations CF C q :=
    (mem_occupiedRankSevenNonSurfaceNodeRecords_iff
      p x₀ equations CF C q record).2 ⟨hoccupied, hI⟩
  exact Finset.mem_biUnion.mpr
    ⟨record, hrecord,
      (mem_rankSevenNonSurfaceNodeRecordPointCell_iff
        p x₀ equations CF C record z).2 ⟨hzChart, rfl, hpoint⟩⟩

/-- Cardinal form of the finite non-surface node-record cover. -/
theorem card_rankSevenNonSurfaceNodeCell_le_sum_recordCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) :
    (rankSevenNonSurfaceNodeCell
      p x₀ equations CF C denominator P k hP hlower q).card ≤
      ∑ record ∈ occupiedRankSevenNonSurfaceNodeRecords
          p x₀ equations CF C q,
        (rankSevenNonSurfaceNodeRecordPointCell
          p x₀ equations CF C record).card := by
  calc
    (rankSevenNonSurfaceNodeCell
        p x₀ equations CF C denominator P k hP hlower q).card ≤
        ((occupiedRankSevenNonSurfaceNodeRecords
          p x₀ equations CF C q).biUnion fun record ↦
            rankSevenNonSurfaceNodeRecordPointCell
              p x₀ equations CF C record).card :=
      Finset.card_le_card
        (rankSevenNonSurfaceNodeCell_subset_recordUnion
          p x₀ equations CF hhomogeneous C denominator P k hP hlower q)
    _ ≤ ∑ record ∈ occupiedRankSevenNonSurfaceNodeRecords
          p x₀ equations CF C q,
        (rankSevenNonSurfaceNodeRecordPointCell
          p x₀ equations CF C record).card := Finset.card_biUnion_le

/-- The occupied non-surface node-record list has cardinality at most the
sum of the literal non-surface component-list cardinalities over occupied
residues. -/
theorem card_occupiedRankSevenNonSurfaceNodeRecords_le_sum_components
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (q : ReservoirModulus P k) :
    (occupiedRankSevenNonSurfaceNodeRecords
      p x₀ equations CF C q).card ≤
      ∑ rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
        (rankSevenNonSurfaceNodeComponents
          p x₀ equations CF C q.1 rho).card := by
  calc
    (occupiedRankSevenNonSurfaceNodeRecords
        p x₀ equations CF C q).card ≤
        ∑ rho ∈ occupiedIntegralResidues q.1
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
          ((rankSevenNonSurfaceNodeComponents
            p x₀ equations CF C q.1 rho).image fun I ↦
              ({ residue := rho, component := I } :
                RankSevenNonSurfaceNodeRecord q.1)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
        (rankSevenNonSurfaceNodeComponents
          p x₀ equations CF C q.1 rho).card := by
      apply Finset.sum_le_sum
      intro rho _hrho
      exact Finset.card_image_le

end

end TranslatedDepthSeven
