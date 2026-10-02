import TranslatedDepthSeven.RankSevenNodeRecords

/-!
# Finite persistent surface records

The persistent surface branch is indexed here by completely explicit finite
data.  A record consists of a reservoir modulus, an occupied residue modulo
that modulus, a projective surface component of the corresponding source
section, and one mark from a fixed finite type.  Its point cell retains the
exact residue, component zero-locus, and mark equalities.

Only finite-set identities and the exact selected-component specification
are used.  In particular this file assumes no uniform component bound, no
degree bound, and no estimate for rational points on a component.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance rankSevenPersistentPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- One finite index for the persistent surface contribution. -/
structure RankSevenPersistentRecord
    (P : Finset ℕ) (k markCount : ℕ) where
  modulus : ReservoirModulus P k
  residue : Fin 13 → ZMod modulus.1
  component : Ideal (MvPolynomial (Fin 14) ℚ)
  mark : Fin markCount

/-- The records above one fixed modulus and residue, before imposing
occupancy of that residue. -/
def rankSevenPersistentRecordsAtNode
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k markCount : ℕ}
    (q : ReservoirModulus P k) (rho : Fin 13 → ZMod q.1) :
    Finset (RankSevenPersistentRecord P k markCount) := by
  classical
  exact (rankSevenSurfaceNodeComponents
    p x₀ equations CF C q.1 rho).biUnion fun I ↦
      (Finset.univ : Finset (Fin markCount)).image fun lambda ↦
        { modulus := q, residue := rho, component := I, mark := lambda }

/-- The record count above one residue is bounded by the number of its
surface components times the number of marks. -/
theorem card_rankSevenPersistentRecordsAtNode_le
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k markCount : ℕ}
    (q : ReservoirModulus P k) (rho : Fin 13 → ZMod q.1) :
    (rankSevenPersistentRecordsAtNode
      (markCount := markCount) p x₀ equations CF C q rho).card ≤
      (rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card * markCount := by
  classical
  let components := rankSevenSurfaceNodeComponents
    p x₀ equations CF C q.1 rho
  change
    (components.biUnion fun I ↦
      (Finset.univ : Finset (Fin markCount)).image fun lambda ↦
        RankSevenPersistentRecord.mk q rho I lambda).card ≤
      components.card * markCount
  calc
    (components.biUnion fun I ↦
        (Finset.univ : Finset (Fin markCount)).image fun lambda ↦
          RankSevenPersistentRecord.mk q rho I lambda).card ≤
        ∑ I ∈ components,
          ((Finset.univ : Finset (Fin markCount)).image fun lambda ↦
            RankSevenPersistentRecord.mk q rho I lambda).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _I ∈ components, markCount := by
      apply Finset.sum_le_sum
      intro I _hI
      have himage :
          ((Finset.univ : Finset (Fin markCount)).image fun lambda ↦
            RankSevenPersistentRecord.mk q rho I lambda).card ≤
            (Finset.univ : Finset (Fin markCount)).card :=
        Finset.card_image_le
      simpa using himage
    _ = components.card * markCount := by simp

/-- All records over all occupied residues and reservoir moduli. -/
def occupiedRankSevenPersistentRecords
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount : ℕ) :
    Finset (RankSevenPersistentRecord P k markCount) := by
  classical
  exact (Finset.univ : Finset (ReservoirModulus P k)).biUnion fun q ↦
    (occupiedIntegralResidues q.1
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)).biUnion
        fun rho ↦
      rankSevenPersistentRecordsAtNode
        (markCount := markCount) p x₀ equations CF C q rho

@[simp]
theorem mem_occupiedRankSevenPersistentRecords_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount : ℕ)
    (record : RankSevenPersistentRecord P k markCount) :
    record ∈ occupiedRankSevenPersistentRecords
        p x₀ equations CF C P k markCount ↔
      record.residue ∈ occupiedIntegralResidues record.modulus.1
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) ∧
      record.component ∈ rankSevenSurfaceNodeComponents
        p x₀ equations CF C record.modulus.1 record.residue := by
  classical
  constructor
  · intro hrecord
    obtain ⟨q, _hq, hresidueUnion⟩ := Finset.mem_biUnion.mp hrecord
    obtain ⟨rho, hoccupied, hnodeRecord⟩ :=
      Finset.mem_biUnion.mp hresidueUnion
    obtain ⟨I, hI, hmarkRecord⟩ := Finset.mem_biUnion.mp hnodeRecord
    obtain ⟨lambda, _hlambda, hEq⟩ := Finset.mem_image.mp hmarkRecord
    cases hEq
    exact ⟨hoccupied, hI⟩
  · rintro ⟨hoccupied, hcomponent⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨record.modulus, Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨record.residue, hoccupied, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨record.component, hcomponent, ?_⟩
    exact Finset.mem_image.mpr
      ⟨record.mark, Finset.mem_univ _, rfl⟩

/-- The exact finite cardinality bound for the full persistent record list,
in its direct nested-sum form. -/
theorem card_occupiedRankSevenPersistentRecords_le_sum
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount : ℕ) :
    (occupiedRankSevenPersistentRecords
      p x₀ equations CF C P k markCount).card ≤
      ∑ q : ReservoirModulus P k,
        ∑ rho ∈ occupiedIntegralResidues q.1
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
          (rankSevenSurfaceNodeComponents
            p x₀ equations CF C q.1 rho).card * markCount := by
  classical
  let chart := depthSevenNormalizedJacobianChartCell
    p x₀ equations CF C
  calc
    (occupiedRankSevenPersistentRecords
        p x₀ equations CF C P k markCount).card ≤
        ∑ q : ReservoirModulus P k,
          ((occupiedIntegralResidues q.1 chart).biUnion fun rho ↦
            rankSevenPersistentRecordsAtNode
              (markCount := markCount)
              p x₀ equations CF C q rho).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ q : ReservoirModulus P k,
        ∑ rho ∈ occupiedIntegralResidues q.1 chart,
          (rankSevenPersistentRecordsAtNode
            (markCount := markCount)
            p x₀ equations CF C q rho).card := by
      apply Finset.sum_le_sum
      intro q _hq
      exact Finset.card_biUnion_le
    _ ≤ ∑ q : ReservoirModulus P k,
        ∑ rho ∈ occupiedIntegralResidues q.1 chart,
          (rankSevenSurfaceNodeComponents
            p x₀ equations CF C q.1 rho).card * markCount := by
      apply Finset.sum_le_sum
      intro q _hq
      apply Finset.sum_le_sum
      intro rho _hrho
      exact card_rankSevenPersistentRecordsAtNode_le
        (markCount := markCount) p x₀ equations CF C q rho

/-- Factored form of the persistent-record cardinality bound. -/
theorem card_occupiedRankSevenPersistentRecords_le_markCount_mul_sum
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount : ℕ) :
    (occupiedRankSevenPersistentRecords
      p x₀ equations CF C P k markCount).card ≤
      markCount *
        ∑ q : ReservoirModulus P k,
          ∑ rho ∈ occupiedIntegralResidues q.1
              (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
            (rankSevenSurfaceNodeComponents
              p x₀ equations CF C q.1 rho).card := by
  have h := card_occupiedRankSevenPersistentRecords_le_sum
    p x₀ equations CF C P k markCount
  simpa [Finset.mul_sum, Finset.sum_mul, Nat.mul_comm] using h

/-- The points in one persistent record, with the mark supplied by an
arbitrary pointwise marking function. -/
def rankSevenPersistentRecordPointCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k markCount : ℕ}
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount) :
    Finset (IntVector 13) :=
  (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
    fun z ↦
      (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
          record.residue ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
          affineIdealZeroLocus record.component ∧
      markOf z = record.mark

@[simp]
theorem mem_rankSevenPersistentRecordPointCell_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k markCount : ℕ}
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (z : IntVector 13) :
    z ∈ rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record ↔
      z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C ∧
      (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
        record.residue ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus record.component ∧
      markOf z = record.mark := by
  classical
  simp [rankSevenPersistentRecordPointCell]

/-- Pointwise exact cover by persistent records.  The caller supplies the
modulus, component, and mark assigned to each point, together with the
literal equality saying that the assigned component is its surface label at
that modulus. -/
theorem finitePointSet_subset_persistentRecordUnion
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (modulusOf : IntVector 13 → ReservoirModulus P k)
    (componentOf : IntVector 13 → Ideal (MvPolynomial (Fin 14) ℚ))
    (markOf : IntVector 13 → Fin markCount)
    (hchart : ∀ z ∈ X,
      z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
    (hlabel : ∀ z ∈ X,
      rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z (modulusOf z) =
          some (componentOf z)) :
    X ⊆ (occupiedRankSevenPersistentRecords
        p x₀ equations CF C P k markCount).biUnion fun record ↦
      rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record := by
  classical
  intro z hz
  have hzChart := hchart z hz
  obtain ⟨hselected, d, hdegree⟩ :=
    (rankSevenStaticSurfaceLabel_eq_some_iff
      p x₀ equations CF C denominator P k hP hlower
      z (modulusOf z) (componentOf z)).1 (hlabel z hz)
  have hcomponent : componentOf z ∈ rankSevenSurfaceNodeComponents
      p x₀ equations CF C (modulusOf z).1
        (integralResidueVector z : Fin 13 → ZMod (modulusOf z).1) :=
    rankSevenStaticSelectedSurfaceComponent_mem_nodeComponents
      p x₀ equations CF C denominator P k hP hlower
      z (modulusOf z) (componentOf z) d hselected hdegree
  have hpointLe := (selectedFiniteEquationComponent_spec
    (rankSevenStaticSourceSectionEquations
      p x₀ equations CF C denominator P k hP hlower (modulusOf z) z)
    (fun i ↦ (integralAffineChartVector z i : ℚ)) hselected).2
  have hpoint : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
      affineIdealZeroLocus (componentOf z) := fun f hf ↦
    RingHom.mem_ker.mp (hpointLe hf)
  let record : RankSevenPersistentRecord P k markCount :=
    { modulus := modulusOf z
      residue := integralResidueVector z
      component := componentOf z
      mark := markOf z }
  have hoccupied : record.residue ∈
      occupiedIntegralResidues record.modulus.1
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) :=
    mem_occupiedIntegralResidues_iff.mpr ⟨z, hzChart, rfl⟩
  have hrecord : record ∈ occupiedRankSevenPersistentRecords
      p x₀ equations CF C P k markCount :=
    (mem_occupiedRankSevenPersistentRecords_iff
      p x₀ equations CF C P k markCount record).2
        ⟨hoccupied, hcomponent⟩
  exact Finset.mem_biUnion.mpr
    ⟨record, hrecord,
      (mem_rankSevenPersistentRecordPointCell_iff
        p x₀ equations CF C markOf record z).2
          ⟨hzChart, rfl, hpoint, rfl⟩⟩

/-- Cardinal form of the pointwise exact persistent-record cover. -/
theorem card_finitePointSet_le_sum_persistentRecordCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (modulusOf : IntVector 13 → ReservoirModulus P k)
    (componentOf : IntVector 13 → Ideal (MvPolynomial (Fin 14) ℚ))
    (markOf : IntVector 13 → Fin markCount)
    (hchart : ∀ z ∈ X,
      z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
    (hlabel : ∀ z ∈ X,
      rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z (modulusOf z) =
          some (componentOf z)) :
    X.card ≤ ∑ record ∈ occupiedRankSevenPersistentRecords
        p x₀ equations CF C P k markCount,
      (rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record).card := by
  calc
    X.card ≤ ((occupiedRankSevenPersistentRecords
        p x₀ equations CF C P k markCount).biUnion fun record ↦
      rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record).card :=
      Finset.card_le_card
        (finitePointSet_subset_persistentRecordUnion
          p x₀ equations CF C denominator P k markCount hP hlower
          X modulusOf componentOf markOf hchart hlabel)
    _ ≤ ∑ record ∈ occupiedRankSevenPersistentRecords
        p x₀ equations CF C P k markCount,
      (rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record).card := Finset.card_biUnion_le

end

end TranslatedDepthSeven
