import TranslatedDepthSeven.RankSevenRecordCardinality
import TranslatedDepthSeven.RankSevenPersistentMultiplicityOneRecordCover

/-!
# Cardinality of persistent records at one literal modulus

The global persistent record set is a union over reservoir moduli.  For the
CRT estimate one must keep that modulus visible, since certificate survival
is known only for moduli which actually occur.  This file gives the exact
per-modulus finite-set bounds and the elementary cover of any filtered record
family by those fibres.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance persistentCardinalityPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The broad persistent records whose stored modulus is exactly `q`. -/
def occupiedRankSevenPersistentRecordsAtModulus
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount : ℕ)
    (q : ReservoirModulus P k) :
    Finset (RankSevenPersistentRecord P k markCount) :=
  (occupiedRankSevenPersistentRecords
    p x₀ equations CF C P k markCount).filter fun record ↦
      record.modulus = q

/-- A broad record in the modulus fibre belongs to the explicit union of
node records over the occupied residues at that modulus. -/
theorem occupiedRankSevenPersistentRecordsAtModulus_subset_nodeUnion
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount : ℕ)
    (q : ReservoirModulus P k) :
    occupiedRankSevenPersistentRecordsAtModulus
        p x₀ equations CF C P k markCount q ⊆
      (occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C)).biUnion fun rho ↦
        rankSevenPersistentRecordsAtNode
          (markCount := markCount) p x₀ equations CF C q rho := by
  classical
  intro record hrecord
  obtain ⟨hbroad, hmodulus⟩ := Finset.mem_filter.mp hrecord
  cases record with
  | mk modulus residue component mark =>
      dsimp only at hmodulus
      subst modulus
      have hspec := (mem_occupiedRankSevenPersistentRecords_iff
        p x₀ equations CF C P k markCount
          { modulus := q, residue := residue,
            component := component, mark := mark }).mp hbroad
      apply Finset.mem_biUnion.mpr
      refine ⟨residue, hspec.1, ?_⟩
      unfold rankSevenPersistentRecordsAtNode
      apply Finset.mem_biUnion.mpr
      refine ⟨component, hspec.2, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨mark, Finset.mem_univ _, rfl⟩

/-- Uniform component mass gives the exact per-modulus record bound. -/
theorem card_occupiedRankSevenPersistentRecordsAtModulus_le
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount D : ℕ)
    (q : ReservoirModulus P k)
    (hcomponents : ∀ rho ∈ occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D) :
    (occupiedRankSevenPersistentRecordsAtModulus
      p x₀ equations CF C P k markCount q).card ≤
      (occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C)).card * (D * markCount) := by
  calc
    (occupiedRankSevenPersistentRecordsAtModulus
        p x₀ equations CF C P k markCount q).card ≤
        ((occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).biUnion fun rho ↦
          rankSevenPersistentRecordsAtNode
            (markCount := markCount)
              p x₀ equations CF C q rho).card :=
      Finset.card_le_card
        (occupiedRankSevenPersistentRecordsAtModulus_subset_nodeUnion
          p x₀ equations CF C P k markCount q)
    _ ≤ ∑ rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C),
        (rankSevenPersistentRecordsAtNode
          (markCount := markCount)
            p x₀ equations CF C q rho).card := Finset.card_biUnion_le
    _ ≤ ∑ _rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C), D * markCount := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact (card_rankSevenPersistentRecordsAtNode_le
        (markCount := markCount) p x₀ equations CF C q rho).trans
          (Nat.mul_le_mul_right markCount (hcomponents rho hrho))
    _ = (occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).card * (D * markCount) := by simp

/-- Any subfamily of broad persistent records is covered by the disjointly
specified modulus fibres.  Disjointness is not needed for this upper bound. -/
theorem card_persistentRecordSubfamily_le_sum_modulusFibres
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount : ℕ)
    (R : Finset (RankSevenPersistentRecord P k markCount)) :
    R.card ≤ ∑ q : ReservoirModulus P k,
      (R.filter fun record ↦ record.modulus = q).card := by
  calc
    R.card ≤ ((Finset.univ : Finset (ReservoirModulus P k)).biUnion
        fun q ↦ R.filter fun record ↦ record.modulus = q).card := by
      apply Finset.card_le_card
      intro record hrecord
      exact Finset.mem_biUnion.mpr
        ⟨record.modulus, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨hrecord, rfl⟩⟩
    _ ≤ ∑ q : ReservoirModulus P k,
        (R.filter fun record ↦ record.modulus = q).card :=
      Finset.card_biUnion_le

/-- A filtered subfamily in one modulus fibre is bounded by the broad
per-modulus family. -/
theorem card_persistentRecordSubfamilyAtModulus_le
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount : ℕ)
    (R : Finset (RankSevenPersistentRecord P k markCount))
    (hR : R ⊆ occupiedRankSevenPersistentRecords
      p x₀ equations CF C P k markCount)
    (q : ReservoirModulus P k) :
    (R.filter fun record ↦ record.modulus = q).card ≤
      (occupiedRankSevenPersistentRecordsAtModulus
        p x₀ equations CF C P k markCount q).card := by
  apply Finset.card_le_card
  intro record hrecord
  obtain ⟨hrecordR, hmodulus⟩ := Finset.mem_filter.mp hrecord
  exact Finset.mem_filter.mpr ⟨hR hrecordR, hmodulus⟩

end

end TranslatedDepthSeven
