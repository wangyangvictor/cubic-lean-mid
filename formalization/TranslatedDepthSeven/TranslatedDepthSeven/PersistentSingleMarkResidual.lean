import TranslatedDepthSeven.RankSevenPersistentDisplayedCertificateRecords
import TranslatedDepthSeven.DegreeOneCurveOccurrenceAssembly
import TranslatedDepthSeven.RankSevenPacketSalbergerComposition

/-!
# Exact set subtraction for the single-mark persistent records

With only one mark the record cell is the entire packet on its component.
Consequently all of its degree-one auxiliary-curve points are a subset of
the cell. A bound by their cardinality plus an error is therefore an exact
bound for the complementary point set. Only these complements are summed;
the linear points are retained as one union.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

theorem rankSevenPersistentSingleMarkPointCell_eq_packet
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (record : RankSevenPersistentRecord P k 1) :
    rankSevenPersistentRecordPointCell p x₀ equations CF Cchart
      displayedCertificateOneMarkOf record =
    rankSevenPacketPointsOnSourceComponent
      (integralResiduePacket
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF Cchart)
        record.residue) record.component := by
  classical
  ext z
  simp only [mem_rankSevenPersistentRecordPointCell_iff,
    mem_rankSevenPacketPointsOnSourceComponent_iff,
    integralResiduePacket, Finset.mem_filter]
  have hmark : displayedCertificateOneMarkOf z = record.mark := Subsingleton.elim _ _
  simp only [hmark, and_true]
  simp only [affineIdealZeroLocus, Set.mem_setOf_eq, and_assoc]

/-- Exact subtraction, not a change from a tagged sum to an untagged union. -/
theorem card_sdiff_cast_le_of_card_le_add
    {α : Type*} [DecidableEq α] (points lines : Finset α)
    (hsubset : lines ⊆ points) (error : ℝ)
    (hcount : (points.card : ℝ) ≤ (lines.card : ℝ) + error) :
    ((points \ lines).card : ℝ) ≤ error := by
  have hcard : ((points \ lines).card : ℝ) + (lines.card : ℝ) =
      (points.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsubset
  linarith

/-- A finite cover with one common union for its distinguished subsets.
No disjointness of the record cells is required. -/
theorem card_le_distinguishedUnion_add_sum_sdiff
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (points : Finset α) (records : Finset ι)
    (cell distinguished : ι → Finset α)
    (hcover : points ⊆ records.biUnion cell) :
    points.card ≤ (records.biUnion distinguished).card +
      ∑ i ∈ records, (cell i \ distinguished i).card := by
  classical
  have hsplit : points ⊆ records.biUnion distinguished ∪
      records.biUnion (fun i ↦ cell i \ distinguished i) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp (hcover hz)
    by_cases hzd : z ∈ distinguished i
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, hzd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_sdiff.mpr ⟨hzi, hzd⟩⟩)
  exact (Finset.card_le_card hsplit).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))

end

end TranslatedDepthSeven
