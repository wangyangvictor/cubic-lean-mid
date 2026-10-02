import TranslatedDepthSeven.RankSevenNodeRecords

/-!
# The finite edge-record cover

For a fixed directed reservoir edge `(q,r)`, this file replaces the
pointwise assertion that the two selected surface labels differ by a
literal finite cover.  Its indices are exactly:

* a residue vector modulo `lcm(q,r)` which is occupied by the original
  normalized point set; and
* two distinct minimal-prime surface components of the two source-section
  ideals obtained by reducing that residue modulo `q` and `r`.

The point cell attached to such a record is cut out by the supremum of the
two component ideals.  No estimate for a cell, no bound for the number of
components, and no geometric decomposition hypothesis occurs here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The points contributing to the unequal, nonempty surface-label term
at one directed reservoir edge. -/
def rankSevenSurfaceEdgeCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k) : Finset (IntVector 13) :=
  (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
    fun z ↦
      survivesTwoCertificates q ((p.m : ℤ) * denominator)
          (MvPolynomial.eval (integralAffineMap x₀ z p.m)
            C.determinant) ∧
      survivesTwoCertificates r ((p.m : ℤ) * denominator)
          (MvPolynomial.eval (integralAffineMap x₀ z p.m)
            C.determinant) ∧
      (modulusReservoirGraph P k hP).Adj q r ∧
      rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower z q ≠
        rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower z r ∧
      rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower z q ≠ none ∧
      rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower z r ≠ none

/-- Retain only those finite edge records whose lcm-residue is actually
occupied by the normalized chart cell. -/
def occupiedRankSevenSurfaceEdgeRecords
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ)
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime) :
    Finset (RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :=
  (rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP).filter
    fun record ↦ record.residue ∈
      occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)

@[simp]
theorem mem_occupiedRankSevenSurfaceEdgeRecords_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ)
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :
    record ∈ occupiedRankSevenSurfaceEdgeRecords
        p x₀ equations CF C P k q r hP ↔
      record ∈ rankSevenSurfaceEdgeRecords
        p x₀ equations CF C q r hP ∧
      record.residue ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) := by
  classical
  simp [occupiedRankSevenSurfaceEdgeRecords]

/-- The points in the occupied lcm-residue attached to an edge record which
also lie on the literal intersection of its two components. -/
def rankSevenSurfaceEdgeRecordPointCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ)
    {q r : ReservoirModulus P k}
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :
    Finset (IntVector 13) :=
  (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
    fun z ↦
      (integralResidueVector z : Fin 13 → ZMod (Nat.lcm q.1 r.1)) =
          record.residue ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus
          (record.leftComponent ⊔ record.rightComponent)

@[simp]
theorem mem_rankSevenSurfaceEdgeRecordPointCell_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ)
    {q r : ReservoirModulus P k}
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (z : IntVector 13) :
    z ∈ rankSevenSurfaceEdgeRecordPointCell
        p x₀ equations CF C P k record ↔
      z ∈ depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C ∧
      (integralResidueVector z : Fin 13 → ZMod (Nat.lcm q.1 r.1)) =
        record.residue ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus
          (record.leftComponent ⊔ record.rightComponent) := by
  classical
  simp [rankSevenSurfaceEdgeRecordPointCell]

/-- Every point of one unequal-label edge cell belongs to one occupied
lcm-residue/component record cell. -/
theorem rankSevenSurfaceEdgeCell_subset_recordUnion
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k) :
    rankSevenSurfaceEdgeCell
        p x₀ equations CF C denominator P k hP hlower q r ⊆
      (occupiedRankSevenSurfaceEdgeRecords
        p x₀ equations CF C P k q r hP).biUnion fun record ↦
          rankSevenSurfaceEdgeRecordPointCell
            p x₀ equations CF C P k record := by
  classical
  intro z hz
  obtain ⟨hzChart, hqSurvives, hrSurvives, hqr, hne, hqne, hrne⟩ :=
    Finset.mem_filter.mp hz
  obtain ⟨record, hrecord, hresidue, hzero⟩ :=
    exists_rankSevenSurfaceEdgeRecord_of_edge
      p x₀ equations CF C denominator P k hP hlower z q r
      hzChart hqSurvives hrSurvives hqr hne hqne hrne
  have hoccupied : record.residue ∈
      occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) := by
    exact mem_occupiedIntegralResidues_iff.mpr
      ⟨z, hzChart, hresidue.symm⟩
  have hrecordOccupied : record ∈ occupiedRankSevenSurfaceEdgeRecords
      p x₀ equations CF C P k q r hP :=
    (mem_occupiedRankSevenSurfaceEdgeRecords_iff
      p x₀ equations CF C P k q r hP record).2
        ⟨hrecord, hoccupied⟩
  exact Finset.mem_biUnion.mpr ⟨record, hrecordOccupied,
    (mem_rankSevenSurfaceEdgeRecordPointCell_iff
      p x₀ equations CF C P k record z).2
      ⟨hzChart, hresidue.symm, hzero⟩⟩

/-- Cardinal form of the finite edge-record cover.  The right side is now
ready for the standard component/degree decomposition and the rescaled
Pila estimate on each literal record. -/
theorem card_rankSevenSurfaceEdgeCell_le_sum_recordCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k) :
    (rankSevenSurfaceEdgeCell
      p x₀ equations CF C denominator P k hP hlower q r).card ≤
      ∑ record ∈ occupiedRankSevenSurfaceEdgeRecords
          p x₀ equations CF C P k q r hP,
        (rankSevenSurfaceEdgeRecordPointCell
          p x₀ equations CF C P k record).card := by
  calc
    (rankSevenSurfaceEdgeCell
      p x₀ equations CF C denominator P k hP hlower q r).card ≤
        ((occupiedRankSevenSurfaceEdgeRecords
          p x₀ equations CF C P k q r hP).biUnion fun record ↦
            rankSevenSurfaceEdgeRecordPointCell
              p x₀ equations CF C P k record).card :=
      Finset.card_le_card
        (rankSevenSurfaceEdgeCell_subset_recordUnion
          p x₀ equations CF C denominator P k hP hlower q r)
    _ ≤ ∑ record ∈ occupiedRankSevenSurfaceEdgeRecords
          p x₀ equations CF C P k q r hP,
        (rankSevenSurfaceEdgeRecordPointCell
          p x₀ equations CF C P k record).card :=
      Finset.card_biUnion_le

/-! ## Exact finite bounds for the record indices -/

/-- For a fixed lcm residue, all pairs of surface components at its two
reductions.  Equal component pairs are retained in this envelope; deleting
them can only decrease the cardinality. -/
def rankSevenSurfaceEdgeRecordPairsAtResidue
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (q r : ReservoirModulus P k)
    (rho : Fin 13 → ZMod (Nat.lcm q.1 r.1)) :
    Finset (RankSevenEdgeRecord (Nat.lcm q.1 r.1)) := by
  classical
  exact (rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
    (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).biUnion
      fun Iq ↦
    (rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
      (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).image
        fun Ir ↦
      { residue := rho, leftComponent := Iq, rightComponent := Ir }

@[simp]
theorem mem_rankSevenSurfaceEdgeRecordPairsAtResidue_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (q r : ReservoirModulus P k)
    (rho : Fin 13 → ZMod (Nat.lcm q.1 r.1))
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :
    record ∈ rankSevenSurfaceEdgeRecordPairsAtResidue
        p x₀ equations CF C q r rho ↔
      record.residue = rho ∧
      record.leftComponent ∈ rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1
          (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho) ∧
      record.rightComponent ∈ rankSevenSurfaceNodeComponents
        p x₀ equations CF C r.1
          (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho) := by
  classical
  constructor
  · intro hrecord
    obtain ⟨Iq, hIq, himage⟩ := Finset.mem_biUnion.mp hrecord
    obtain ⟨Ir, hIr, hEq⟩ := Finset.mem_image.mp himage
    cases hEq
    exact ⟨rfl, hIq, hIr⟩
  · rintro ⟨hresidue, hleft, hright⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨record.leftComponent, ?_, ?_⟩
    · exact hleft
    · apply Finset.mem_image.mpr
      refine ⟨record.rightComponent, ?_, ?_⟩
      · exact hright
      · cases record
        simp_all

/-- The number of component-pair records over one residue is bounded by the
product of the two literal node-component cardinalities. -/
theorem card_rankSevenSurfaceEdgeRecordPairsAtResidue_le
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (q r : ReservoirModulus P k)
    (rho : Fin 13 → ZMod (Nat.lcm q.1 r.1)) :
    (rankSevenSurfaceEdgeRecordPairsAtResidue
      p x₀ equations CF C q r rho).card ≤
      (rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
        (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).card *
      (rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
        (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).card := by
  classical
  let left := rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
    (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)
  let right := rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
    (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)
  change
    (left.biUnion fun Iq ↦
      right.image fun Ir ↦
        RankSevenEdgeRecord.mk rho Iq Ir).card ≤
      left.card * right.card
  calc
    (left.biUnion fun Iq ↦
        right.image fun Ir ↦
          RankSevenEdgeRecord.mk rho Iq Ir).card ≤
        ∑ Iq ∈ left,
          (right.image fun Ir ↦
            RankSevenEdgeRecord.mk rho Iq Ir).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _Iq ∈ left, right.card := by
      apply Finset.sum_le_sum
      intro Iq _hIq
      exact Finset.card_image_le
    _ = left.card * right.card := by simp

/-- The occupied distinct records form a subset of the union of the full
component-pair envelopes over the occupied lcm residues. -/
theorem occupiedRankSevenSurfaceEdgeRecords_subset_residuePairUnion
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ)
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime) :
    occupiedRankSevenSurfaceEdgeRecords
        p x₀ equations CF C P k q r hP ⊆
      (occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)).biUnion
          fun rho ↦ rankSevenSurfaceEdgeRecordPairsAtResidue
            p x₀ equations CF C q r rho := by
  classical
  intro record hrecord
  obtain ⟨hfull, hoccupied⟩ :=
    (mem_occupiedRankSevenSurfaceEdgeRecords_iff
      p x₀ equations CF C P k q r hP record).1 hrecord
  obtain ⟨hleft, hright, _hne⟩ :=
    (mem_rankSevenSurfaceEdgeRecords_iff
      p x₀ equations CF C q r hP record).1 hfull
  apply Finset.mem_biUnion.mpr
  refine ⟨record.residue, hoccupied, ?_⟩
  exact (mem_rankSevenSurfaceEdgeRecordPairsAtResidue_iff
    p x₀ equations CF C q r record.residue record).2
      ⟨rfl, hleft, hright⟩

/-- Exact finite combinatorial bound for the occupied edge-record list.
No uniform bound for either component list is used. -/
theorem card_occupiedRankSevenSurfaceEdgeRecords_le_sum_products
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ)
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime) :
    (occupiedRankSevenSurfaceEdgeRecords
      p x₀ equations CF C P k q r hP).card ≤
      ∑ rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
        (rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
          (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).card *
        (rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
          (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).card := by
  let residues := occupiedIntegralResidues (Nat.lcm q.1 r.1)
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
  calc
    (occupiedRankSevenSurfaceEdgeRecords
        p x₀ equations CF C P k q r hP).card ≤
        (residues.biUnion fun rho ↦
          rankSevenSurfaceEdgeRecordPairsAtResidue
            p x₀ equations CF C q r rho).card :=
      Finset.card_le_card
        (occupiedRankSevenSurfaceEdgeRecords_subset_residuePairUnion
          p x₀ equations CF C P k q r hP)
    _ ≤ ∑ rho ∈ residues,
        (rankSevenSurfaceEdgeRecordPairsAtResidue
          p x₀ equations CF C q r rho).card := Finset.card_biUnion_le
    _ ≤ ∑ rho ∈ residues,
        (rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
          (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).card *
        (rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
          (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).card := by
      apply Finset.sum_le_sum
      intro rho _hrho
      exact card_rankSevenSurfaceEdgeRecordPairsAtResidue_le
        p x₀ equations CF C q r rho

/-! ## Decomposition of each record intersection into minimal primes -/

/-- The points in a fixed edge-record residue which lie on one displayed
minimal-prime component of the component intersection. -/
def rankSevenSurfaceEdgeFrontierPointCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ) {q r : ReservoirModulus P k}
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (L : Ideal (MvPolynomial (Fin 14) ℚ)) : Finset (IntVector 13) :=
  (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
    fun z ↦
      (integralResidueVector z : Fin 13 → ZMod (Nat.lcm q.1 r.1)) =
          record.residue ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus L

@[simp]
theorem mem_rankSevenSurfaceEdgeFrontierPointCell_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ) {q r : ReservoirModulus P k}
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (L : Ideal (MvPolynomial (Fin 14) ℚ)) (z : IntVector 13) :
    z ∈ rankSevenSurfaceEdgeFrontierPointCell
        p x₀ equations CF C P k record L ↔
      z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C ∧
      (integralResidueVector z : Fin 13 → ZMod (Nat.lcm q.1 r.1)) =
        record.residue ∧
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus L := by
  classical
  simp [rankSevenSurfaceEdgeFrontierPointCell]

/-- A record point cell is covered by the actual minimal primes over the
supremum of its two component ideals.  Every resulting cell retains the
same lcm residue equality. -/
theorem rankSevenSurfaceEdgeRecordPointCell_subset_frontierUnion
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ) {q r : ReservoirModulus P k}
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :
    rankSevenSurfaceEdgeRecordPointCell
        p x₀ equations CF C P k record ⊆
      (finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent)).biUnion fun L ↦
          rankSevenSurfaceEdgeFrontierPointCell
            p x₀ equations CF C P k record L := by
  classical
  intro z hz
  obtain ⟨hzChart, hresidue, hzero⟩ :=
    (mem_rankSevenSurfaceEdgeRecordPointCell_iff
      p x₀ equations CF C P k record z).1 hz
  let point : Fin 14 → ℚ :=
    fun i ↦ (integralAffineChartVector z i : ℚ)
  let T : Ideal (MvPolynomial (Fin 14) ℚ) :=
    RingHom.ker (MvPolynomial.eval point)
  letI : T.IsPrime := RingHom.ker_isPrime _
  have hsupT : record.leftComponent ⊔ record.rightComponent ≤ T := by
    intro f hf
    exact RingHom.mem_ker.mpr (hzero f hf)
  obtain ⟨L, hL, hLT⟩ := exists_finiteMinimalPrime_le hsupT
  apply Finset.mem_biUnion.mpr
  refine ⟨L, hL,
    (mem_rankSevenSurfaceEdgeFrontierPointCell_iff
      p x₀ equations CF C P k record L z).2 ?_⟩
  refine ⟨hzChart, hresidue, ?_⟩
  intro f hf
  exact RingHom.mem_ker.mp (hLT hf)

/-- Cardinal form of the minimal-prime frontier cover of one record cell. -/
theorem card_rankSevenSurfaceEdgeRecordPointCell_le_sum_frontierCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ) {q r : ReservoirModulus P k}
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :
    (rankSevenSurfaceEdgeRecordPointCell
      p x₀ equations CF C P k record).card ≤
      ∑ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        (rankSevenSurfaceEdgeFrontierPointCell
          p x₀ equations CF C P k record L).card := by
  calc
    (rankSevenSurfaceEdgeRecordPointCell
        p x₀ equations CF C P k record).card ≤
        ((finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent)).biUnion fun L ↦
            rankSevenSurfaceEdgeFrontierPointCell
              p x₀ equations CF C P k record L).card :=
      Finset.card_le_card
        (rankSevenSurfaceEdgeRecordPointCell_subset_frontierUnion
          p x₀ equations CF C P k record)
    _ ≤ ∑ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        (rankSevenSurfaceEdgeFrontierPointCell
          p x₀ equations CF C P k record L).card := Finset.card_biUnion_le

end

end TranslatedDepthSeven
