import TranslatedDepthSeven.RankSevenFiniteRecordPartition

/-!
# Record covers which retain certificate survival

The coarse finite record covers are convenient for describing the algebraic
components, but their record cells range over every occupied residue of the
ambient rank-seven chart.  For the square-free residue estimate one must not
forget that the modulus attached to a contributing point avoids both the
fixed denominator certificate and the evaluated Jacobian certificate.

This file intersects every node and edge record cell with the literal branch
from which it arose and deletes empty records.  Thus every retained record
has an actual witness carrying the required certificate-survival statement.
No cardinality or geometric estimate is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance survivingRecordPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Non-surface node records -/

/-- The part of a node record cell which really belongs to the surviving
`none`-label branch at its displayed modulus. -/
def rankSevenSurvivingNonSurfaceNodeRecordPointCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k)
    (record : RankSevenNonSurfaceNodeRecord q.1) :
    Finset (IntVector 13) :=
  (rankSevenNonSurfaceNodeRecordPointCell
      p x₀ equations CF C record).filter fun z ↦
    z ∈ rankSevenNonSurfaceNodeCell
      p x₀ equations CF C denominator P k hP hlower q

@[simp]
theorem mem_rankSevenSurvivingNonSurfaceNodeRecordPointCell_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k)
    (record : RankSevenNonSurfaceNodeRecord q.1) (z : IntVector 13) :
    z ∈ rankSevenSurvivingNonSurfaceNodeRecordPointCell
        p x₀ equations CF C denominator P k hP hlower q record ↔
      z ∈ rankSevenNonSurfaceNodeRecordPointCell
          p x₀ equations CF C record ∧
      z ∈ rankSevenNonSurfaceNodeCell
          p x₀ equations CF C denominator P k hP hlower q := by
  classical
  simp [rankSevenSurvivingNonSurfaceNodeRecordPointCell]

/-- Delete every coarse node record whose surviving branch cell is empty. -/
def occupiedRankSevenSurvivingNonSurfaceNodeRecords
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) :
    Finset (RankSevenNonSurfaceNodeRecord q.1) :=
  (occupiedRankSevenNonSurfaceNodeRecords
      p x₀ equations CF C q).filter fun record ↦
    (rankSevenSurvivingNonSurfaceNodeRecordPointCell
      p x₀ equations CF C denominator P k hP hlower q record).Nonempty

@[simp]
theorem mem_occupiedRankSevenSurvivingNonSurfaceNodeRecords_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k)
    (record : RankSevenNonSurfaceNodeRecord q.1) :
    record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF C denominator P k hP hlower q ↔
      record ∈ occupiedRankSevenNonSurfaceNodeRecords
          p x₀ equations CF C q ∧
      (rankSevenSurvivingNonSurfaceNodeRecordPointCell
        p x₀ equations CF C denominator P k hP hlower q record).Nonempty := by
  classical
  simp [occupiedRankSevenSurvivingNonSurfaceNodeRecords]

/-- Exact surviving-record cover of the actual non-surface node branch. -/
theorem rankSevenNonSurfaceNodeCell_subset_survivingRecordUnion
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
      (occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF C denominator P k hP hlower q).biUnion
          fun record ↦ rankSevenSurvivingNonSurfaceNodeRecordPointCell
            p x₀ equations CF C denominator P k hP hlower q record := by
  classical
  intro z hz
  obtain ⟨record, hrecord, hzrecord⟩ := Finset.mem_biUnion.mp
    (rankSevenNonSurfaceNodeCell_subset_recordUnion
      p x₀ equations CF hhomogeneous C denominator P k hP hlower q hz)
  have hzsurviving : z ∈ rankSevenSurvivingNonSurfaceNodeRecordPointCell
      p x₀ equations CF C denominator P k hP hlower q record :=
    Finset.mem_filter.mpr ⟨hzrecord, hz⟩
  have hrecordSurviving : record ∈
      occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF C denominator P k hP hlower q :=
    Finset.mem_filter.mpr ⟨hrecord, ⟨z, hzsurviving⟩⟩
  exact Finset.mem_biUnion.mpr
    ⟨record, hrecordSurviving, hzsurviving⟩

/-- Cardinal form of the exact surviving node-record cover. -/
theorem card_rankSevenNonSurfaceNodeCell_le_sum_survivingRecordCells
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
      ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
          p x₀ equations CF C denominator P k hP hlower q,
        (rankSevenSurvivingNonSurfaceNodeRecordPointCell
          p x₀ equations CF C denominator P k hP hlower q record).card := by
  calc
    (rankSevenNonSurfaceNodeCell
        p x₀ equations CF C denominator P k hP hlower q).card ≤
        ((occupiedRankSevenSurvivingNonSurfaceNodeRecords
          p x₀ equations CF C denominator P k hP hlower q).biUnion
            fun record ↦ rankSevenSurvivingNonSurfaceNodeRecordPointCell
              p x₀ equations CF C denominator P k hP hlower q record).card :=
      Finset.card_le_card
        (rankSevenNonSurfaceNodeCell_subset_survivingRecordUnion
          p x₀ equations CF hhomogeneous C denominator P k hP hlower q)
    _ ≤ ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
          p x₀ equations CF C denominator P k hP hlower q,
        (rankSevenSurvivingNonSurfaceNodeRecordPointCell
          p x₀ equations CF C denominator P k hP hlower q record).card :=
      Finset.card_biUnion_le

/-- Every retained node record has an actual witness at which its modulus
avoids both certificates. -/
theorem survivingNonSurfaceNodeRecord_has_certificateWitness
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k)
    (record : RankSevenNonSurfaceNodeRecord q.1)
    (hrecord : record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
      p x₀ equations CF C denominator P k hP hlower q) :
    ∃ z ∈ rankSevenSurvivingNonSurfaceNodeRecordPointCell
        p x₀ equations CF C denominator P k hP hlower q record,
      survivesTwoCertificates q ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) := by
  obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hrecord).2
  refine ⟨z, hz, ?_⟩
  exact (Finset.mem_filter.mp
    ((Finset.mem_filter.mp hz).2)).2.1

/-! ## Unequal-surface edge records -/

/-- The part of an edge record cell which really belongs to the surviving
unequal-label branch at the displayed ordered edge. -/
def rankSevenSurvivingSurfaceEdgeRecordPointCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :
    Finset (IntVector 13) :=
  (rankSevenSurfaceEdgeRecordPointCell
      p x₀ equations CF C P k record).filter fun z ↦
    z ∈ rankSevenSurfaceEdgeCell
      p x₀ equations CF C denominator P k hP hlower q r

/-- Delete every coarse edge record whose surviving unequal-label cell is
empty. -/
def occupiedRankSevenSurvivingSurfaceEdgeRecords
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k) :
    Finset (RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :=
  (occupiedRankSevenSurfaceEdgeRecords
      p x₀ equations CF C P k q r hP).filter fun record ↦
    (rankSevenSurvivingSurfaceEdgeRecordPointCell
      p x₀ equations CF C denominator P k hP hlower q r record).Nonempty

/-- Exact surviving-record cover of one actual unequal-surface edge cell. -/
theorem rankSevenSurfaceEdgeCell_subset_survivingRecordUnion
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
      (occupiedRankSevenSurvivingSurfaceEdgeRecords
        p x₀ equations CF C denominator P k hP hlower q r).biUnion
          fun record ↦ rankSevenSurvivingSurfaceEdgeRecordPointCell
            p x₀ equations CF C denominator P k hP hlower q r record := by
  classical
  intro z hz
  obtain ⟨record, hrecord, hzrecord⟩ := Finset.mem_biUnion.mp
    (rankSevenSurfaceEdgeCell_subset_recordUnion
      p x₀ equations CF C denominator P k hP hlower q r hz)
  have hzsurviving : z ∈ rankSevenSurvivingSurfaceEdgeRecordPointCell
      p x₀ equations CF C denominator P k hP hlower q r record :=
    Finset.mem_filter.mpr ⟨hzrecord, hz⟩
  have hrecordSurviving : record ∈
      occupiedRankSevenSurvivingSurfaceEdgeRecords
        p x₀ equations CF C denominator P k hP hlower q r :=
    Finset.mem_filter.mpr ⟨hrecord, ⟨z, hzsurviving⟩⟩
  exact Finset.mem_biUnion.mpr
    ⟨record, hrecordSurviving, hzsurviving⟩

/-- Cardinal form of the exact surviving edge-record cover. -/
theorem card_rankSevenSurfaceEdgeCell_le_sum_survivingRecordCells
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
      ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF C denominator P k hP hlower q r,
        (rankSevenSurvivingSurfaceEdgeRecordPointCell
          p x₀ equations CF C denominator P k hP hlower q r record).card := by
  calc
    (rankSevenSurfaceEdgeCell
        p x₀ equations CF C denominator P k hP hlower q r).card ≤
        ((occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF C denominator P k hP hlower q r).biUnion
            fun record ↦ rankSevenSurvivingSurfaceEdgeRecordPointCell
              p x₀ equations CF C denominator P k hP hlower q r record).card :=
      Finset.card_le_card
        (rankSevenSurfaceEdgeCell_subset_survivingRecordUnion
          p x₀ equations CF C denominator P k hP hlower q r)
    _ ≤ ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF C denominator P k hP hlower q r,
        (rankSevenSurvivingSurfaceEdgeRecordPointCell
          p x₀ equations CF C denominator P k hP hlower q r record).card :=
      Finset.card_biUnion_le

/-- Every retained edge record has an actual witness at which both endpoint
moduli avoid both certificates. -/
theorem survivingSurfaceEdgeRecord_has_certificateWitness
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF C denominator P k hP hlower q r) :
    ∃ z ∈ rankSevenSurvivingSurfaceEdgeRecordPointCell
        p x₀ equations CF C denominator P k hP hlower q r record,
      survivesTwoCertificates q ((p.m : ℤ) * denominator)
          (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) ∧
        survivesTwoCertificates r ((p.m : ℤ) * denominator)
          (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) := by
  obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hrecord).2
  refine ⟨z, hz, ?_⟩
  have hzEdge := (Finset.mem_filter.mp hz).2
  exact ⟨(Finset.mem_filter.mp hzEdge).2.1,
    (Finset.mem_filter.mp hzEdge).2.2.1⟩

/-- A retained edge record comes from an actual directed edge of the
reservoir graph.  This is the predicate needed to invoke the proved lcm
scale bound. -/
theorem survivingSurfaceEdgeRecord_adj
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF C denominator P k hP hlower q r) :
    (modulusReservoirGraph P k hP).Adj q r := by
  obtain ⟨z, hz, _⟩ := survivingSurfaceEdgeRecord_has_certificateWitness
    p x₀ equations CF C denominator P k hP hlower q r record hrecord
  have hzEdge := (Finset.mem_filter.mp hz).2
  exact (Finset.mem_filter.mp hzEdge).2.2.2.1

/-- Certificate survival propagates from the retained record's witness to
every point of any frontier cell attached to that record.  The reason is
literal: both points have the same residue modulo `lcm(q,r)`, hence modulo
each endpoint modulus, and integral polynomial evaluation respects that
coordinate congruence. -/
theorem survivingSurfaceEdgeRecord_frontierPoint_survives
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF C denominator P k hP hlower q r)
    (L : Ideal (MvPolynomial (Fin 14) ℚ)) (z : IntVector 13)
    (hz : z ∈ rankSevenSurfaceEdgeFrontierPointCell
      p x₀ equations CF C P k record L) :
    survivesTwoCertificates q ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) ∧
      survivesTwoCertificates r ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) := by
  obtain ⟨w, hw, hwsurvives⟩ :=
    survivingSurfaceEdgeRecord_has_certificateWitness
      p x₀ equations CF C denominator P k hP hlower q r record hrecord
  have hwRecord : w ∈ rankSevenSurfaceEdgeRecordPointCell
      p x₀ equations CF C P k record := (Finset.mem_filter.mp hw).1
  have hwResidue :=
    (mem_rankSevenSurfaceEdgeRecordPointCell_iff
      p x₀ equations CF C P k record w).mp hwRecord |>.2.1
  have hzResidue :=
    (mem_rankSevenSurfaceEdgeFrontierPointCell_iff
      p x₀ equations CF C P k record L z).mp hz |>.2.1
  have hResidueLcm :
      (integralResidueVector w : Fin 13 → ZMod (Nat.lcm q.1 r.1)) =
        integralResidueVector z := hwResidue.trans hzResidue.symm
  have hResidueQ := congrArg
    (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1)) hResidueLcm
  have hResidueR := congrArg
    (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1)) hResidueLcm
  have hcoordinateQ : ∀ i,
      (integralAffineMap x₀ w p.m i : ZMod q.1) =
        (integralAffineMap x₀ z p.m i : ZMod q.1) := by
    intro i
    have hi := congrFun hResidueQ i
    simp only [reduceResidueVector, integralResidueVector] at hi
    have hi' : (w i : ZMod q.1) = (z i : ZMod q.1) := by
      simpa using hi
    simp only [integralAffineMap, Int.cast_add, Int.cast_mul,
      Int.cast_natCast]
    rw [hi']
  have hcoordinateR : ∀ i,
      (integralAffineMap x₀ w p.m i : ZMod r.1) =
        (integralAffineMap x₀ z p.m i : ZMod r.1) := by
    intro i
    have hi := congrFun hResidueR i
    simp only [reduceResidueVector, integralResidueVector] at hi
    have hi' : (w i : ZMod r.1) = (z i : ZMod r.1) := by
      simpa using hi
    simp only [integralAffineMap, Int.cast_add, Int.cast_mul,
      Int.cast_natCast]
    rw [hi']
  refine ⟨⟨hwsurvives.1.1, ?_⟩, ⟨hwsurvives.2.1, ?_⟩⟩
  · exact coprime_eval_natAbs_of_coordinate_cast_eq C.determinant
      (integralAffineMap x₀ w p.m) (integralAffineMap x₀ z p.m)
      hcoordinateQ hwsurvives.1.2
  · exact coprime_eval_natAbs_of_coordinate_cast_eq C.determinant
      (integralAffineMap x₀ w p.m) (integralAffineMap x₀ z p.m)
      hcoordinateR hwsurvives.2.2

/-- A surviving edge-record cell is covered by the same literal minimal
prime frontiers as its coarse parent cell.  The record index, however, now
retains both certificate survival and adjacency. -/
theorem card_survivingSurfaceEdgeRecordPointCell_le_sum_frontierCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1)) :
    (rankSevenSurvivingSurfaceEdgeRecordPointCell
      p x₀ equations CF C denominator P k hP hlower q r record).card ≤
      ∑ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        (rankSevenSurfaceEdgeFrontierPointCell
          p x₀ equations CF C P k record L).card := by
  calc
    (rankSevenSurvivingSurfaceEdgeRecordPointCell
        p x₀ equations CF C denominator P k hP hlower q r record).card ≤
        (rankSevenSurfaceEdgeRecordPointCell
          p x₀ equations CF C P k record).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ ∑ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        (rankSevenSurfaceEdgeFrontierPointCell
          p x₀ equations CF C P k record L).card :=
      card_rankSevenSurfaceEdgeRecordPointCell_le_sum_frontierCells
        p x₀ equations CF C P k record

/-- Corrected finite-record partition.  Unlike the coarse predecessor, its
node record list contains only records with a surviving witness, while its
edge record list contains only records with a surviving witness on an actual
adjacent ordered pair.  Hence subsequent residue and lcm estimates may be
applied without reintroducing either missing predicate. -/
theorem card_rankSevenChart_le_survivingNodeRecords_edgeFrontiers_persistent
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (H A : ℝ)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤ H ^ A → (E₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P E₁ E₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo P E₁ E₂) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected)
    (hfixedNe : (p.m : ℤ) * denominator ≠ 0)
    (hfixedSize : ((((p.m : ℤ) * denominator).natAbs : ℕ) : ℝ) ≤ H ^ A)
    (hdetNe : ∀ z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C,
      MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant ≠ 0)
    (hdetSize : ∀ z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C,
      (((MvPolynomial.eval (integralAffineMap x₀ z p.m)
        C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ A) :
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).card ≤
      (∑ q : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF C denominator P k hP hlower q,
          (rankSevenSurvivingNonSurfaceNodeRecordPointCell
            p x₀ equations CF C denominator P k hP hlower q record).card) +
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF C denominator P k hP hlower q r,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            (rankSevenSurfaceEdgeFrontierPointCell
              p x₀ equations CF C P k record L).card) +
      (∑ o ∈ occurringRankSevenStaticSurfaceLabels
          p x₀ equations CF C denominator P k hP hlower,
        ((depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
          fun z ↦ o ≠ none ∧ ∀ q : ReservoirModulus P k,
            survivesTwoCertificates q ((p.m : ℤ) * denominator)
              (MvPolynomial.eval (integralAffineMap x₀ z p.m)
                C.determinant) →
            rankSevenStaticSurfaceLabel
              p x₀ equations CF C denominator P k hP hlower z q = o).card) := by
  have hpartition := card_rankSevenChart_le_surfaceVertex_edge_persistent
    p x₀ equations CF C denominator P k hP hlower H A hsurvival
      hfixedNe hfixedSize hdetNe hdetSize
  have hnodes :
      (∑ q : ReservoirModulus P k,
        (rankSevenNonSurfaceNodeCell
          p x₀ equations CF C denominator P k hP hlower q).card) ≤
      ∑ q : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF C denominator P k hP hlower q,
          (rankSevenSurvivingNonSurfaceNodeRecordPointCell
            p x₀ equations CF C denominator P k hP hlower q record).card := by
    apply Finset.sum_le_sum
    intro q _hq
    exact card_rankSevenNonSurfaceNodeCell_le_sum_survivingRecordCells
      p x₀ equations CF hhomogeneous C denominator P k hP hlower q
  have hedges :
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        (rankSevenSurfaceEdgeCell
          p x₀ equations CF C denominator P k hP hlower q r).card) ≤
      ∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF C denominator P k hP hlower q r,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            (rankSevenSurfaceEdgeFrontierPointCell
              p x₀ equations CF C P k record L).card := by
    apply Finset.sum_le_sum
    intro q _hq
    apply Finset.sum_le_sum
    intro r _hr
    calc
      (rankSevenSurfaceEdgeCell
          p x₀ equations CF C denominator P k hP hlower q r).card ≤
          ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF C denominator P k hP hlower q r,
            (rankSevenSurvivingSurfaceEdgeRecordPointCell
              p x₀ equations CF C denominator P k hP hlower q r record).card :=
        card_rankSevenSurfaceEdgeCell_le_sum_survivingRecordCells
          p x₀ equations CF C denominator P k hP hlower q r
      _ ≤ ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF C denominator P k hP hlower q r,
            ∑ L ∈ finiteMinimalPrimes
                (record.leftComponent ⊔ record.rightComponent),
              (rankSevenSurfaceEdgeFrontierPointCell
                p x₀ equations CF C P k record L).card := by
        apply Finset.sum_le_sum
        intro record _hrecord
        exact card_survivingSurfaceEdgeRecordPointCell_le_sum_frontierCells
          p x₀ equations CF C denominator P k hP hlower q r record
  exact hpartition.trans
    (Nat.add_le_add (Nat.add_le_add hnodes hedges) (le_refl _))

end

end TranslatedDepthSeven
