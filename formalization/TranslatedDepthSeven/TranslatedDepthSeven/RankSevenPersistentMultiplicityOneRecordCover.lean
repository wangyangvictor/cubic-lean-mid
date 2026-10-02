import TranslatedDepthSeven.RankSevenPersistentMultiplicityRecords

/-!
# Persistent records with actual multiplicity-one witnesses

The broad persistent-record list contains every occupied residue, every
surface component above that residue, and every mark.  For the terminal
argument one must retain only records which are actually supplied by the
persistent-surface construction.  This file performs that deletion
literally.

A retained record has an integral witness in the finite set under study.
At that witness the stored component is persistent, the record modulus
avoids the two static certificates and the marked local certificate, and
the stored special-fibre point has Hilbert--Samuel multiplicity one at every
prime factor of the modulus.  The resulting finite list still covers every
point assigned by `exists_finite_persistentSurface_multiplicityOne_records`.

Only finite-set reasoning and congruence invariance of integral polynomial
evaluation are used here.  No counting or geometric estimate is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance persistentMultiplicityOneCoverPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

set_option maxHeartbeats 4000000

/-- The actual witnesses retained by one persistent record.  Besides lying
in the record's literal point cell and in `X`, a witness retains all three
certificate conditions, persistence of the stored component, and the
factorwise multiplicity-one statements used by the terminal theorem. -/
def rankSevenPersistentMultiplicityOneWitnessCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) {markCount : ℕ}
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount) :
    Finset (IntVector 13) :=
  (rankSevenPersistentRecordPointCell
      p x₀ equations CF C markOf record).filter fun z ↦
    z ∈ X ∧
    z ∈ rankSevenPersistentSurfaceCell
      p x₀ equations CF C denominator P k hP hlower record.component ∧
    survivesTwoCertificates record.modulus
      ((p.m : ℤ) * denominator)
      (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) ∧
    Nat.Coprime record.modulus.1
      (integralSelectedJacobianChartCertificate
        localEquations selectedVar (menu (markOf z)) z).natAbs ∧
    rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower
        z record.modulus = some record.component ∧
    ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
      HasHilbertSamuelMultiplicityAt
        ((Nat.mem_primeFactors.mp hs).1)
        (projectiveSpecialFiberIdeal record.component)
        (rankSevenPersistentRecordPrimePoint record s hs) 2 1

@[simp]
theorem mem_rankSevenPersistentMultiplicityOneWitnessCell_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) {markCount : ℕ}
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (z : IntVector 13) :
    z ∈ rankSevenPersistentMultiplicityOneWitnessCell
        p x₀ equations CF C denominator P k hP hlower X
          localEquations selectedVar menu markOf record ↔
      z ∈ rankSevenPersistentRecordPointCell
          p x₀ equations CF C markOf record ∧
      z ∈ X ∧
      z ∈ rankSevenPersistentSurfaceCell
        p x₀ equations CF C denominator P k hP hlower record.component ∧
      survivesTwoCertificates record.modulus
        ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) ∧
      Nat.Coprime record.modulus.1
        (integralSelectedJacobianChartCertificate
          localEquations selectedVar (menu (markOf z)) z).natAbs ∧
      rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower
          z record.modulus = some record.component ∧
      ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
        HasHilbertSamuelMultiplicityAt
          ((Nat.mem_primeFactors.mp hs).1)
          (projectiveSpecialFiberIdeal record.component)
          (rankSevenPersistentRecordPrimePoint record s hs) 2 1 := by
  classical
  simp [rankSevenPersistentMultiplicityOneWitnessCell]

/-- Delete every broad persistent record which has no actual persistent
multiplicity-one witness in `X`. -/
def occupiedRankSevenPersistentMultiplicityOneRecords
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :
    Finset (RankSevenPersistentRecord P k markCount) :=
  (occupiedRankSevenPersistentRecords
    p x₀ equations CF C P k markCount).filter fun record ↦
      (rankSevenPersistentMultiplicityOneWitnessCell
        p x₀ equations CF C denominator P k hP hlower X
          localEquations selectedVar menu markOf record).Nonempty

@[simp]
theorem mem_occupiedRankSevenPersistentMultiplicityOneRecords_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount) :
    record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
        p x₀ equations CF C denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf ↔
      record ∈ occupiedRankSevenPersistentRecords
          p x₀ equations CF C P k markCount ∧
      (rankSevenPersistentMultiplicityOneWitnessCell
        p x₀ equations CF C denominator P k hP hlower X
          localEquations selectedVar menu markOf record).Nonempty := by
  classical
  simp [occupiedRankSevenPersistentMultiplicityOneRecords]

/-- Every retained record comes with an actual witness carrying all of the
displayed persistent and multiplicity-one data. -/
theorem persistentMultiplicityOneRecord_has_witness
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (hrecord : record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) :
    ∃ z, z ∈ rankSevenPersistentMultiplicityOneWitnessCell
      p x₀ equations CF C denominator P k hP hlower X
        localEquations selectedVar menu markOf record := by
  exact (Finset.mem_filter.mp hrecord).2

/-- A retained record is occupied and its broad record cell is nonempty. -/
theorem persistentMultiplicityOneRecord_occupied_and_nonempty
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (hrecord : record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) :
    record ∈ occupiedRankSevenPersistentRecords
        p x₀ equations CF C P k markCount ∧
      (rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record).Nonempty := by
  have hbroad := (Finset.mem_filter.mp hrecord).1
  obtain ⟨z, hz⟩ := persistentMultiplicityOneRecord_has_witness
    p x₀ equations CF C denominator P k markCount hP hlower X
      localEquations selectedVar menu markOf record hrecord
  exact ⟨hbroad, z,
    (mem_rankSevenPersistentMultiplicityOneWitnessCell_iff
      p x₀ equations CF C denominator P k hP hlower X
        localEquations selectedVar menu markOf record z).mp hz |>.1⟩

/-- Multiplicity one at every prime factor is now a property of every
retained record, not an unrecorded property of the point which selected it. -/
theorem persistentMultiplicityOneRecord_factorwise_multiplicityOne
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (hrecord : record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) :
    ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
      HasHilbertSamuelMultiplicityAt
        ((Nat.mem_primeFactors.mp hs).1)
        (projectiveSpecialFiberIdeal record.component)
        (rankSevenPersistentRecordPrimePoint record s hs) 2 1 := by
  obtain ⟨z, hz⟩ := persistentMultiplicityOneRecord_has_witness
    p x₀ equations CF C denominator P k markCount hP hlower X
      localEquations selectedVar menu markOf record hrecord
  exact (mem_rankSevenPersistentMultiplicityOneWitnessCell_iff
    p x₀ equations CF C denominator P k hP hlower X
      localEquations selectedVar menu markOf record z).mp hz |>.2.2.2.2.2.2

/-- If `X` belongs to one fixed persistent surface `I`, then every retained
record stores exactly `I`.  Indeed, the record modulus survives at its
witness, so persistence in `I` and persistence in the stored component give
two equal values of the same literal static label. -/
theorem persistentMultiplicityOneRecord_component_eq_fixedSurface
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (hX : X ⊆ rankSevenPersistentSurfaceCell
      p x₀ equations CF C denominator P k hP hlower I)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (hrecord : record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) :
    record.component = I := by
  obtain ⟨z, hz⟩ := persistentMultiplicityOneRecord_has_witness
    p x₀ equations CF C denominator P k markCount hP hlower X
      localEquations selectedVar menu markOf record hrecord
  have hzSpec := (mem_rankSevenPersistentMultiplicityOneWitnessCell_iff
    p x₀ equations CF C denominator P k hP hlower X
      localEquations selectedVar menu markOf record z).mp hz
  have hlabelRecord := hzSpec.2.2.2.2.2.1
  have hlabelI := (mem_rankSevenPersistentSurfaceCell_iff
    p x₀ equations CF C denominator P k hP hlower I z).mp
      (hX hzSpec.2.1) |>.2 record.modulus hzSpec.2.2.2.1
  exact Option.some.inj (hlabelRecord.symm.trans hlabelI)

/-- Certificate survival and the marked local-certificate coprimality pass
from a retained witness to every point of the broad record cell.  Both
claims follow from equality of the stored residue modulo the record
modulus; equality of the marks fixes the principal-open polynomial. -/
theorem persistentMultiplicityOneRecord_point_has_coprimality
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (hrecord : record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf)
    (z : IntVector 13)
    (hz : z ∈ rankSevenPersistentRecordPointCell
      p x₀ equations CF C markOf record) :
    survivesTwoCertificates record.modulus
        ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) ∧
      Nat.Coprime record.modulus.1
        (integralSelectedJacobianChartCertificate
          localEquations selectedVar (menu (markOf z)) z).natAbs := by
  obtain ⟨w, hw⟩ := persistentMultiplicityOneRecord_has_witness
    p x₀ equations CF C denominator P k markCount hP hlower X
      localEquations selectedVar menu markOf record hrecord
  have hwSpec := (mem_rankSevenPersistentMultiplicityOneWitnessCell_iff
    p x₀ equations CF C denominator P k hP hlower X
      localEquations selectedVar menu markOf record w).mp hw
  have hwRecord := hwSpec.1
  have hwSurvives := hwSpec.2.2.2.1
  have hwLocalCoprime := hwSpec.2.2.2.2.1
  have hwCell := (mem_rankSevenPersistentRecordPointCell_iff
    p x₀ equations CF C markOf record w).mp hwRecord
  have hzCell := (mem_rankSevenPersistentRecordPointCell_iff
    p x₀ equations CF C markOf record z).mp hz
  have hresidue :
      (integralResidueVector w : Fin 13 → ZMod record.modulus.1) =
        integralResidueVector z := hwCell.2.1.trans hzCell.2.1.symm
  have hcoordinate : ∀ i, (w i : ZMod record.modulus.1) =
      (z i : ZMod record.modulus.1) := by
    intro i
    have hi := congrFun hresidue i
    simpa [integralResidueVector] using hi
  have haffineCoordinate : ∀ i,
      (integralAffineMap x₀ w p.m i : ZMod record.modulus.1) =
        (integralAffineMap x₀ z p.m i : ZMod record.modulus.1) := by
    intro i
    simp only [integralAffineMap, Int.cast_add, Int.cast_mul,
      Int.cast_natCast]
    rw [hcoordinate i]
  have hdetCoprime : Nat.Coprime record.modulus.1
      (MvPolynomial.eval (integralAffineMap x₀ z p.m)
        C.determinant).natAbs :=
    coprime_eval_natAbs_of_coordinate_cast_eq C.determinant
      (integralAffineMap x₀ w p.m) (integralAffineMap x₀ z p.m)
      haffineCoordinate hwSurvives.2
  have hmark : markOf w = markOf z :=
    hwCell.2.2.2.trans hzCell.2.2.2.symm
  let localCertificatePolynomial : MvPolynomial (Fin 13) ℤ :=
    menu (markOf w) * selectedJacobianDeterminant localEquations selectedVar
  have hwLocalPolynomial : Nat.Coprime record.modulus.1
      (MvPolynomial.eval w localCertificatePolynomial).natAbs := by
    simpa [localCertificatePolynomial,
      integralSelectedJacobianChartCertificate] using hwLocalCoprime
  have hzLocalPolynomial : Nat.Coprime record.modulus.1
      (MvPolynomial.eval z localCertificatePolynomial).natAbs :=
    coprime_eval_natAbs_of_coordinate_cast_eq localCertificatePolynomial
      w z hcoordinate hwLocalPolynomial
  have hzLocalCoprime : Nat.Coprime record.modulus.1
      (integralSelectedJacobianChartCertificate
        localEquations selectedVar (menu (markOf z)) z).natAbs := by
    simpa [localCertificatePolynomial,
      integralSelectedJacobianChartCertificate, hmark] using hzLocalPolynomial
  exact ⟨⟨hwSurvives.1, hdetCoprime⟩, hzLocalCoprime⟩

/-- The exact point-cell cover after deleting all persistent records without
an actual persistent multiplicity-one witness.  The hypotheses are exactly
the assignment data produced by
`exists_finite_persistentSurface_multiplicityOne_records`. -/
theorem finitePointSet_subset_persistentMultiplicityOneRecordUnion
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (hX : X ⊆ rankSevenPersistentSurfaceCell
      p x₀ equations CF C denominator P k hP hlower I)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (hrecords : ∀ z ∈ X,
      ∃ record : RankSevenPersistentRecord P k markCount,
        record ∈ occupiedRankSevenPersistentRecords
          p x₀ equations CF C P k markCount ∧
        record.component = I ∧
        record.mark = markOf z ∧
        (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
          record.residue ∧
        z ∈ rankSevenPersistentRecordPointCell
          p x₀ equations CF C markOf record ∧
        survivesTwoCertificates record.modulus
          ((p.m : ℤ) * denominator)
          (MvPolynomial.eval
            (integralAffineMap x₀ z p.m) C.determinant) ∧
        Nat.Coprime record.modulus.1
          (integralSelectedJacobianChartCertificate
            localEquations selectedVar (menu (markOf z)) z).natAbs ∧
        rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower
            z record.modulus = some I ∧
        ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
          HasHilbertSamuelMultiplicityAt
            ((Nat.mem_primeFactors.mp hs).1)
            (projectiveSpecialFiberIdeal I)
            (rankSevenPersistentRecordPrimePoint record s hs) 2 1) :
    X ⊆ (occupiedRankSevenPersistentMultiplicityOneRecords
        p x₀ equations CF C denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf).biUnion fun record ↦
      rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record := by
  classical
  intro z hz
  obtain ⟨record, hrecord, hcomponent, _hmark, _hresidue,
      hzRecord, hsurvives, hlocalCoprime, hlabel, hmultiplicity⟩ :=
    hrecords z hz
  have hzPersistent : z ∈ rankSevenPersistentSurfaceCell
      p x₀ equations CF C denominator P k hP hlower record.component := by
    simpa [hcomponent] using hX hz
  have hlabel' : rankSevenStaticSurfaceLabel
      p x₀ equations CF C denominator P k hP hlower
        z record.modulus = some record.component := by
    simpa [hcomponent] using hlabel
  have hmultiplicity' : ∀ (s : ℕ)
      (hs : s ∈ record.modulus.1.primeFactors),
      HasHilbertSamuelMultiplicityAt
        ((Nat.mem_primeFactors.mp hs).1)
        (projectiveSpecialFiberIdeal record.component)
        (rankSevenPersistentRecordPrimePoint record s hs) 2 1 := by
    simpa [hcomponent] using hmultiplicity
  have hzWitness : z ∈ rankSevenPersistentMultiplicityOneWitnessCell
      p x₀ equations CF C denominator P k hP hlower X
        localEquations selectedVar menu markOf record :=
    (mem_rankSevenPersistentMultiplicityOneWitnessCell_iff
      p x₀ equations CF C denominator P k hP hlower X
        localEquations selectedVar menu markOf record z).2
      ⟨hzRecord, hz, hzPersistent, hsurvives, hlocalCoprime,
        hlabel', hmultiplicity'⟩
  have hretained : record ∈
      occupiedRankSevenPersistentMultiplicityOneRecords
        p x₀ equations CF C denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf :=
    (mem_occupiedRankSevenPersistentMultiplicityOneRecords_iff
      p x₀ equations CF C denominator P k markCount hP hlower X
        localEquations selectedVar menu markOf record).2
      ⟨hrecord, ⟨z, hzWitness⟩⟩
  exact Finset.mem_biUnion.mpr ⟨record, hretained, hzRecord⟩

/-- Cardinal form of the exact filtered persistent-record cover. -/
theorem card_finitePointSet_le_sum_persistentMultiplicityOneRecordCells
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (hX : X ⊆ rankSevenPersistentSurfaceCell
      p x₀ equations CF C denominator P k hP hlower I)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (hrecords : ∀ z ∈ X,
      ∃ record : RankSevenPersistentRecord P k markCount,
        record ∈ occupiedRankSevenPersistentRecords
          p x₀ equations CF C P k markCount ∧
        record.component = I ∧
        record.mark = markOf z ∧
        (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
          record.residue ∧
        z ∈ rankSevenPersistentRecordPointCell
          p x₀ equations CF C markOf record ∧
        survivesTwoCertificates record.modulus
          ((p.m : ℤ) * denominator)
          (MvPolynomial.eval
            (integralAffineMap x₀ z p.m) C.determinant) ∧
        Nat.Coprime record.modulus.1
          (integralSelectedJacobianChartCertificate
            localEquations selectedVar (menu (markOf z)) z).natAbs ∧
        rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower
            z record.modulus = some I ∧
        ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
          HasHilbertSamuelMultiplicityAt
            ((Nat.mem_primeFactors.mp hs).1)
            (projectiveSpecialFiberIdeal I)
            (rankSevenPersistentRecordPrimePoint record s hs) 2 1) :
    X.card ≤ ∑ record ∈
        occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF C denominator P k hP hlower X markCount
            localEquations selectedVar menu markOf,
      (rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record).card := by
  calc
    X.card ≤ ((occupiedRankSevenPersistentMultiplicityOneRecords
        p x₀ equations CF C denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf).biUnion fun record ↦
      rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record).card :=
      Finset.card_le_card
        (finitePointSet_subset_persistentMultiplicityOneRecordUnion
          p x₀ equations CF C denominator P k markCount hP hlower I X hX
            localEquations selectedVar menu markOf hrecords)
    _ ≤ ∑ record ∈
        occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF C denominator P k hP hlower X markCount
            localEquations selectedVar menu markOf,
      (rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record).card := Finset.card_biUnion_le

end

end TranslatedDepthSeven
