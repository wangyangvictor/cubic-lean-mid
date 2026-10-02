import TranslatedDepthSeven.RankSevenPersistentMultiplicityOneRecordCover
import TranslatedDepthSeven.RankSevenPersistentRecordReservoirScale

/-!
# Summing the persistent multiplicity-one record estimates

This file combines the literal filtered-record cover with the
reservoir-scale Salberger--Pila estimate for each retained record.  The
auxiliary degree bound and auxiliary form are retained record by record.
The finitely many positive Pila constants are absorbed into one positive
constant, without assuming any counting estimate.  This is only a bound for
the already fixed finite set: its final constant is chosen after that set and
must not be used as a coefficient-uniform asymptotic constant.  The uniform
replacement used on the critical path is in
`RankSevenPersistentUniformAggregate`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 4000000

/-- A finite set on one fixed persistent surface is bounded by the sum of
the literal degree-one curve contributions arising from the Salberger
auxiliary forms, plus one constant times the number of retained records and
the reservoir-scale Pila factor.

The constant in this local statement is chosen after `p`, `X`, and the record
set.  Thus this theorem is useful as a finite decomposition identity, but not
as the uniform estimate in a limit over `p.H`.  See
`exists_uniform_persistentMultiplicityOne_sum_constant` for that estimate.

The retained record set is exactly
`occupiedRankSevenPersistentMultiplicityOneRecords`; in particular empty
records have already been deleted.  The only auxiliary-intersection input
is the standard surface--hypersurface Bezout theorem.  In particular there
is no false fixed degree bound uniform over homogeneous forms of arbitrary
degree: a form of degree `a` has total component-degree mass at most
`d * a`. -/
theorem card_finitePointSet_le_persistentMultiplicityOne_linearTerms_add_reservoirScale
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (CF : ℕ) (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (hX : X ⊆ rankSevenPersistentSurfaceCell
      p x₀ equations CF Cchart denominator P k hP hlower I)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (hrecords : ∀ z ∈ X,
      ∃ record : RankSevenPersistentRecord P k markCount,
        record ∈ occupiedRankSevenPersistentRecords
          p x₀ equations CF Cchart P k markCount ∧
        record.component = I ∧
        record.mark = markOf z ∧
        (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
          record.residue ∧
        z ∈ rankSevenPersistentRecordPointCell
          p x₀ equations CF Cchart markOf record ∧
        survivesTwoCertificates record.modulus
          ((p.m : ℤ) * denominator)
          (MvPolynomial.eval
            (integralAffineMap x₀ z p.m) Cchart.determinant) ∧
        Nat.Coprime record.modulus.1
          (integralSelectedJacobianChartCertificate
            localEquations selectedVar (menu (markOf z)) z).natAbs ∧
        rankSevenStaticSurfaceLabel
          p x₀ equations CF Cchart denominator P k hP hlower
            z record.modulus = some I ∧
        ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
          HasHilbertSamuelMultiplicityAt
            ((Nat.mem_primeFactors.mp hs).1)
            (projectiveSpecialFiberIdeal I)
            (rankSevenPersistentRecordPrimePoint record s hs) 2 1)
    {d : ℕ} (hd : 2 ≤ d)
    (hIdimensionDegree : HasProjectiveDimensionDegree I 2 d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (K auxiliaryDegree : RankSevenPersistentRecord P k markCount → ℕ)
      (auxiliaryForm : RankSevenPersistentRecord P k markCount →
        MvPolynomial (Fin 14) ℚ)
      (C : ℝ),
      0 < C ∧
      (∀ record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF Cchart denominator P k hP hlower X markCount
            localEquations selectedVar menu markOf,
        auxiliaryDegree record ≤ K record ∧
        (auxiliaryForm record).IsHomogeneous (auxiliaryDegree record) ∧
        auxiliaryForm record ∉ I ∧
        ∀ z ∈ rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF Cchart) record.residue) I,
          MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ))
            (auxiliaryForm record) = 0) ∧
      ((X.card : ℕ) : ℝ) ≤
        (∑ record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
            p x₀ equations CF Cchart denominator P k hP hlower X markCount
              localEquations selectedVar menu markOf,
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I (auxiliaryForm record))
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue) I)).card : ℝ)) +
        C *
          ((occupiedRankSevenPersistentMultiplicityOneRecords
            p x₀ equations CF Cchart denominator P k hP hlower X markCount
              localEquations selectedVar menu markOf).card : ℝ) *
          (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
  classical
  let R : Finset (RankSevenPersistentRecord P k markCount) :=
    occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF Cchart denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf
  let scale : ℝ :=
    (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε)
  have hperRecord : ∀ record : RankSevenPersistentRecord P k markCount,
      ∃ (K a : ℕ) (G : MvPolynomial (Fin 14) ℚ) (C₀ : ℝ),
        0 < C₀ ∧
        (record ∈ R →
          a ≤ K ∧ G.IsHomogeneous a ∧ G ∉ I ∧
          (∀ z ∈ rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue) I,
            MvPolynomial.eval
              (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
          ((rankSevenPersistentRecordPointCell
            p x₀ equations CF Cchart markOf record).card : ℝ) ≤
            ((finitePointsOnLinearCurveComponents
              (realAffineChartIntersectionIdeal I G)
              (rankSevenPacketPointsOnSourceComponent
                (integralResiduePacket
                  (depthSevenNormalizedJacobianChartCell
                    p x₀ equations CF Cchart) record.residue) I)).card : ℝ) +
            C₀ * scale) := by
    intro record
    by_cases hrecord : record ∈ R
    · have hrecord' : record ∈
          occupiedRankSevenPersistentMultiplicityOneRecords
            p x₀ equations CF Cchart denominator P k hP hlower X markCount
              localEquations selectedVar menu markOf := by
        simpa only [R] using hrecord
      obtain ⟨hoccupied, hnonempty⟩ :=
        persistentMultiplicityOneRecord_occupied_and_nonempty
          p x₀ equations CF Cchart denominator P k markCount hP hlower X
            localEquations selectedVar menu markOf record hrecord'
      have hcomponent : record.component = I :=
        persistentMultiplicityOneRecord_component_eq_fixedSurface
          p x₀ equations CF Cchart denominator P k markCount hP hlower I X
            hX localEquations selectedVar menu markOf record hrecord'
      have hdimensionDegree : HasProjectiveDimensionDegree
          record.component 2 d := by
        simpa only [hcomponent] using hIdimensionDegree
      have hmultiplicity : ∀ (s : ℕ)
          (hs : s ∈ record.modulus.1.primeFactors),
          HasHilbertSamuelMultiplicityAt
            ((Nat.mem_primeFactors.mp hs).1)
            (projectiveSpecialFiberIdeal record.component)
            (rankSevenPersistentRecordPrimePoint record s hs) 2 1 :=
        persistentMultiplicityOneRecord_factorwise_multiplicityOne
          p x₀ equations CF Cchart denominator P k markCount hP hlower X
            localEquations selectedVar menu markOf record hrecord'
      obtain ⟨K, hterminal⟩ :=
        rankSevenPersistentRecordPointCell_card_le_rescaledPila_scale_of_multiplicityOne
          hSalberger hPila hBezout p x₀ equations hhomogeneous CF Cchart hP hlower
            markOf record hoccupied hnonempty hd hdimensionDegree
            hmultiplicity ε hε
      obtain ⟨a, G, C₀, hC₀, ha, hGhomogeneous, hGnot,
          hGzero, hcount⟩ := hterminal
      refine ⟨K, a, G, C₀, hC₀, fun _hrecordAgain ↦ ?_⟩
      refine ⟨ha, hGhomogeneous, ?_, ?_, ?_⟩
      · simpa only [hcomponent] using hGnot
      · simpa only [hcomponent] using hGzero
      · simpa only [hcomponent, scale] using hcount
    · exact ⟨0, 0, 0, 1, by norm_num, fun h ↦ (hrecord h).elim⟩
  choose K auxiliaryDegree auxiliaryForm localC hdata using hperRecord
  have hauxiliary : ∀ record ∈ R,
      auxiliaryDegree record ≤ K record ∧
      (auxiliaryForm record).IsHomogeneous (auxiliaryDegree record) ∧
      auxiliaryForm record ∉ I ∧
      ∀ z ∈ rankSevenPacketPointsOnSourceComponent
          (integralResiduePacket
            (depthSevenNormalizedJacobianChartCell
              p x₀ equations CF Cchart) record.residue) I,
        MvPolynomial.eval
          (fun i ↦ (integralAffineChartVector z i : ℚ))
          (auxiliaryForm record) = 0 := by
    intro record hrecord
    have h := (hdata record).2 hrecord
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hlocalCnonneg : 0 ≤ ∑ record ∈ R, localC record := by
    apply Finset.sum_nonneg
    intro record _hrecord
    exact (hdata record).1.le
  let C : ℝ := 1 + ∑ record ∈ R, localC record
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  have hcoefficient :
      (∑ record ∈ R, localC record) ≤ C * (R.card : ℝ) := by
    by_cases hR : R.Nonempty
    · have hcardNat : 1 ≤ R.card := Finset.one_le_card.mpr hR
      have hcard : (1 : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast hcardNat
      have hsumLeC : (∑ record ∈ R, localC record) ≤ C := by
        dsimp only [C]
        linarith
      exact hsumLeC.trans (by
        calc
          C = C * 1 := by ring
          _ ≤ C * (R.card : ℝ) :=
            mul_le_mul_of_nonneg_left hcard hC.le)
    · have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      simp [hRempty]
  have hcoverNat : X.card ≤ ∑ record ∈ R,
      (rankSevenPersistentRecordPointCell
        p x₀ equations CF Cchart markOf record).card := by
    simpa only [R] using
      card_finitePointSet_le_sum_persistentMultiplicityOneRecordCells
        p x₀ equations CF Cchart denominator P k markCount hP hlower I X
          hX localEquations selectedVar menu markOf hrecords
  have hcover : (X.card : ℝ) ≤ ∑ record ∈ R,
      ((rankSevenPersistentRecordPointCell
        p x₀ equations CF Cchart markOf record).card : ℝ) := by
    exact_mod_cast hcoverNat
  have hrecordBounds :
      (∑ record ∈ R,
        ((rankSevenPersistentRecordPointCell
          p x₀ equations CF Cchart markOf record).card : ℝ)) ≤
      ∑ record ∈ R,
        (((finitePointsOnLinearCurveComponents
          (realAffineChartIntersectionIdeal I (auxiliaryForm record))
          (rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF Cchart) record.residue) I)).card : ℝ) +
          localC record * scale) := by
    apply Finset.sum_le_sum
    intro record hrecord
    exact ((hdata record).2 hrecord).2.2.2.2
  have hscaleNonneg : 0 ≤ scale := by
    exact Real.rpow_nonneg (Real.rpow_nonneg p.T_pos.le _) _
  refine ⟨K, auxiliaryDegree, auxiliaryForm, C, hC, ?_, ?_⟩
  · simpa only [R] using hauxiliary
  · change (X.card : ℝ) ≤
      (∑ record ∈ R,
        ((finitePointsOnLinearCurveComponents
          (realAffineChartIntersectionIdeal I (auxiliaryForm record))
          (rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF Cchart) record.residue) I)).card : ℝ)) +
        C * (R.card : ℝ) * scale
    calc
      (X.card : ℝ) ≤ ∑ record ∈ R,
          ((rankSevenPersistentRecordPointCell
            p x₀ equations CF Cchart markOf record).card : ℝ) := hcover
      _ ≤ ∑ record ∈ R,
          (((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I (auxiliaryForm record))
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue) I)).card : ℝ) +
            localC record * scale) := hrecordBounds
      _ = (∑ record ∈ R,
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I (auxiliaryForm record))
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue) I)).card : ℝ)) +
          (∑ record ∈ R, localC record) * scale := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ (∑ record ∈ R,
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I (auxiliaryForm record))
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue) I)).card : ℝ)) +
          C * (R.card : ℝ) * scale := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_right hcoefficient hscaleNonneg) _

end

end TranslatedDepthSeven
