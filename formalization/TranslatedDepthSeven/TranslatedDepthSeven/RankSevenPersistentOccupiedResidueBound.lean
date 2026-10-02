import TranslatedDepthSeven.RankSevenOccupiedResidueBound
import TranslatedDepthSeven.RankSevenPersistentRecordCardinality

/-!
# Occupurrence mass for the retained persistent records

This is the persistent analogue of the node and edge occurrence bounds.  It
keeps the sum over the literal reservoir moduli.  For a nonempty modulus
fibre, an actual retained witness supplies certificate survival, so the
fixed-cone CRT estimate applies to that modulus.  Empty fibres contribute
zero.  No surface point-count estimate enters.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance persistentOccupiedPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The retained persistent multiplicity-one record set has the sum of the
literal `q^6` occurrence masses. -/
theorem card_occupiedRankSevenPersistentMultiplicityOneRecords_cast_le_sum
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount D : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (hcomponents : ∀ (q : ReservoirModulus P k)
        (rho : Fin 13 → ZMod q.1),
      rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) →
      (rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) ε ≤ p.H) :
    ((occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF C model.denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf).card : ℝ) ≤
      ∑ q : ReservoirModulus P k,
        p.H ^ ε * (q.1 : ℝ) ^ 6 * (D * markCount) := by
  classical
  let R : Finset (RankSevenPersistentRecord P k markCount) :=
    occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF C model.denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf
  have hRbroad : R ⊆ occupiedRankSevenPersistentRecords
      p x₀ equations CF C P k markCount := by
    intro record hrecord
    exact (mem_occupiedRankSevenPersistentMultiplicityOneRecords_iff
      p x₀ equations CF C model.denominator P k markCount hP hlower X
        localEquations selectedVar menu markOf record).mp hrecord |>.1
  have hcoverNat : R.card ≤ ∑ q : ReservoirModulus P k,
      (R.filter fun record ↦ record.modulus = q).card :=
    card_persistentRecordSubfamily_le_sum_modulusFibres
      p x₀ equations CF C P k markCount R
  have hcoverReal : (R.card : ℝ) ≤ ∑ q : ReservoirModulus P k,
      ((R.filter fun record ↦ record.modulus = q).card : ℝ) := by
    exact_mod_cast hcoverNat
  refine hcoverReal.trans ?_
  apply Finset.sum_le_sum
  intro q _hq
  let Rq := R.filter fun record ↦ record.modulus = q
  by_cases hRq : Rq.Nonempty
  · obtain ⟨record, hrecordRq⟩ := hRq
    obtain ⟨hrecordR, hrecordModulus⟩ := Finset.mem_filter.mp hrecordRq
    have hrecord : record ∈
        occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF C model.denominator P k hP hlower X markCount
            localEquations selectedVar menu markOf := by
      simpa only [R] using hrecordR
    obtain ⟨z, hz⟩ := persistentMultiplicityOneRecord_has_witness
      p x₀ equations CF C model.denominator P k markCount hP hlower X
        localEquations selectedVar menu markOf record hrecord
    have hsurvives :=
      (mem_rankSevenPersistentMultiplicityOneWitnessCell_iff
        p x₀ equations CF C model.denominator P k hP hlower X
          localEquations selectedVar menu markOf record z).mp hz |>.2.2.2.1
    have hsurvivesQ : survivesTwoCertificates q
        ((p.m : ℤ) * model.denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m)
          C.determinant) := by
      simpa only [hrecordModulus] using hsurvives
    have hresidue :=
      card_depthSevenNormalizedChart_occupiedResidues_of_survives_cast_le
        hM₀ hε p x₀ equations CF C model hP q
          (MvPolynomial.eval (integralAffineMap x₀ z p.m)
            C.determinant) hsurvivesQ hk hH
    have hRqNat : Rq.card ≤
        (occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).card * (D * markCount) := by
      calc
        Rq.card ≤
            (occupiedRankSevenPersistentRecordsAtModulus
              p x₀ equations CF C P k markCount q).card := by
          exact card_persistentRecordSubfamilyAtModulus_le
            p x₀ equations CF C P k markCount R hRbroad q
        _ ≤ (occupiedIntegralResidues q.1
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF C)).card * (D * markCount) :=
          card_occupiedRankSevenPersistentRecordsAtModulus_le
            p x₀ equations CF C P k markCount D q
              (hcomponents q)
    have hRqReal : (Rq.card : ℝ) ≤
        ((occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).card : ℝ) * (D * markCount) := by
      exact_mod_cast hRqNat
    exact hRqReal.trans
      (mul_le_mul_of_nonneg_right hresidue
        (mul_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg markCount)))
  · have hRqEmpty : Rq = ∅ := Finset.not_nonempty_iff_eq_empty.mp hRq
    have hcardZero : Rq.card = 0 := by simp [hRqEmpty]
    rw [show (R.filter fun record ↦ record.modulus = q).card = 0 by
      simpa only [Rq] using hcardZero]
    simpa only [Nat.cast_zero] using
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg p.H_pos.le ε)
          (pow_nonneg (Nat.cast_nonneg q.1) 6))
        (mul_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg markCount)))

end

end TranslatedDepthSeven
