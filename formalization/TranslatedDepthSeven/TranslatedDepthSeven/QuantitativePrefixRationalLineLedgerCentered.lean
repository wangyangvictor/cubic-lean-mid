import TranslatedDepthSeven.QuantitativePrefixRationalLineLedger

/-!
# Centered-box rational line ledger

The primitive one-line estimate is translation invariant.  This file keeps
the actual box center in the quantitative-prefix rational-line ledger, so its
high-line cost depends on the radius rather than the absolute coordinate
size.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 9000000
set_option synthInstance.maxHeartbeats 600000

local instance centeredRationalLineLedgerProjectiveDecidableEq :
    DecidableEq (Projectivization ℚ (Fin 3 → ℚ)) := Classical.decEq _

/-- The rational projective line ledger in a box of radius `R` around an
arbitrary real center. -/
theorem exists_quantitativePrefixPersistent_rationalProjectiveLineLedger_centered
    {d : ℕ}
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ I)
    (u : IntVector 3) (m : ℕ) (hm : 0 < m)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (center : RealVector 3) (R : ℝ)
    (hbox : ∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
      |(integralAffineMap u z m i : ℝ) - center i| ≤ R)
    (cutoff : ℕ) :
    let J := fun o : {o // o ∈ active} ↦
      rationalAffineChartIntersectionIdeal I (terminalCut o.1)
    let Y := fun o : {o // o ∈ active} ↦
      quantitativePrefixPersistentAffineCell u m cell o.1
    ∃ (base direction : RationalLinearOccurrence J → IntVector 3)
      (parameter : RationalLinearOccurrence J → IntVector 3 → ℤ),
      (∀ o ∈ activeRationalLinearOccurrences J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑(rationalLinearOccurrencePoints J Y o) : Set (IntVector 3)) ∧
        (∀ z ∈ rationalLinearOccurrencePoints J Y o,
          z = fun i ↦ base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℚ ↦
            fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ∧
        Set.range (fun t : ℚ ↦
          fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ⊆
            affineIdealZeroLocus (J o.1)) ∧
      Fintype.card (RationalLinearOccurrence J) ≤
        ∑ o ∈ active, d * terminalDegree o ∧
      (quantitativePrefixPersistentRationalLinearPointUnion
          I active terminalCut u m cell).card ≤
        (∑ o ∈ active, d * terminalDegree o) +
        (∑ o ∈ active, d * terminalDegree o) *
          (1 + ⌈2 * R⌉₊ / (m * (cutoff + 1))) +
        (activeRationalExactLowUnion J Y
          (activeRationalLowProjectiveDirections J Y direction cutoff)
          (rationalOccurrenceProjectiveDirection J direction)).card := by
  classical
  dsimp only
  let J := fun o : {o // o ∈ active} ↦
    rationalAffineChartIntersectionIdeal I (terminalCut o.1)
  let Y := fun o : {o // o ∈ active} ↦
    quantitativePrefixPersistentAffineCell u m cell o.1
  obtain ⟨base, direction, parameter, hfull⟩ :=
    exists_activeRationalLinearOccurrence_fullIntegralLines J Y
  have hoccurrence : Fintype.card (RationalLinearOccurrence J) ≤
      ∑ o ∈ active, d * terminalDegree o :=
    card_quantitativePrefixPersistent_rationalOccurrences_le_degreeSum
      I hprime hhom hdegree active terminalDegree terminalCut hterminal
  let lowDirections :=
    activeRationalLowProjectiveDirections J Y direction cutoff
  let occurrenceDirection := rationalOccurrenceProjectiveDirection J direction
  let highBound := 1 + ⌈2 * R⌉₊ / (m * (cutoff + 1))
  have hlineData : ∀ o ∈ activeRationalLinearOccurrences J Y,
      PrimitiveDirection (direction o) ∧
      Set.InjOn (parameter o)
        (↑(rationalLinearOccurrencePoints J Y o) : Set (IntVector 3)) ∧
      ∀ z ∈ rationalLinearOccurrencePoints J Y o,
        z = fun i ↦ base o i + parameter o z * direction o i := by
    intro o ho
    exact ⟨(hfull o ho).1, (hfull o ho).2.1, (hfull o ho).2.2.1⟩
  have hHigh : ∀ o : RationalLinearOccurrence J,
      (activeRationalSelectedHighFibre
        J Y lowDirections occurrenceDirection o).card ≤ highBound := by
    intro o
    by_cases ho : o ∈ activeRationalLinearOccurrences J Y
    · by_cases hempty : activeRationalSelectedHighFibre
          J Y lowDirections occurrenceDirection o = ∅
      · simp [hempty]
      · have hBox' : ∀ z ∈ activeRationalSelectedHighFibre
            J Y lowDirections occurrenceDirection o, ∀ i,
            |(z.1 i : ℝ) - center i| ≤ R := by
          intro z _hz i
          have hzY := selectedActiveRationalLinearOccurrence_point_mem J Y z
          have hzCell : z.1 ∈ Y
              (selectedActiveRationalLinearOccurrence J Y z).1 :=
            (mem_finitePointsOnRationalAffineIdeal_iff _ _ _).mp hzY |>.1
          change z.1 ∈ (cell
            (selectedActiveRationalLinearOccurrence J Y z).1.1).image
              (fun w ↦ integralAffineMap u w m) at hzCell
          obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzCell
          rw [← hwz]
          exact hbox
            (selectedActiveRationalLinearOccurrence J Y z).1.1
            (selectedActiveRationalLinearOccurrence J Y z).1.2 w hw i
        have hResidue' : ∀ z ∈ activeRationalSelectedHighFibre
            J Y lowDirections occurrenceDirection o, ∀ i,
            z.1 i ≡ u i [ZMOD (m : ℤ)] := by
          intro z _hz i
          have hzY := selectedActiveRationalLinearOccurrence_point_mem J Y z
          have hzCell : z.1 ∈ Y
              (selectedActiveRationalLinearOccurrence J Y z).1 :=
            (mem_finitePointsOnRationalAffineIdeal_iff _ _ _).mp hzY |>.1
          change z.1 ∈ (cell
            (selectedActiveRationalLinearOccurrence J Y z).1.1).image
              (fun w ↦ integralAffineMap u w m) at hzCell
          obtain ⟨w, _hw, hwz⟩ := Finset.mem_image.mp hzCell
          rw [← hwz]
          exact (ZMod.intCast_eq_intCast_iff _ _ _).1
            (integralAffineMap_congruent u w i)
        have hraw := activeRationalSelectedHighFibre_card_le
          J Y lowDirections occurrenceDirection base direction parameter
          hlineData o ho center R m hm u hBox' hResidue'
        have hheight : cutoff < directionHeight (direction o) := by
          obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
          exact directionHeight_gt_cutoff_of_mem_activeRationalSelectedHigh
            J Y direction cutoff o z hz
        have hheight' : cutoff + 1 ≤ directionHeight (direction o) := by omega
        have hdenpos : 0 < m * (cutoff + 1) :=
          Nat.mul_pos hm (Nat.zero_lt_succ cutoff)
        exact hraw.trans (Nat.add_le_add_left
          (Nat.div_le_div_left (Nat.mul_le_mul_left m hheight') hdenpos) 1)
    · have hempty : activeRationalSelectedHighFibre
          J Y lowDirections occurrenceDirection o = ∅ := by
        ext z
        simp only [activeRationalSelectedHighFibre, Finset.mem_filter,
          Finset.notMem_empty, iff_false]
        intro hz
        exact ho (by
          rw [← hz.2.2]
          exact selectedActiveRationalLinearOccurrence_mem_active J Y z)
      simp [hempty]
  have hledger := underlyingRationalLinear_card_le_high_add_exactLow
    J Y lowDirections occurrenceDirection highBound hHigh
  have hunion :=
    quantitativePrefixPersistentRationalLinearPointUnion_eq_underlying
      I active terminalCut u m cell
  have hresult :
      (quantitativePrefixPersistentRationalLinearPointUnion
          I active terminalCut u m cell).card ≤
        (∑ o ∈ active, d * terminalDegree o) +
        (∑ o ∈ active, d * terminalDegree o) * highBound +
          (activeRationalExactLowUnion
            J Y lowDirections occurrenceDirection).card := by
    calc
      (quantitativePrefixPersistentRationalLinearPointUnion
          I active terminalCut u m cell).card =
          (underlyingRationalLinearContributionPoints J Y).card :=
        congrArg Finset.card hunion
      _ ≤ Fintype.card (RationalLinearOccurrence J) +
          Fintype.card (RationalLinearOccurrence J) * highBound +
            (activeRationalExactLowUnion
              J Y lowDirections occurrenceDirection).card := hledger
      _ ≤ (∑ o ∈ active, d * terminalDegree o) +
          (∑ o ∈ active, d * terminalDegree o) * highBound +
            (activeRationalExactLowUnion
              J Y lowDirections occurrenceDirection).card := by
        exact Nat.add_le_add
          (Nat.add_le_add hoccurrence
            (Nat.mul_le_mul_right highBound hoccurrence)) (le_refl _)
  refine ⟨base, direction, parameter, hfull, hoccurrence, ?_⟩
  simpa only [lowDirections, occurrenceDirection, highBound] using hresult

/-- At cutoff zero, primitive positivity makes the centered low catalogue
empty, so the entire rational-line union is counted with radius `R`. -/
theorem exists_quantitativePrefixPersistent_rationalLineCount_centered
    {d : ℕ}
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ I)
    (u : IntVector 3) (m : ℕ) (hm : 0 < m)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (center : RealVector 3) (R : ℝ)
    (hbox : ∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
      |(integralAffineMap u z m i : ℝ) - center i| ≤ R) :
    let J := fun o : {o // o ∈ active} ↦
      rationalAffineChartIntersectionIdeal I (terminalCut o.1)
    let Y := fun o : {o // o ∈ active} ↦
      quantitativePrefixPersistentAffineCell u m cell o.1
    ∃ (base direction : RationalLinearOccurrence J → IntVector 3)
      (parameter : RationalLinearOccurrence J → IntVector 3 → ℤ),
      (∀ o ∈ activeRationalLinearOccurrences J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑(rationalLinearOccurrencePoints J Y o) : Set (IntVector 3)) ∧
        (∀ z ∈ rationalLinearOccurrencePoints J Y o,
          z = fun i ↦ base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℚ ↦
            fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ∧
        Set.range (fun t : ℚ ↦
          fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ⊆
            affineIdealZeroLocus (J o.1)) ∧
      Fintype.card (RationalLinearOccurrence J) ≤
        ∑ o ∈ active, d * terminalDegree o ∧
      (quantitativePrefixPersistentRationalLinearPointUnion
          I active terminalCut u m cell).card ≤
        (∑ o ∈ active, d * terminalDegree o) +
        (∑ o ∈ active, d * terminalDegree o) *
          (1 + ⌈2 * R⌉₊ / m) := by
  classical
  dsimp only
  let J := fun o : {o // o ∈ active} ↦
    rationalAffineChartIntersectionIdeal I (terminalCut o.1)
  let Y := fun o : {o // o ∈ active} ↦
    quantitativePrefixPersistentAffineCell u m cell o.1
  obtain ⟨base, direction, parameter, hfull, hoccurrence, hledger⟩ :=
    exists_quantitativePrefixPersistent_rationalProjectiveLineLedger_centered
      I hprime hhom hdegree active terminalDegree terminalCut hterminal
        u m hm cell center R hbox 0
  have hlow : activeRationalLowProjectiveDirections J Y direction 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨o, ho, _hoq⟩ := Finset.mem_image.mp hq
    have hoData := Finset.mem_filter.mp ho
    obtain ⟨i, hi, hheight⟩ := (hfull o hoData.1).1.exists_natAbs_eq_directionHeight
    have hpos : 0 < directionHeight (direction o) := by
      rw [← hheight]
      exact Int.natAbs_pos.mpr hi
    omega
  have hlowUnion : activeRationalExactLowUnion J Y
      (activeRationalLowProjectiveDirections J Y direction 0)
      (rationalOccurrenceProjectiveDirection J direction) = ∅ := by
    simp [hlow, activeRationalExactLowUnion]
  refine ⟨base, direction, parameter, hfull, hoccurrence, ?_⟩
  rw [hlowUnion] at hledger
  simpa using hledger

end

end TranslatedDepthSeven
