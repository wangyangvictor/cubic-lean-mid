import CubicTenVariables.FixedLeadingSurfaceLinesFromCurveCount
import TranslatedDepthSeven.QuantitativePrefixRationalLineLedger

/-!
# Actual residual rational degree-one components

The point union is the existing literal union over rational degree-one
minimal components. Active occurrences are deduplicated by their entire
rational affine-line sets. Their points are regrouped on these distinct
lines before applying the proved uniform line estimate. Inactive
occurrences cost at most one point each. Thus the overhead is the actual
component-occurrence ledger, with no assumption on its aggregate size.

The degree-one classification and primitive line parametrization are
proved in the imported development. The only additional literature input
is the explicit fixed ternary primitive-point estimate of Heath-Brown.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceResidualLineContribution

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceParallelLineTransport FixedLeadingSurfaceDirectionMultiplicity
open FixedLeadingSurfaceLineDirectionIncidence
open scoped BigOperators

/-- The constant is chosen before the varying surface, the residual ideal
family, its selected integral points and the box. Repeated component
occurrences do not create repeated lines in the geometric line count. -/
theorem exists_uniform_residual_linear_contribution
    (curveCount : Literature.HeathBrown2002FixedTernaryPrimitiveCount)
    {d : ℕ} (hd : 2 ≤ d) (k : MvPolynomial (Fin 3) ℤ)
    (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 → g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k →
      ∀ (ι : Type) [Fintype ι]
        (J : ι → Ideal (MvPolynomial (Fin 3) ℚ))
        (X : ι → Finset (IntVector 3)),
      (∀ i, map (Int.castRingHom ℚ) g ∈ J i) →
      ∀ B : ℕ, 1 ≤ B →
      (∀ i, ∀ z ∈ X i, ∀ j, |z j| ≤ (B : ℤ)) →
      ((underlyingRationalLinearContributionPoints J X).card : ℝ) ≤
        (∑ i : ι, ((rationalLinearAffineComponents (J i)).card : ℝ)) +
          A * (B : ℝ) ^ (1 + ε) := by
  classical
  obtain ⟨A, hA, hsum⟩ :=
    FixedLeadingSurfaceLinesFromCurveCount.exists_uniform_line_contribution
      curveCount hd k hk hirr ε hε
  refine ⟨A, hA, ?_⟩
  intro g c hc hdegree htop ι _ J X hsurface B hB hbox
  obtain ⟨base, direction, parameter, hdata⟩ :=
    exists_activeRationalLinearOccurrence_fullIntegralLines J X
  let active := activeRationalLinearOccurrences J X
  let inactive := (Finset.univ : Finset (RationalLinearOccurrence J)) \ active
  let occurrencePoints := rationalLinearOccurrencePoints J X
  let allPoints := underlyingRationalLinearContributionPoints J X
  let activePoints := activeUnderlyingRationalLinearPoints J X
  let occurrenceLine := fun o : RationalLinearOccurrence J ↦
    affineLine (rationalVector (base o)) (rationalVector (direction o))
  let lines := active.image occurrenceLine
  let representative := fun L : {L // L ∈ lines} ↦
    (Finset.mem_image.mp L.2).choose
  have hrepresentative (L : {L // L ∈ lines}) :
      representative L ∈ active ∧ occurrenceLine (representative L) = L.1 :=
    (Finset.mem_image.mp L.2).choose_spec
  let linePoints := fun L : {L // L ∈ lines} ↦
    allPoints.filter fun z ↦ rationalVector z ∈ L.1
  have hallBox : ∀ z ∈ allPoints, ∀ j, |z j| ≤ (B : ℤ) := by
    intro z hz j
    obtain ⟨o, _ho, hzo⟩ := Finset.mem_biUnion.mp hz
    exact hbox o.1 z
      ((mem_finitePointsOnRationalAffineIdeal_iff (X o.1) o.2.1 z).mp hzo).1 j
  have hlineEq (o : RationalLinearOccurrence J) (ho : o ∈ active) :
      affineIdealZeroLocus o.2.1 = occurrenceLine o := by
    simpa only [occurrenceLine, affineLine, rationalVector, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] using (hdata o ho).2.2.2.1
  have hlineSubset (o : RationalLinearOccurrence J) (ho : o ∈ active) :
      occurrenceLine o ⊆ affineIdealZeroLocus (J o.1) := by
    simpa only [occurrenceLine, affineLine, rationalVector, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] using (hdata o ho).2.2.2.2
  have hprimitive : ∀ L : {L // L ∈ lines},
      PrimitiveDirection (direction (representative L)) :=
    fun L ↦ (hdata _ (hrepresentative L).1).1
  have hdistinct : Function.Injective (fun L : {L // L ∈ lines} ↦
      affineLine (rationalVector (base (representative L)))
        (rationalVector (direction (representative L)))) := by
    intro L M h
    apply Subtype.ext
    exact (hrepresentative L).2.symm.trans (h.trans (hrepresentative M).2)
  have hcontained : ∀ L : {L // L ∈ lines},
      linePolynomial g (base (representative L)) (direction (representative L)) = 0 := by
    intro L
    apply linePolynomial_eq_zero_of_all_rational_parameters
    intro t
    have hm : (fun i ↦ (base (representative L) i : ℚ) +
        t * (direction (representative L) i : ℚ)) ∈
        occurrenceLine (representative L) := by
      exact ⟨t, rfl⟩
    exact hlineSubset _ (hrepresentative L).1 hm _ (hsurface _)
  have hpointsOnLine : ∀ L : {L // L ∈ lines}, ∀ z ∈ linePoints L,
      ∃ t : ℚ, ∀ i,
        ((z i - base (representative L) i : ℤ) : ℚ) =
          t * (direction (representative L) i : ℚ) := by
    intro L z hz
    have hm := (Finset.mem_filter.mp hz).2
    rw [← (hrepresentative L).2] at hm
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    intro i
    have hi := congrFun ht i
    change (base (representative L) i : ℚ) +
      t * (direction (representative L) i : ℚ) = (z i : ℚ) at hi
    push_cast
    linarith
  have hcount := hsum g c hc hdegree htop {L // L ∈ lines}
    linePoints (fun L ↦ base (representative L))
    (fun L ↦ direction (representative L)) hprimitive hdistinct hcontained B hB
    hpointsOnLine
    (fun L z hz ↦ hallBox z (Finset.mem_filter.mp hz).1)
  have hactiveCover : activePoints ⊆
      (Finset.univ : Finset {L // L ∈ lines}).biUnion linePoints := by
    intro z hz
    obtain ⟨o, ho, hzo⟩ := Finset.mem_biUnion.mp hz
    let L : {L // L ∈ lines} :=
      ⟨occurrenceLine o, Finset.mem_image.mpr ⟨o, ho, rfl⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨L, Finset.mem_univ _, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨o, Finset.mem_univ _, hzo⟩
    · change rationalVector z ∈ occurrenceLine o
      rw [← hlineEq o ho]
      exact ((mem_finitePointsOnRationalAffineIdeal_iff
        (X o.1) o.2.1 z).mp hzo).2
  have hactiveCard : (activePoints.card : ℝ) ≤
      (active.card : ℝ) + A * (B : ℝ) ^ (1 + ε) := by
    have hcard : activePoints.card ≤
        ∑ L : {L // L ∈ lines}, (linePoints L).card :=
      (Finset.card_le_card hactiveCover).trans Finset.card_biUnion_le
    have hlines : Fintype.card {L // L ∈ lines} ≤ active.card := by
      simpa only [Fintype.card_coe] using
        (Finset.card_image_le : lines.card ≤ active.card)
    calc
      (activePoints.card : ℝ) ≤
          ∑ L : {L // L ∈ lines}, ((linePoints L).card : ℝ) := by exact_mod_cast hcard
      _ ≤ (Fintype.card {L // L ∈ lines} : ℝ) +
          A * (B : ℝ) ^ (1 + ε) := hcount
      _ ≤ _ := add_le_add (Nat.cast_le.mpr hlines) le_rfl
  have hinactiveCard : (inactive.biUnion occurrencePoints).card ≤ inactive.card := by
    calc
      _ ≤ ∑ o ∈ inactive, (occurrencePoints o).card := Finset.card_biUnion_le
      _ ≤ ∑ _o ∈ inactive, 1 := by
        apply Finset.sum_le_sum
        intro o ho
        have hnot := (Finset.mem_sdiff.mp ho).2
        have hsmall : ¬ 2 ≤ (occurrencePoints o).card := by
          intro h
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        omega
      _ = inactive.card := by simp
  have hcover : allPoints ⊆ (inactive.biUnion occurrencePoints) ∪ activePoints := by
    intro z hz
    obtain ⟨o, _ho, hzo⟩ := Finset.mem_biUnion.mp hz
    by_cases ho : o ∈ active
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨o, ho, hzo⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨o, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ho⟩, hzo⟩)
  have hall : allPoints.card ≤ inactive.card + activePoints.card :=
    (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right hinactiveCard _))
  have hpartition : inactive.card + active.card =
      Fintype.card (RationalLinearOccurrence J) := by
    simpa only [inactive, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ active)
  have hledger : (inactive.card : ℝ) + (active.card : ℝ) =
      ∑ i : ι, ((rationalLinearAffineComponents (J i)).card : ℝ) := by
    exact_mod_cast hpartition.trans (card_rationalLinearOccurrence J)
  calc
    (allPoints.card : ℝ) ≤ (inactive.card : ℝ) + (activePoints.card : ℝ) := by
      exact_mod_cast hall
    _ ≤ (inactive.card : ℝ) + ((active.card : ℝ) + A * (B : ℝ) ^ (1 + ε)) :=
      add_le_add le_rfl hactiveCard
    _ = _ := by rw [← add_assoc, hledger]

/-- The exact degree-one ledger is bounded by the existing literal
minimal-component list, without assuming a numerical component bound. -/
theorem rational_linear_ledger_le_minimal_components
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 3) ℚ)) :
    (∑ i : ι, ((rationalLinearAffineComponents (J i)).card : ℝ)) ≤
      ∑ i : ι, ((finiteMinimalPrimes (J i)).card : ℝ) := by
  classical
  apply Finset.sum_le_sum
  intro i _hi
  exact Nat.cast_le.mpr (Finset.card_filter_le _ _)

end CubicTenVariables.FixedLeadingSurfaceResidualLineContribution
