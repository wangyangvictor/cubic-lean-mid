import TranslatedDepthSeven.RankSevenSurvivingRecordCover
import TranslatedDepthSeven.RankSevenPersistentRecords

/-!
# Uniform cardinality bounds for the literal rank-seven records

This file contains only finite combinatorics.  It converts a uniform bound
for each *actual* minimal-component list into bounds for the node, edge, and
persistent record sets already used by the rank-seven partition.  In
particular, it neither assumes nor names a point-count estimate.

The geometric input used later is a degree-mass bound.  Since every component
has positive degree, that bound implies the hypotheses called `hcomponents`
below.  Keeping the present lemmas at the level of literal finite sets makes
that final use of Bezout transparent.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance recordCardinalityPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- A positive integer mass bounds the cardinality of its indexing set. -/
theorem Finset.card_le_of_sum_positive_mass
    {α : Type*} [DecidableEq α]
    (s : Finset α) (mass : α → ℕ) (D : ℕ)
    (hpositive : ∀ x ∈ s, 1 ≤ mass x)
    (hMass : ∑ x ∈ s, mass x ≤ D) :
    s.card ≤ D := by
  calc
    s.card = ∑ _x ∈ s, 1 := by simp
    _ ≤ ∑ x ∈ s, mass x := by
      apply Finset.sum_le_sum
      intro x hx
      exact hpositive x hx
    _ ≤ D := hMass

/-- The usual positive degree-mass estimate bounds the complete literal
minimal-prime list at a node. -/
theorem card_rankSevenNodeComponents_le_of_degreeMass
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q)
    (componentDegree : Ideal (MvPolynomial (Fin 14) ℚ) → ℕ)
    (D : ℕ)
    (hpositive : ∀ I ∈ rankSevenNodeComponents
      p x₀ equations CF C q rho, 1 ≤ componentDegree I)
    (hMass : ∑ I ∈ rankSevenNodeComponents
      p x₀ equations CF C q rho, componentDegree I ≤ D) :
    (rankSevenNodeComponents p x₀ equations CF C q rho).card ≤ D :=
  Finset.card_le_of_sum_positive_mass
    (rankSevenNodeComponents p x₀ equations CF C q rho)
      componentDegree D hpositive hMass

/-- The surface sublist inherits the same degree-mass cardinality bound. -/
theorem card_rankSevenSurfaceNodeComponents_le_of_degreeMass
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q)
    (componentDegree : Ideal (MvPolynomial (Fin 14) ℚ) → ℕ)
    (D : ℕ)
    (hpositive : ∀ I ∈ rankSevenNodeComponents
      p x₀ equations CF C q rho, 1 ≤ componentDegree I)
    (hMass : ∑ I ∈ rankSevenNodeComponents
      p x₀ equations CF C q rho, componentDegree I ≤ D) :
    (rankSevenSurfaceNodeComponents
      p x₀ equations CF C q rho).card ≤ D := by
  exact (Finset.card_filter_le _ _).trans
    (card_rankSevenNodeComponents_le_of_degreeMass
      p x₀ equations CF C q rho componentDegree D hpositive hMass)

/-- The non-surface sublist inherits the same degree-mass cardinality bound. -/
theorem card_rankSevenNonSurfaceNodeComponents_le_of_degreeMass
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q)
    (componentDegree : Ideal (MvPolynomial (Fin 14) ℚ) → ℕ)
    (D : ℕ)
    (hpositive : ∀ I ∈ rankSevenNodeComponents
      p x₀ equations CF C q rho, 1 ≤ componentDegree I)
    (hMass : ∑ I ∈ rankSevenNodeComponents
      p x₀ equations CF C q rho, componentDegree I ≤ D) :
    (rankSevenNonSurfaceNodeComponents
      p x₀ equations CF C q rho).card ≤ D := by
  exact (Finset.card_filter_le _ _).trans
    (card_rankSevenNodeComponents_le_of_degreeMass
      p x₀ equations CF C q rho componentDegree D hpositive hMass)

/-- A uniform component-list bound over the occupied residues bounds the
number of non-surface node records by the number of occupied residues times
that bound. -/
theorem card_occupiedRankSevenNonSurfaceNodeRecords_le_card_mul
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (q : ReservoirModulus P k)
    (D : ℕ)
    (hcomponents : ∀ rho ∈ occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenNonSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D) :
    (occupiedRankSevenNonSurfaceNodeRecords
      p x₀ equations CF C q).card ≤
      (occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C)).card * D := by
  refine (card_occupiedRankSevenNonSurfaceNodeRecords_le_sum_components
    p x₀ equations CF C q).trans ?_
  calc
    ∑ rho ∈ occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
        (rankSevenNonSurfaceNodeComponents
          p x₀ equations CF C q.1 rho).card ≤
        ∑ _rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C), D := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact hcomponents rho hrho
    _ = (occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).card * D := by simp

/-- The certificate-surviving node records form a subfamily of the coarse
node records, hence satisfy the same uniform cardinality estimate. -/
theorem card_occupiedRankSevenSurvivingNonSurfaceNodeRecords_le_card_mul
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (D : ℕ)
    (hcomponents : ∀ rho ∈ occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenNonSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D) :
    (occupiedRankSevenSurvivingNonSurfaceNodeRecords
      p x₀ equations CF C denominator P k hP hlower q).card ≤
      (occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C)).card * D := by
  calc
    (occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF C denominator P k hP hlower q).card ≤
        (occupiedRankSevenNonSurfaceNodeRecords
          p x₀ equations CF C q).card := Finset.card_filter_le _ _
    _ ≤ (occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).card * D :=
      card_occupiedRankSevenNonSurfaceNodeRecords_le_card_mul
        p x₀ equations CF C q D hcomponents

/-- Uniform bounds for both endpoint component lists give the expected
square of the component bound for edge records over one lcm residue set. -/
theorem card_occupiedRankSevenSurfaceEdgeRecords_le_card_mul_sq
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ)
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime)
    (D : ℕ)
    (hleft : ∀ rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
        (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).card ≤ D)
    (hright : ∀ rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
        (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).card ≤ D) :
    (occupiedRankSevenSurfaceEdgeRecords
      p x₀ equations CF C P k q r hP).card ≤
      (occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C)).card * (D * D) := by
  refine (card_occupiedRankSevenSurfaceEdgeRecords_le_sum_products
    p x₀ equations CF C P k q r hP).trans ?_
  calc
    ∑ rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
        (rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
          (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).card *
        (rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
          (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).card ≤
        ∑ _rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
          D * D := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact Nat.mul_le_mul (hleft rho hrho) (hright rho hrho)
    _ = (occupiedIntegralResidues (Nat.lcm q.1 r.1)
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).card * (D * D) := by simp

/-- The certificate-surviving edge records are a subfamily of the coarse
edge records. -/
theorem card_occupiedRankSevenSurvivingSurfaceEdgeRecords_le_card_mul_sq
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k) (D : ℕ)
    (hleft : ∀ rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
        (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).card ≤ D)
    (hright : ∀ rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
        (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).card ≤ D) :
    (occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF C denominator P k hP hlower q r).card ≤
      (occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C)).card * (D * D) := by
  calc
    (occupiedRankSevenSurvivingSurfaceEdgeRecords
        p x₀ equations CF C denominator P k hP hlower q r).card ≤
        (occupiedRankSevenSurfaceEdgeRecords
          p x₀ equations CF C P k q r hP).card := Finset.card_filter_le _ _
    _ ≤ (occupiedIntegralResidues (Nat.lcm q.1 r.1)
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).card * (D * D) :=
      card_occupiedRankSevenSurfaceEdgeRecords_le_card_mul_sq
        p x₀ equations CF C P k q r hP D hleft hright

/-- Uniform component and occupied-residue bounds give a completely factored
bound for the persistent record family. -/
theorem card_occupiedRankSevenPersistentRecords_le_factored
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k markCount D R : ℕ)
    (hcomponents : ∀ (q : ReservoirModulus P k)
        (rho : Fin 13 → ZMod q.1),
      rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) →
      (rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D)
    (hresidues : ∀ q : ReservoirModulus P k,
      (occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C)).card ≤ R) :
    (occupiedRankSevenPersistentRecords
      p x₀ equations CF C P k markCount).card ≤
      markCount * (Fintype.card (ReservoirModulus P k) * (R * D)) := by
  refine (card_occupiedRankSevenPersistentRecords_le_markCount_mul_sum
    p x₀ equations CF C P k markCount).trans ?_
  apply Nat.mul_le_mul_left
  calc
    ∑ q : ReservoirModulus P k,
        ∑ rho ∈ occupiedIntegralResidues q.1
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
          (rankSevenSurfaceNodeComponents
            p x₀ equations CF C q.1 rho).card ≤
        ∑ _q : ReservoirModulus P k, R * D := by
      apply Finset.sum_le_sum
      intro q _hq
      calc
        ∑ rho ∈ occupiedIntegralResidues q.1
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
            (rankSevenSurfaceNodeComponents
              p x₀ equations CF C q.1 rho).card ≤
            ∑ _rho ∈ occupiedIntegralResidues q.1
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF C), D := by
          apply Finset.sum_le_sum
          intro rho hrho
          exact hcomponents q rho hrho
        _ = (occupiedIntegralResidues q.1
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF C)).card * D := by simp
        _ ≤ R * D := Nat.mul_le_mul_right D (hresidues q)
    _ = Fintype.card (ReservoirModulus P k) * (R * D) := by simp

end

end TranslatedDepthSeven
