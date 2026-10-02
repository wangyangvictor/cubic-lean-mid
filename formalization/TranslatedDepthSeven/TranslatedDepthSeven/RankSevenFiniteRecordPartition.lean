import TranslatedDepthSeven.RankSevenEdgeRecordCover
import TranslatedDepthSeven.RankSevenNodeRecordCover

/-!
# The literal finite-record partition on a rank-seven chart

This file substitutes the finite node and edge record covers into the exact
vertex--edge--persistent partition.  The node term is indexed by an occupied
residue and an actual non-surface minimal prime.  The edge term is indexed by
an occupied lcm-residue, two distinct surface components, and an actual
minimal prime over their ideal supremum.  No component-count, degree, or
point-count estimate is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The exact rank-seven chart partition after replacing both the node term
and the unequal-surface edge term by their literal finite algebraic record
covers.  The only term not altered here is the persistent-surface term. -/
theorem card_rankSevenChart_le_nodeRecords_edgeFrontiers_persistent
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
        ∑ record ∈ occupiedRankSevenNonSurfaceNodeRecords
            p x₀ equations CF C q,
          (rankSevenNonSurfaceNodeRecordPointCell
            p x₀ equations CF C record).card) +
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurfaceEdgeRecords
            p x₀ equations CF C P k q r hP,
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
  have hpartition :=
    card_rankSevenChart_le_surfaceVertex_edge_persistent
      p x₀ equations CF C denominator P k hP hlower H A hsurvival
      hfixedNe hfixedSize hdetNe hdetSize
  change (depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C).card ≤
    (∑ q : ReservoirModulus P k,
      (rankSevenNonSurfaceNodeCell
        p x₀ equations CF C denominator P k hP hlower q).card) +
    (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
      (rankSevenSurfaceEdgeCell
        p x₀ equations CF C denominator P k hP hlower q r).card) +
    (∑ o ∈ occurringRankSevenStaticSurfaceLabels
        p x₀ equations CF C denominator P k hP hlower,
      ((depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
        fun z ↦ o ≠ none ∧ ∀ q : ReservoirModulus P k,
          survivesTwoCertificates q ((p.m : ℤ) * denominator)
            (MvPolynomial.eval (integralAffineMap x₀ z p.m)
              C.determinant) →
          rankSevenStaticSurfaceLabel
            p x₀ equations CF C denominator P k hP hlower z q = o).card) at hpartition
  have hnodes :
      (∑ q : ReservoirModulus P k,
        (rankSevenNonSurfaceNodeCell
          p x₀ equations CF C denominator P k hP hlower q).card) ≤
      ∑ q : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenNonSurfaceNodeRecords
            p x₀ equations CF C q,
          (rankSevenNonSurfaceNodeRecordPointCell
            p x₀ equations CF C record).card := by
    apply Finset.sum_le_sum
    intro q _hq
    exact card_rankSevenNonSurfaceNodeCell_le_sum_recordCells
      p x₀ equations CF hhomogeneous C denominator P k hP hlower q
  have hedges :
      (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        (rankSevenSurfaceEdgeCell
          p x₀ equations CF C denominator P k hP hlower q r).card) ≤
      ∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurfaceEdgeRecords
            p x₀ equations CF C P k q r hP,
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
          ∑ record ∈ occupiedRankSevenSurfaceEdgeRecords
              p x₀ equations CF C P k q r hP,
            (rankSevenSurfaceEdgeRecordPointCell
              p x₀ equations CF C P k record).card :=
        card_rankSevenSurfaceEdgeCell_le_sum_recordCells
          p x₀ equations CF C denominator P k hP hlower q r
      _ ≤ ∑ record ∈ occupiedRankSevenSurfaceEdgeRecords
              p x₀ equations CF C P k q r hP,
            ∑ L ∈ finiteMinimalPrimes
                (record.leftComponent ⊔ record.rightComponent),
              (rankSevenSurfaceEdgeFrontierPointCell
                p x₀ equations CF C P k record L).card := by
        apply Finset.sum_le_sum
        intro record _hrecord
        exact card_rankSevenSurfaceEdgeRecordPointCell_le_sum_frontierCells
          p x₀ equations CF C P k record
  exact hpartition.trans
    (Nat.add_le_add (Nat.add_le_add hnodes hedges) (le_refl _))

end

end TranslatedDepthSeven
