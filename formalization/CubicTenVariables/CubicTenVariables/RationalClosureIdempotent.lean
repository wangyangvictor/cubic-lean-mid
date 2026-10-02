import CubicTenVariables.RationalConeComponents

/-! Rational density and idempotence of the rational-point closure do not
require the generating set itself to be closed. The closed-set hypothesis
is needed only for identifying its rational points with the original ones. -/

noncomputable section
namespace CubicTenVariables.RationalClosureIdempotent
open MvPolynomial HessianTheorem11 RationalConeClosure

/-- Every generator belongs to the actual rational closure. -/
theorem rational_generators_subset {n : ℕ} (C : Set (GeometricPoint n)) :
    rationalEmbedding '' (rationalPoints C ∪ {0}) ⊆ rationalConeClosure C := by
  rintro _ ⟨q, hq | hq, rfl⟩
  · exact Or.inl (subset_geometricClosure _ ⟨q, hq, rfl⟩)
  · rw [Set.mem_singleton_iff] at hq
    simpa only [hq, rationalEmbedding_zero] using zero_mem_rationalConeClosure C

/-- The actual rational points of the closure are dense for every generating
set, regardless of closedness or constructibility of that original set. -/
theorem rationalPoints_dense_any {n : ℕ} (C : Set (GeometricPoint n)) :
    geometricClosure (rationalEmbedding '' rationalPoints (rationalConeClosure C)) =
      rationalConeClosure C := by
  apply le_antisymm
  · apply geometricClosure_subset_closed _ (rationalConeClosure_closed C)
    rintro _ ⟨q, hq, rfl⟩
    exact hq
  · conv_lhs => rw [← closure_rational_generators C]
    apply geometricClosure_mono
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, rational_generators_subset C ⟨q, hq, rfl⟩, rfl⟩

/-- Taking the rational closure again adds no points. -/
theorem rationalConeClosure_idempotent {n : ℕ} (C : Set (GeometricPoint n)) :
    rationalConeClosure (rationalConeClosure C) = rationalConeClosure C := by
  change geometricClosure (rationalEmbedding '' rationalPoints (rationalConeClosure C)) ∪ {0} =
    rationalConeClosure C
  rw [rationalPoints_dense_any]
  exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (zero_mem_rationalConeClosure C))

/-- The exact old component-descent APIs apply with the closed generating
set replaced by its proved idempotent rational closure. -/
theorem component_after_idempotence {n : ℕ} (C Z : Set (GeometricPoint n))
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z) :
    IsIrreducibleComponent (rationalConeClosure (rationalConeClosure C)) Z := by
  rwa [rationalConeClosure_idempotent]

end CubicTenVariables.RationalClosureIdempotent
