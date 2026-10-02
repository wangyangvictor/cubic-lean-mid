import CubicTenVariables.ConductorFixedFrequency

/-! The exact set represented by the simultaneous level-zero condition.
Intersecting the promoted prime partition with the unpromoted square
partition removes the incoming promoted open. This is a set identity and
does not require any geometric or literature assumption. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.MicrolocalGenericFrequencyBridge
open MvPolynomial HessianTheorem11 RationalConeClosure
open ProjectiveMicrolocalData ConductorFixedFrequency

variable {t : ℕ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}

/-- Only the empty level-zero promotion is needed; the incoming level-one
promotion may be an arbitrary subset. -/
theorem zero_parts_inter_eq (U : ℕ → Set (Fin 10 → ℚ)) (hU : U 0 = ∅) :
    MicrolocalPromotedPartition.part f U 0 ∩ MicrolocalSquarePartition.part f 0 =
      MicrolocalSquarePartition.part f 0 := by
  rw [MicrolocalPromotedPartition.part_eq_source U 0 (by decide),
    MicrolocalSquarePartition.part_eq_layer 0 (by decide)]
  simp only [Fin.val_zero,zero_add,hU,Set.diff_empty]
  ext x
  simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_union,Set.mem_singleton_iff]
  tauto

/-- The actual rational intersection is precisely the nonzero rational
frequencies outside the actual geometric depth-one locus. -/
theorem rational_parts_inter_eq {F : MvPolynomial (Fin 10) ℤ}
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)) :
    MicrolocalPromotedPartition.part f
        (MicrolocalPartitionCounts.promotionFamily (fun i => (tables i).open)) 0 ∩
      MicrolocalSquarePartition.part f 0 =
      {v : Fin 10 → ℚ | v ≠ 0 ∧ rationalEmbedding v ∉ ProjectiveMicrolocalDepth.depth f 1} := by
  rw [zero_parts_inter_eq _ (MicrolocalPartitionCounts.promotionFamily_zero _),
    MicrolocalSquarePartition.part_eq_layer 0 (by decide)]
  ext v
  simp only [MicrolocalPromotedPartition.filtration,Fin.val_zero,zero_add,
    if_true,show ¬ (1 : ℕ)=0 by decide,if_false,Set.mem_diff,Set.mem_univ,
    true_and,Set.mem_singleton_iff,Set.mem_setOf_eq,rationalPoints]
  tauto

/-- The integer-frequency condition used by the conductor estimates has
no additional hidden promoted-open restriction. -/
theorem goodFrequency_iff {F : MvPolynomial (Fin 10) ℤ}
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (v : Fin 10 → ℤ) :
    GoodFrequency F f tables v ↔ v ≠ 0 ∧
      (fun i => (v i : GeometricField)) ∉ ProjectiveMicrolocalDepth.depth f 1 := by
  have hset := Set.ext_iff.mp (rational_parts_inter_eq tables) (fun i => (v i : ℚ))
  change GoodFrequency F f tables v ↔
    (fun i => (v i : ℚ)) ≠ 0 ∧
      rationalEmbedding (fun i => (v i : ℚ)) ∉ ProjectiveMicrolocalDepth.depth f 1 at hset
  have hcast : (fun i => (v i : ℚ)) = 0 ↔ v = 0 := by
    constructor
    · intro hv
      funext i
      have hi : (v i : ℚ)=0 := congrFun hv i
      exact_mod_cast hi
    · intro hv
      subst v
      rfl
  have he : rationalEmbedding (fun i => (v i : ℚ)) =
      fun i => (v i : GeometricField) := by
    funext i
    simp only [rationalEmbedding,map_intCast]
  rw [he] at hset
  exact hset.trans (and_congr (not_congr hcast) Iff.rfl)

/-- Equivalently the actual geometric fiber has dimension strictly below
one. Empty fibers are included by the existing `Dimension` convention. -/
theorem goodFrequency_iff_fiber_dimension {F : MvPolynomial (Fin 10) ℤ}
    (tables : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (v : Fin 10 → ℤ) :
    GoodFrequency F f tables v ↔ v ≠ 0 ∧
      affineDimension (BihomogeneousIncidenceFamily.fiber f GeometricField
        (fun i => (v i : GeometricField))) < (1 : Dimension) := by
  rw [goodFrequency_iff tables v,ProjectiveMicrolocalDepth.depth_eq_fiber_dimension]
  simp only [Set.mem_setOf_eq,not_le,Nat.cast_one]

end CubicTenVariables.MicrolocalGenericFrequencyBridge
