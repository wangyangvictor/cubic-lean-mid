import TranslatedDepthSeven.PowerSeriesSubspaceOrdersInternal

/-!
# The product-space dimension inequality for formal power series

The initial orders occurring in `U` and `V` add to orders occurring in any
space containing their products.  Two translates, using the largest order
of `U` and the smallest order of `V`, intersect only in their common
endpoint.  Their union already has at least `dim U + dim V - 1` elements.
-/

namespace TranslatedDepthSeven

noncomputable section

theorem nat_finset_card_add_le_of_add_mem
    (S T R : Finset ℕ) (hS : S.Nonempty) (hT : T.Nonempty)
    (hadd : ∀ s ∈ S, ∀ t ∈ T, s + t ∈ R) :
    S.card + T.card ≤ R.card + 1 := by
  classical
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image S id hS
  obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image T id hT
  let X := S.image (fun s ↦ s + b)
  let Y := T.image (fun t ↦ a + t)
  have hX : X.card = S.card := Finset.card_image_of_injective _ (add_left_injective b)
  have hY : Y.card = T.card := Finset.card_image_of_injective _ (add_right_injective a)
  have hcover : X ∪ Y ⊆ R := by
    intro z hz
    rcases Finset.mem_union.mp hz with hx | hy
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact hadd s hs b hb
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      exact hadd a ha t ht
  have hinter : X ∩ Y ⊆ {a + b} := by
    intro z hz
    obtain ⟨s, hs, hsz⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).1
    obtain ⟨t, ht, htz⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).2
    have hsle : s ≤ a := hmax s hs
    have htle : b ≤ t := hmin t ht
    simp only [Finset.mem_singleton]
    omega
  have hu := Finset.card_le_card hcover
  have hi : (X ∩ Y).card ≤ 1 := by
    simpa using Finset.card_le_card hinter
  have hc := Finset.card_union_add_card_inter X Y
  omega

theorem powerSeries_productSpace_finrank_inequality
    {K : Type*} [Field K]
    (U V W : Submodule K (PowerSeries K))
    [Module.Finite K U] [Module.Finite K V] [Module.Finite K W]
    (hU : 0 < Module.finrank K U) (hV : 0 < Module.finrank K V)
    (hmul : ∀ f ∈ U, ∀ g ∈ V, f * g ∈ W) :
    Module.finrank K U + Module.finrank K V ≤ Module.finrank K W + 1 := by
  classical
  let S := (powerSeriesSubspaceOrderSet_finite U).toFinset
  let T := (powerSeriesSubspaceOrderSet_finite V).toFinset
  let R := (powerSeriesSubspaceOrderSet_finite W).toFinset
  have hS : S.card = Module.finrank K U := by
    rw [← powerSeriesSubspaceOrderSet_ncard_eq_finrank U]
    exact (Set.ncard_eq_toFinset_card _ _).symm
  have hT : T.card = Module.finrank K V := by
    rw [← powerSeriesSubspaceOrderSet_ncard_eq_finrank V]
    exact (Set.ncard_eq_toFinset_card _ _).symm
  have hR : R.card = Module.finrank K W := by
    rw [← powerSeriesSubspaceOrderSet_ncard_eq_finrank W]
    exact (Set.ncard_eq_toFinset_card _ _).symm
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hTn : T.Nonempty := Finset.card_pos.mp (by omega)
  have hbound := nat_finset_card_add_le_of_add_mem S T R hSn hTn (by
    intro s hs t ht
    obtain ⟨f, hf, hforder⟩ := (powerSeriesSubspaceOrderSet_finite U).mem_toFinset.mp hs
    obtain ⟨g, hg, hgorder⟩ := (powerSeriesSubspaceOrderSet_finite V).mem_toFinset.mp ht
    apply (powerSeriesSubspaceOrderSet_finite W).mem_toFinset.mpr
    refine ⟨f * g, hmul f hf g hg, ?_⟩
    rw [PowerSeries.order_mul, hforder, hgorder, Nat.cast_add])
  omega

end

end TranslatedDepthSeven
