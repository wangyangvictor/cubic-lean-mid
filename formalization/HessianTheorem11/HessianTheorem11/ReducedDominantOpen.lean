import HessianTheorem11.AffineOpenSets

/-! Dominant inverse images of dense opens preserve affine dimension.
Everything follows from actual polynomial continuity, prime vanishing ideals,
and equality of the vanishing ideal of a set and its closure. No dimension,
generic-rank, component, fiber, or other external geometry input is used. -/
noncomputable section
namespace HessianTheorem11.ReducedDominantOpen
open MvPolynomial

/-- Polynomial inverse images of actual closed affine sets are closed. -/
theorem closed_preimage {σ τ : Type*}
    (P : τ → MvPolynomial σ GeometricField)
    {C : Set (τ → GeometricField)} (hC : AlgebraicallyClosedSet C) :
    AlgebraicallyClosedSet (polynomialMap P ⁻¹' C) := by
  apply le_antisymm
  · intro x hx
    have h := polynomialMap_image_closure_subset P (polynomialMap P ⁻¹' C)
      (Set.mem_image_of_mem (polynomialMap P) hx)
    exact geometricClosure_subset_closed (Set.image_preimage_subset _ _) hC h
  · exact subset_geometricClosure _

/-- The actual inverse image of a dense open under a dominant polynomial
map is dense in the closed irreducible source. -/
theorem dense_preimage {σ τ : Type*}
    (P : τ → MvPolynomial σ GeometricField)
    (Z : Set (σ → GeometricField)) (U O : Set (τ → GeometricField))
    (hZ : AlgebraicallyClosedSet Z) (hi : GeometricallyIrreducible Z)
    (hdom : geometricClosure (polynomialMap P '' Z) = U)
    (hO : RelativelyOpenSet U O) (hdense : geometricClosure O = U) :
    geometricClosure {z ∈ Z | polynomialMap P z ∈ O} = Z := by
  obtain ⟨C,hC,hOC⟩ := hO
  have hmap (z) (hz : z ∈ Z) : polynomialMap P z ∈ U := by
    rw [← hdom]
    exact subset_geometricClosure _ (Set.mem_image_of_mem _ hz)
  have hpre : RelativelyOpenSet Z {z ∈ Z | polynomialMap P z ∈ O} := by
    refine ⟨polynomialMap P ⁻¹' C, closed_preimage P hC, ?_⟩
    ext z
    simp only [Set.mem_setOf_eq, hOC, Set.mem_diff, Set.mem_preimage]
    exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,hmap z h.1,h.2⟩⟩
  apply hpre.dense_of_nonempty hZ hi
  by_contra hn
  have himage : polynomialMap P '' Z ⊆ C := by
    rintro _ ⟨z,hz,rfl⟩
    by_contra hzC
    apply hn
    refine ⟨z,hz,?_⟩
    rw [hOC]
    exact ⟨hmap z hz,hzC⟩
  have hUC : U ⊆ C := by
    rw [← hdom]
    exact geometricClosure_subset_closed himage hC
  have hOempty : O = ∅ := by
    rw [hOC]
    exact Set.diff_eq_empty.mpr hUC
  have hUempty : U = ∅ := by
    rw [hOempty] at hdense
    simpa only [geometricClosure, vanishingIdeal_empty, zeroLocus_top] using hdense.symm
  obtain ⟨z,hz⟩ := hi.nonempty
  have hh := hmap z hz
  rw [hUempty] at hh
  exact hh

/-- The complete former DominantOpenInput, now without any mathematical
input. This is a component reduction of AG, rather than a renamed package. -/
theorem dominantOpenInput : DominantOpenInput where
  dimension_preimage P Z U O hZ hi hdom hO hdense := by
    calc
      affineDimension {z ∈ Z | polynomialMap P z ∈ O} =
          affineDimension (geometricClosure {z ∈ Z | polynomialMap P z ∈ O}) :=
        (affineDimension_closure _).symm
      _ = affineDimension Z := by rw [dense_preimage P Z U O hZ hi hdom hO hdense]

end HessianTheorem11.ReducedDominantOpen
