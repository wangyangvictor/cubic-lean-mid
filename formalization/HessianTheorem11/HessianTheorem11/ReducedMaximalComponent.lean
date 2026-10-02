import HessianTheorem11.ReducedConeInputs

/-! Maximal-dimensional irreducible components from actual finite
decomposition and the proved finite-union dimension formula.  There is no
component, dimension, generic-open, or other external mathematical input. -/
noncomputable section
namespace HessianTheorem11.ReducedMaximalComponent
open MvPolynomial Module

/-- Reindexing the actual minimal-prime decomposition handles every finite
affine coordinate type, not only an initial segment `Fin n`. -/
theorem finite_components {σ : Type} [Fintype σ]
    (Z : Set (σ → GeometricField)) (hZ : AlgebraicallyClosedSet Z) :
    ∃ (c : ℕ) (C : Fin c → Set (σ → GeometricField)),
      Z = ⋃ i, C i ∧ ∀ i, IsIrreducibleComponent Z (C i) := by
  classical
  let L := LinearEquiv.piCongrLeft GeometricField
    (fun _ : Fin (Fintype.card σ) => GeometricField) (Fintype.equivFin σ)
  have hclosed : AlgebraicallyClosedSet (L '' Z) :=
    algebraicallyClosedSet_linearMap_image L.toLinearMap L.injective hZ
  obtain ⟨c,C,hcover,hC⟩ := ReducedInputs.finite_components (L '' Z) hclosed
  refine ⟨c,fun i => L.symm '' C i,?_,?_⟩
  · have h := congrArg (Set.image L.symm) hcover
    simpa only [Set.image_iUnion, Set.image_image, Function.comp_def,
      LinearEquiv.symm_apply_apply, Set.image_id'] using h
  · intro i
    have h := (hC i).linearEquiv_image L.symm
    simpa only [Set.image_image, Function.comp_def, LinearEquiv.symm_apply_apply,
      Set.image_id'] using h

/-- The exact former `AffineComponentsInput.maximal_dimension_component`
field, proved without any external package. Nonemptiness supplies an index;
the finite dimension supremum is attained at one actual component. -/
theorem maximal_dimension_component {σ : Type} [Fintype σ]
    (X : Set (σ → GeometricField)) (hX : AlgebraicallyClosedSet X)
    (hne : X.Nonempty) :
    ∃ Z, IsIrreducibleComponent X Z ∧ affineDimension Z = affineDimension X := by
  classical
  obtain ⟨c,C,hcover,hC⟩ := finite_components X hX
  obtain ⟨x,hx⟩ := hne
  rw [hcover] at hx
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
  have hindex : (Finset.univ : Finset (Fin c)).Nonempty := ⟨j,Finset.mem_univ j⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ hindex
    (fun i => affineDimension (C i))
  have hd : affineDimension X =
      Finset.univ.sup (fun i => affineDimension (C i)) := by
    rw [hcover]
    simpa only [Finset.mem_univ, Set.iUnion_true] using
      affineDimension_finset_union Finset.univ C
  exact ⟨C i,hC i,hi.symm.trans hd.symm⟩

end HessianTheorem11.ReducedMaximalComponent
