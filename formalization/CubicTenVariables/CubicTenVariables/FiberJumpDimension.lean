import CubicTenVariables.DominatingComponentSelection
import CubicTenVariables.RationalConeComponents

/-!
The closure of the locus where a polynomial map has larger-than-generic
fibers has a strict dimension bound. The parameter locus need not be
closed, and the map need not be proper. Every component of its closure
is controlled using its original dense generators.
-/

noncomputable section
namespace CubicTenVariables.FiberJumpDimension
open MvPolynomial HessianTheorem11

/-- Parameters with an actual whole-source fiber of dimension at least `k`. -/
def largeFiberParameters {n m : ℕ} (P : Fin m → GeometricPolynomial n)
    (Y : Set (GeometricPoint n)) (k : ℕ) : Set (GeometricPoint m) :=
  {v | (k : Dimension) ≤ affineDimension {x | x ∈ Y ∧ polynomialMap P x = v}}

/-- The entire large-fiber locus is contained in a closed set whose
preimage omits a point of the source. No closedness of that locus is used. -/
theorem exists_closed_exceptional {n m d s k : ℕ}
    (P : Fin m → GeometricPolynomial n) (Y : Set (GeometricPoint n))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hd : affineDimension Y = (d : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension))
    (hk : 0 < k) (hjump : d - s < k) :
    ∃ D : Set (GeometricPoint m), AlgebraicallyClosedSet D ∧
      geometricClosure (largeFiberParameters P Y k) ⊆ D ∧
      ∃ x ∈ Y, polynomialMap P x ∉ D := by
  obtain ⟨O, hO, hnO, _, hOI, hdim⟩ :=
    GenericWholeFiberDimension.exists_dense_open_whole_fiber_dimension_eq P Y hY hiY
      d s hd hs
  obtain ⟨D, hD, heq⟩ := hO
  have hBD : largeFiberParameters P Y k ⊆ D := by
    intro v hv
    by_contra hvD
    have hne : {x | x ∈ Y ∧ polynomialMap P x = v}.Nonempty := by
      by_contra hn
      have hf := Set.not_nonempty_iff_eq_empty.mp hn
      have hh := hv
      change (k : Dimension) ≤ affineDimension {x | x ∈ Y ∧ polynomialMap P x = v} at hh
      rw [hf, affineDimension_empty] at hh
      exact WithBot.not_coe_le_bot _ hh
    obtain ⟨x, hx, hxv⟩ := hne
    have hvZ : v ∈ geometricClosure (polynomialMap P '' Y) :=
      subset_geometricClosure _ ⟨x, hx, hxv⟩
    have hvO : v ∈ O := heq.symm ▸ ⟨hvZ, hvD⟩
    have hlow := hv
    change (k : Dimension) ≤ affineDimension {x | x ∈ Y ∧ polynomialMap P x = v} at hlow
    rw [hdim v hvO] at hlow
    have hnat : k ≤ d - s := by exact_mod_cast hlow
    omega
  obtain ⟨v, hv⟩ := hnO
  obtain ⟨x, hx, hxv⟩ := hOI hv
  refine ⟨D, hD, geometricClosure_subset_closed hBD hD, x, hx, ?_⟩
  rw [hxv]
  exact (heq ▸ hv).2

/-- Every component of the closure of the actual jump locus satisfies
the strict source-dimension bound. -/
theorem component_dimension_add_lt {n m d s k z : ℕ}
    (P : Fin m → GeometricPolynomial n) (Y : Set (GeometricPoint n))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hd : affineDimension Y = (d : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension))
    (hk : 0 < k) (hjump : d - s < k)
    (Z : Set (GeometricPoint m))
    (hZ : IsIrreducibleComponent (geometricClosure (largeFiberParameters P Y k)) Z)
    (hz : affineDimension Z = (z : Dimension)) : z + k < d := by
  obtain ⟨D, hD, hBD, x₀, hx₀, hx₀D⟩ :=
    exists_closed_exceptional P Y hY hiY hd hs hk hjump
  let T := Y ∩ polynomialMap P ⁻¹' Z
  have hT : AlgebraicallyClosedSet T := by
    apply Set.Subset.antisymm _ (subset_geometricClosure _)
    intro x hx
    exact ⟨geometricClosure_subset_closed Set.inter_subset_left hY hx,
      geometricClosure_subset_closed Set.inter_subset_right
        (ReducedDominantOpen.closed_preimage P hZ.closed) hx⟩
  have hA : geometricClosure (largeFiberParameters P Y k ∩ Z) = Z :=
    RationalConeComponents.closure_inter_component_of_dense _ _ Z
      (algebraicallyClosedSet_geometricClosure _) rfl hZ
  have hlarge : ∀ v ∈ largeFiberParameters P Y k ∩ Z,
      (k : Dimension) ≤ affineDimension {x | x ∈ T ∧ polynomialMap P x = v} := by
    intro v hv
    have he : {x | x ∈ T ∧ polynomialMap P x = v} =
        {x | x ∈ Y ∧ polynomialMap P x = v} := by
      ext x
      change (x ∈ Y ∧ polynomialMap P x ∈ Z) ∧ polynomialMap P x = v ↔
        x ∈ Y ∧ polynomialMap P x = v
      aesop
    rw [he]
    exact hv.1
  obtain ⟨K, hK, _, hdim⟩ :=
    DominatingComponentSelection.exists_large_dominating_component P T hT
      Z (largeFiberParameters P Y k ∩ Z) hZ.closed hZ.irreducible
      (by rintro _ ⟨x, hx, rfl⟩; exact hx.2) hz hA hk hlarge
  have hproper : K ⊂ Y := by
    refine ⟨hK.subset.trans Set.inter_subset_left, ?_⟩
    intro hback
    have hxZ := (hK.subset (hback hx₀)).2
    exact hx₀D (hBD (hZ.subset hxZ))
  have hdrop := ReducedStrictDimension.proper_closed K Y hK.closed hY hiY hproper
  rw [hd] at hdrop
  exact_mod_cast hdim.trans_lt hdrop

/-- The closure bound is valid even when the jump locus is not closed.
Natural subtraction includes the empty or very-high-threshold cases. -/
theorem closure_dimension_le {n m d s k : ℕ}
    (P : Fin m → GeometricPolynomial n) (Y : Set (GeometricPoint n))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hd : affineDimension Y = (d : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension))
    (hk : 0 < k) (hjump : d - s < k) :
    affineDimension (geometricClosure (largeFiberParameters P Y k)) ≤
      ((d - (k + 1) : ℕ) : Dimension) := by
  obtain ⟨c, C, hcover, hC⟩ := ReducedMaximalComponent.finite_components
    (geometricClosure (largeFiberParameters P Y k)) (algebraicallyClosedSet_geometricClosure _)
  rw [hcover]
  apply affineDimension_fintype_union_le
  intro i
  obtain ⟨z, hz⟩ := ReducedComponentDimension.finite_dimension (C i) (hC i).irreducible.nonempty
  have hlt := component_dimension_add_lt P Y hY hiY hd hs hk hjump (C i) (hC i) hz
  rw [hz]
  exact_mod_cast (show z ≤ d - (k + 1) by omega)

end CubicTenVariables.FiberJumpDimension
