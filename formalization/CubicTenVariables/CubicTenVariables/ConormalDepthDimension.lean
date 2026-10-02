import CubicTenVariables.FiberJumpDimension

/-! One-component dimension algebra for the conormal depth argument.
All loci are defined from the actual polynomial map and its whole-source
fibers. The source is any closed irreducible set of dimension `n`; no
conormal, singular-support, cubic, or literature hypothesis is introduced.
When the target ambient dimension is also `n`, the resulting inequalities
are precisely codimension bounds. Equality identifies the actual image
closure, which is the conormal base in the intended application.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConormalDepthDimension

open MvPolynomial HessianTheorem11

/-- A nonnegative-dimensional fiber is nonempty, so every depth parameter
lies in the actual image. Its closure lies in the actual image closure. -/
theorem closure_largeFiberParameters_subset_imageClosure {a b : ℕ}
    (P : Fin b → GeometricPolynomial a) (Y : Set (GeometricPoint a)) (j : ℕ) :
    geometricClosure (FiberJumpDimension.largeFiberParameters P Y j) ⊆
      geometricClosure (polynomialMap P '' Y) := by
  apply geometricClosure_mono
  intro v hv
  have hne : {x | x ∈ Y ∧ polynomialMap P x = v}.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hdim := hv
    change (j : Dimension) ≤ affineDimension {x | x ∈ Y ∧ polynomialMap P x = v} at hdim
    rw [he, affineDimension_empty] at hdim
    exact WithBot.not_coe_le_bot _ hdim
  obtain ⟨x, hx, hxv⟩ := hne
  exact ⟨x, hx, hxv⟩

/-- The closure of the depth-at-least-j locus has dimension at most n-j.
The natural subtraction also handles thresholds larger than the source
dimension; closedness of the depth locus itself is not asserted. -/
theorem closure_dimension_le {a b n s j : ℕ}
    (P : Fin b → GeometricPolynomial a) (Y : Set (GeometricPoint a))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hn : affineDimension Y = (n : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension))
    (hj : 0 < j) :
    affineDimension (geometricClosure (FiberJumpDimension.largeFiberParameters P Y j)) ≤
      ((n - j : ℕ) : Dimension) := by
  have hsn := GenericWholeFiberDimension.image_dimension_le_source P Y hY hiY n s hn hs
  by_cases hsmall : j ≤ n - s
  · have hdim := affineDimension_mono
      (closure_largeFiberParameters_subset_imageClosure P Y j)
    rw [hs] at hdim
    exact hdim.trans (by exact_mod_cast (show s ≤ n - j by omega))
  · exact (FiberJumpDimension.closure_dimension_le P Y hY hiY hn hs hj
      (by omega)).trans (by exact_mod_cast (show n - (j + 1) ≤ n - j by omega))

/-- An irreducible component attaining dimension n-j must be the whole
image closure, and the generic fiber dimension n-s must equal j. This is
the equality case needed to identify codimension-j conormal bases. -/
theorem component_eq_imageClosure_of_dimension_eq {a b n s j : ℕ}
    (P : Fin b → GeometricPolynomial a) (Y : Set (GeometricPoint a))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hn : affineDimension Y = (n : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension))
    (hj : 0 < j) (Z : Set (GeometricPoint b))
    (hZ : IsIrreducibleComponent
      (geometricClosure (FiberJumpDimension.largeFiberParameters P Y j)) Z)
    (hZdim : affineDimension Z = ((n - j : ℕ) : Dimension)) :
    n - s = j ∧ Z = geometricClosure (polynomialMap P '' Y) := by
  have hsn := GenericWholeFiberDimension.image_dimension_le_source P Y hY hiY n s hn hs
  have hsub := hZ.subset.trans (closure_largeFiberParameters_subset_imageClosure P Y j)
  have hzle : n - j ≤ s := by
    have hdim := affineDimension_mono hsub
    rw [hZdim, hs] at hdim
    exact_mod_cast hdim
  by_cases hsmall : j ≤ n - s
  · have heq : n - s = j := by omega
    refine ⟨heq, ?_⟩
    by_contra hne
    have hproper : Z ⊂ geometricClosure (polynomialMap P '' Y) :=
      ⟨hsub, fun hback => hne (Set.Subset.antisymm hsub hback)⟩
    have hiD : GeometricallyIrreducible (geometricClosure (polynomialMap P '' Y)) :=
      (geometricallyIrreducible_closure_iff _).mpr (hiY.polynomialMap_image P)
    have hdrop := ReducedStrictDimension.proper_closed Z _ hZ.closed
      (algebraicallyClosedSet_geometricClosure _) hiD hproper
    rw [hZdim, hs] at hdrop
    have hlt : n - j < s := by exact_mod_cast hdrop
    omega
  · have hlt := FiberJumpDimension.component_dimension_add_lt P Y hY hiY
      hn hs hj (by omega) Z hZ hZdim
    omega

/-- The equality case for any closed subset of the depth closure, in the
positive codimension range used by the finite-incidence application. No
maximal-component assumption or irreducibility of the subset is needed. -/
theorem closed_subset_eq_imageClosure_of_dimension_eq {a b n s j : ℕ}
    (P : Fin b → GeometricPolynomial a) (Y : Set (GeometricPoint a))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hn : affineDimension Y = (n : Dimension))
    (hs : affineDimension (geometricClosure (polynomialMap P '' Y)) = (s : Dimension))
    (hj : 0 < j) (hjn : j < n) (Z : Set (GeometricPoint b))
    (hZ : AlgebraicallyClosedSet Z)
    (hsub : Z ⊆ geometricClosure (FiberJumpDimension.largeFiberParameters P Y j))
    (hZdim : affineDimension Z = ((n-j : ℕ) : Dimension)) :
    n-s = j ∧ Z = geometricClosure (polynomialMap P '' Y) := by
  have hsn := GenericWholeFiberDimension.image_dimension_le_source P Y hY hiY n s hn hs
  have hsubD := hsub.trans (closure_largeFiberParameters_subset_imageClosure P Y j)
  have hzle : n-j ≤ s := by
    have hdim := affineDimension_mono hsubD
    rw [hZdim, hs] at hdim
    exact_mod_cast hdim
  by_cases hsmall : j ≤ n-s
  · have heq : n-s = j := by omega
    refine ⟨heq, ?_⟩
    by_contra hne
    have hiD : GeometricallyIrreducible (geometricClosure (polynomialMap P '' Y)) :=
      (geometricallyIrreducible_closure_iff _).mpr (hiY.polynomialMap_image P)
    have hproper : Z ⊂ geometricClosure (polynomialMap P '' Y) :=
      Set.ssubset_iff_subset_ne.mpr ⟨hsubD, hne⟩
    have hdrop := ReducedStrictDimension.proper_closed Z _ hZ
      (algebraicallyClosedSet_geometricClosure _) hiD hproper
    rw [hZdim, hs] at hdrop
    have hlt : n-j < s := by exact_mod_cast hdrop
    omega
  · have hle := (affineDimension_mono hsub).trans
      (FiberJumpDimension.closure_dimension_le P Y hY hiY hn hs hj (by omega))
    rw [hZdim] at hle
    have hnat : n-j ≤ n-(j+1) := by exact_mod_cast hle
    omega

end CubicTenVariables.ConormalDepthDimension
