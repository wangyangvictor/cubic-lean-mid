import HessianTheorem11.BibleHyperplanes
import HessianTheorem11.KernelAnnihilatorGeometry
import HessianTheorem11.NormalCrossGenericRank

/-! The linear-section interface is derived from the retained ordinary
proper-closed-subset dimension theorem and polynomial coordinate isomorphisms. -/
noncomputable section
namespace HessianTheorem11.ReducedInputs
open MvPolynomial Module

theorem linearSectionDimension (AC : AffineComponentsInput)
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput) :
    LinearSectionDimensionInput where
  subspace_hypersurface {n} L P hp := by
    classical
    let Z := {x | x ∈ L ∧ eval x P = 0}
    by_cases hn : Z.Nonempty
    · obtain ⟨d, hd⟩ := AC.finite_dimension Z hn
      have hclosed := BibleHyperplanes.homogeneous_cut_closed _
        (algebraicallyClosedSet_submodule L) P
      have hi : GeometricallyIrreducible (L : Set (GeometricPoint n)) := by
        have h := geometricallyIrreducible_univ.linearMap_image (submoduleCoordinateMap L)
        simpa only [Set.image_univ, submoduleCoordinateMap_range] using h
      have hs : Z ⊂ (L : Set (GeometricPoint n)) := by
        refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ hx => hx.1, ?_⟩
        intro he
        obtain ⟨x,hx,hp⟩ := hp
        exact hp ((show x ∈ Z from he.symm ▸ hx).2)
      have hlt := AD.proper_closed Z L hclosed (algebraicallyClosedSet_submodule L) hi hs
      rw [hd, affineDimension_submodule_from_generic_rank GR] at hlt
      have hn' : d < finrank GeometricField L := by exact_mod_cast hlt
      change affineDimension Z ≤ _
      rw [hd]
      exact_mod_cast (show d ≤ finrank GeometricField L - 1 by omega)
    · have hz : Z = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      change affineDimension Z ≤ _
      rw [hz, affineDimension_empty]
      exact bot_le
  fixed_coordinates {n m} Z y := by
    classical
    let P : (Fin n ⊕ Fin m) → GeometricPolynomial n :=
      Sum.elim (fun i => X i) (fun j => C (y j))
    let Q := pairLeftPolynomials n m
    have hP (x : GeometricPoint n) : polynomialMap P x = pairPoint x y := by
      ext i
      cases i <;> simp [P, polynomialMap, pairPoint]
    have hQ : polynomialMap Q = pairLeft := polynomialMap_pairLeftPolynomials _ _
    have hleft : Function.LeftInverse (polynomialMap Q) (polynomialMap P) := by
      intro x
      rw [hQ, hP, pairLeft_pairPoint]
    have hs : {p | pairLeft p ∈ Z ∧ pairRight p = y} = polynomialMap P '' Z := by
      ext p
      constructor
      · intro hp
        refine ⟨pairLeft p, hp.1, ?_⟩
        rw [hP, ← hp.2, pairPoint_projections]
      · rintro ⟨x,hx,rfl⟩
        rw [hP]
        exact ⟨hx, rfl⟩
    rw [hs]
    exact affineDimension_image_of_polynomial_leftInverse P Q hleft Z

end HessianTheorem11.ReducedInputs
