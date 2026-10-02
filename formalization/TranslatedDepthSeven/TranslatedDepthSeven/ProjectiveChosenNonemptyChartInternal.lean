import TranslatedDepthSeven.HomogeneousComponentSeparatorsInternal
import TranslatedDepthSeven.PrincipalHomogeneousHypersurfaceDegreeInternal

/-! # A nonempty first chart after a coordinate permutation

Positive projective Hilbert degree forces one coordinate to survive.
Swapping it with coordinate zero preserves the literal homogeneous
quotient pieces and the full projective dimension-degree certificate.
No rationality, algebraic-closure, or geometric-integrality input is used.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000

theorem exists_coordinatePermutation_nonemptyFirstChart
    {K : Type*} [Field K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d) :
    ∃ e : Equiv.Perm (Fin (N + 1)),
      let I' := I.map (renameEquiv K e)
      I'.IsPrime ∧ I'.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) ∧
        X (0 : Fin (N + 1)) ∉ I' ∧ HasProjectiveDimensionDegree I' r d ∧
        ∀ k : ℕ, Module.finrank K (projectiveHilbertPiece K N I k) =
          Module.finrank K (projectiveHilbertPiece K N I' k) := by
  classical
  obtain ⟨i, hi⟩ := exists_coordinate_not_mem_of_projectiveHilbertDimensionDegree I hdegree.2
  let e : Equiv.Perm (Fin (N + 1)) := Equiv.swap 0 i
  let E := renameEquiv K e
  let I' := I.map E
  letI : I.IsPrime := hI
  have hI' : I'.IsPrime := by dsimp only [I', E]; infer_instance
  refine ⟨e, hI', map_renameEquiv_isHomogeneous e I hhom, ?_,
    hasProjectiveDimensionDegree_map_renameEquiv_internal e I hdegree, ?_⟩
  · intro hzero
    apply hi
    have hEi : E (X i) = X (0 : Fin (N + 1)) := by
      simp only [E, renameEquiv_apply, rename_X, e, Equiv.swap_apply_right]
    have hx : E (X i) ∈ I' := by rw [hEi]; exact hzero
    exact (Ideal.apply_mem_of_equiv_iff (f := E.toRingEquiv)).mp hx
  · intro k
    exact finrank_quotientHomogeneousComponent_map_renameEquiv K e I k

end
end TranslatedDepthSeven
