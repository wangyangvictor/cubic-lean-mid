import HessianTheorem11.FiveTernaryQuadrics
import HessianTheorem11.QuadricGram
import HessianTheorem11.QuadraticThreeSlice
import HessianTheorem11.PolynomialImageRelations

/-! Five independent quadratic coordinates subject to a nonsingular quadratic
relation have image dimension four. The specific obstruction to dimension
three is proved by ternary coefficient algebra; only ordinary generic rank
and strict dimension drop for affine varieties are inputs. -/
set_option maxRecDepth 2000
noncomputable section
namespace HessianTheorem11
open Matrix MvPolynomial Module PolynomialRestriction TangentHessianRank
variable {n : ℕ}

theorem five_quadrics_imageDimension_ge_four
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (p : Fin 5 → GeometricPolynomial n) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hlin : LinearIndependent GeometricField p)
    (A : Matrix (Fin 5) (Fin 5) GeometricField) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : quadraticRelation A p = 0)
    (G : GenericRankOpen Set.univ p (quadraticJacobianLinearMap p hp)) :
    4 ≤ G.imageDimension := by
  by_contra hh
  have hdim : affineDimension (geometricClosure (polynomialMap p '' Set.univ)) ≤ 3 := by
    rw [G.dimension_image]
    have h : G.imageDimension ≤ 3 := by omega
    exact_mod_cast h
  obtain ⟨x,v,w,hslice⟩ := quadratic_low_image_has_threePlane GR AD p hp
    ⟨0, hlin.ne_zero 0⟩ hdim
  let B := threePlaneMatrix x v w
  let q : Fin 5 → GeometricPolynomial 3 := fun i => restrict B (p i)
  have hq : ∀ i, (q i).IsHomogeneous 2 :=
    fun i => homogeneous_restrict B (p i) (hp i)
  have hqind : LinearIndependent GeometricField q :=
    linearIndependent_of_same_imageClosure p q hslice.symm hlin
  have hqrel : quadraticRelation A q = 0 := by
    have h := congrArg (restrict B) hrel
    simpa [quadraticRelation, q, restrict] using h
  exact FiveTernaryQuadrics.five_independent_no_relation q hq hqind A hA hdet hqrel

theorem five_quadrics_generic_rank_eq_four
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (p : Fin 5 → GeometricPolynomial n) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hlin : LinearIndependent GeometricField p)
    (A : Matrix (Fin 5) (Fin 5) GeometricField) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : quadraticRelation A p = 0)
    (G : GenericRankOpen Set.univ p (quadraticJacobianLinearMap p hp)) :
    G.imageDimension = 4 := by
  have hlo := five_quadrics_imageDimension_ge_four GR AD p hp hlin A hA hdet hrel G
  obtain ⟨x,hx,hpx⟩ := G.exists_polynomial_ne_zero (p 0) (hlin.ne_zero 0)
  have hpvec : (fun i => eval x (p i)) ≠ 0 := by
    intro h
    exact hpx (congrFun h 0)
  have hhi := rank_polynomialJacobian_lt A hA hdet p hrel x hpvec
  have hJ : polynomialJacobian p x = quadraticJacobianLinearMap p hp x := rfl
  rw [hJ, G.quadratic_rank_eq x hx] at hhi
  simp only [Fintype.card_fin] at hhi
  omega

theorem five_quadrics_exists_rank_four
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (p : Fin 5 → GeometricPolynomial n) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hlin : LinearIndependent GeometricField p)
    (A : Matrix (Fin 5) (Fin 5) GeometricField) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : quadraticRelation A p = 0) :
    ∃ x : GeometricPoint n, (fun i => eval x (p i)) ≠ 0 ∧
      (polynomialJacobian p x).rank = 4 := by
  obtain ⟨G⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    p (quadraticJacobianLinearMap p hp)
  obtain ⟨x,hx,hpx⟩ := G.exists_polynomial_ne_zero (p 0) (hlin.ne_zero 0)
  refine ⟨x, ?_, ?_⟩
  · intro h
    exact hpx (congrFun h 0)
  · change (quadraticJacobianLinearMap p hp x).rank = 4
    rw [G.quadratic_rank_eq x hx]
    exact five_quadrics_generic_rank_eq_four GR AD p hp hlin A hA hdet hrel G

theorem five_quadrics_dominant_on_quadric
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (p : Fin 5 → GeometricPolynomial n) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hlin : LinearIndependent GeometricField p)
    (A : Matrix (Fin 5) (Fin 5) GeometricField) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : quadraticRelation A p = 0) :
    geometricClosure (polynomialMap p '' Set.univ) =
      {d | dotProduct d (A.mulVec d) = 0} := by
  have hsub : geometricClosure (polynomialMap p '' Set.univ) ⊆
      polynomialHypersurface (gramPolynomial A) := by
    apply geometricClosure_subset_closed _ (polynomialHypersurface_closed _)
    rintro _ ⟨x,hx,rfl⟩
    have he := congrArg (eval x) hrel
    change eval (polynomialMap p x) (gramPolynomial A) = 0
    rw [eval_gramPolynomial]
    simpa [quadraticRelation, polynomialMap, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc, mul_left_comm] using he
  have hirr := gramPolynomial_irreducible A hA hdet (by decide : 2 < 5)
  obtain ⟨G⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    p (quadraticJacobianLinearMap p hp)
  have hdim : ((5 - 1 : ℕ) : Dimension) ≤
      affineDimension (geometricClosure (polynomialMap p '' Set.univ)) := by
    rw [G.dimension_image]
    have h := five_quadrics_imageDimension_ge_four GR AD p hp hlin A hA hdet hrel G
    exact_mod_cast h
  have he := equal_hypersurface_of_dimension_ge AD (gramPolynomial A) hirr
    _ (algebraicallyClosedSet_geometricClosure _) hsub hdim
  rw [he]
  ext d
  change eval d (gramPolynomial A) = 0 ↔ dotProduct d (A.mulVec d) = 0
  rw [eval_gramPolynomial]

end HessianTheorem11
