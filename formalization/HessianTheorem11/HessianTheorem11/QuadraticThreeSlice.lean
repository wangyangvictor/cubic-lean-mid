import HessianTheorem11.ThreePlaneRank
import HessianTheorem11.QuadraticLowImage

/-! Three-dimensional slicing of arbitrary quadratic images. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module PolynomialRestriction
variable {n m : ℕ}

theorem quadratic_low_image_has_threePlane
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (Q : Fin m → GeometricPolynomial n) (hQ : ∀ j, (Q j).IsHomogeneous 2)
    (hne : ∃ j, Q j ≠ 0)
    (hdim : affineDimension (geometricClosure (polynomialMap Q '' Set.univ)) ≤ 3) :
    ∃ x v w : GeometricPoint n,
      geometricClosure (polynomialMap
        (fun j => restrict (threePlaneMatrix x v w) (Q j)) '' Set.univ) =
        geometricClosure (polynomialMap Q '' Set.univ) := by
  classical
  obtain ⟨G⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    Q (quadraticJacobianLinearMap Q hQ)
  obtain ⟨j, hj⟩ := hne
  obtain ⟨x, hx, hxQ⟩ := G.exists_polynomial_ne_zero (Q j) hj
  have hdimG : G.imageDimension ≤ 3 := by
    rw [G.dimension_image] at hdim
    exact_mod_cast hdim
  have hxJ : (quadraticJacobianLinearMap Q hQ x).mulVec x ≠ 0 := by
    rw [quadraticJacobian_mulVec_self]
    intro he
    have hh : 2 * eval x (Q j) = 0 := by
      simpa [polynomialMap, nsmul_eq_mul] using congrFun he j
    exact hxQ ((mul_eq_zero.mp hh).resolve_left (by norm_num))
  obtain ⟨v, w, hv⟩ := exists_threePlane_preserving_rank (quadraticJacobianLinearMap Q hQ x)
    x hxJ ((G.quadratic_rank_eq x hx).trans_le hdimG)
  let B := threePlaneMatrix x v w
  let R : Fin m → GeometricPolynomial 3 := fun j => restrict B (Q j)
  have hR : ∀ j, (R j).IsHomogeneous 2 := fun j => homogeneous_restrict B (Q j) (hQ j)
  obtain ⟨H⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    R (quadraticJacobianLinearMap R hR)
  have hHdim : G.imageDimension ≤ H.imageDimension := by
    have hh := H.quadratic_rank_le (![1,0,0] : GeometricPoint 3)
    rw [quadraticJacobian_restrict Q hQ B] at hh
    have hb : B.mulVec ![1,0,0] = x := by simp [B, threePlaneMatrix_mulVec]
    rw [hb, hv, G.quadratic_rank_eq x hx] at hh
    exact hh
  have hsub : geometricClosure (polynomialMap R '' Set.univ) ⊆
      geometricClosure (polynomialMap Q '' Set.univ) := by
    apply geometricClosure_mono
    rintro _ ⟨a, _, rfl⟩
    refine ⟨B.mulVec a, Set.mem_univ _, ?_⟩
    ext i
    exact (eval_restrict B (Q i) a).symm
  refine ⟨x, v, w, ?_⟩
  change geometricClosure (polynomialMap R '' Set.univ) = _
  by_contra hne
  have hlt := AD.proper_closed _ _ (algebraicallyClosedSet_geometricClosure _)
    (algebraicallyClosedSet_geometricClosure _)
    ((geometricallyIrreducible_closure_iff _).mpr
      (geometricallyIrreducible_univ.polynomialMap_image Q))
    (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  rw [H.dimension_image, G.dimension_image] at hlt
  have hle : (G.imageDimension : Dimension) ≤ (H.imageDimension : Dimension) := by
    exact_mod_cast hHdim
  exact (not_lt_of_ge hle) hlt

end HessianTheorem11
