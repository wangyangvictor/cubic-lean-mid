import HessianTheorem11.TwoPlaneRank
import HessianTheorem11.QuadraticSlice
import HessianTheorem11.AffineHypersurfaceDimension

/-! A quadratic map whose image has dimension at most two is dominated by
an actual two-vector slice. Its linear span consequently has dimension at
most three. The only geometric inputs are generic differential rank and the
strict dimension drop for proper closed subsets of irreducible varieties. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module PolynomialRestriction
variable {n m : ℕ}

theorem quadraticJacobian_restrict (Q : Fin m → GeometricPolynomial n)
    (hQ : ∀ j, (Q j).IsHomogeneous 2) {k : ℕ}
    (B : Matrix (Fin n) (Fin k) GeometricField) (x : GeometricPoint k) :
    quadraticJacobianLinearMap (fun j => restrict B (Q j))
        (fun j => homogeneous_restrict B (Q j) (hQ j)) x =
      quadraticJacobianLinearMap Q hQ (B.mulVec x) * B := by
  ext i j
  simp [quadraticJacobianLinearMap, pderiv_restrict, Matrix.mul_apply]

theorem quadratic_low_image_has_twoPlane
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (Q : Fin m → GeometricPolynomial n) (hQ : ∀ j, (Q j).IsHomogeneous 2)
    (hne : ∃ j, Q j ≠ 0)
    (hdim : affineDimension (geometricClosure (polynomialMap Q '' Set.univ)) ≤ 2) :
    ∃ x v : GeometricPoint n,
      geometricClosure (polynomialMap
        (fun j => restrict (twoPlaneMatrix x v) (Q j)) '' Set.univ) =
        geometricClosure (polynomialMap Q '' Set.univ) := by
  classical
  obtain ⟨G⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    Q (quadraticJacobianLinearMap Q hQ)
  obtain ⟨j, hj⟩ := hne
  obtain ⟨x, hx, hxQ⟩ := G.exists_polynomial_ne_zero (Q j) hj
  have hdimG : G.imageDimension ≤ 2 := by
    rw [G.dimension_image] at hdim
    exact_mod_cast hdim
  have hxJ : (quadraticJacobianLinearMap Q hQ x).mulVec x ≠ 0 := by
    rw [quadraticJacobian_mulVec_self]
    intro he
    have hh := congrFun he j
    have hh : 2 * eval x (Q j) = 0 := by
      simpa [polynomialMap, nsmul_eq_mul] using hh
    exact hxQ ((mul_eq_zero.mp hh).resolve_left (by norm_num))
  obtain ⟨v, hv⟩ := exists_twoPlane_preserving_rank (quadraticJacobianLinearMap Q hQ x)
    x hxJ ((G.quadratic_rank_eq x hx).trans_le hdimG)
  let B := twoPlaneMatrix x v
  let R : Fin m → GeometricPolynomial 2 := fun j => restrict B (Q j)
  have hR : ∀ j, (R j).IsHomogeneous 2 := fun j => homogeneous_restrict B (Q j) (hQ j)
  obtain ⟨H⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    R (quadraticJacobianLinearMap R hR)
  have hHdim : G.imageDimension ≤ H.imageDimension := by
    have hh := H.quadratic_rank_le (![1,0] : GeometricPoint 2)
    rw [quadraticJacobian_restrict Q hQ B] at hh
    have hb : B.mulVec ![1,0] = x := by simp [B, twoPlaneMatrix_mulVec]
    rw [hb, hv, G.quadratic_rank_eq x hx] at hh
    exact hh
  have hsub : geometricClosure (polynomialMap R '' Set.univ) ⊆
      geometricClosure (polynomialMap Q '' Set.univ) := by
    apply geometricClosure_mono
    rintro _ ⟨a, _, rfl⟩
    refine ⟨B.mulVec a, Set.mem_univ _, ?_⟩
    ext i
    exact (eval_restrict B (Q i) a).symm
  refine ⟨x, v, ?_⟩
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

theorem quadratic_low_image_span_le_three
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (Q : Fin m → GeometricPolynomial n) (hQ : ∀ j, (Q j).IsHomogeneous 2)
    (hdim : affineDimension (geometricClosure (polynomialMap Q '' Set.univ)) ≤ 2) :
    finrank GeometricField (Submodule.span GeometricField
      (polynomialMap Q '' Set.univ)) ≤ 3 := by
  classical
  by_cases hne : ∃ j, Q j ≠ 0
  · obtain ⟨x, v, heq⟩ := quadratic_low_image_has_twoPlane GR AD Q hQ hne hdim
    let S := quadraticTuplePlaneEnvelope Q x v
    have hsmall : polynomialMap
        (fun j => restrict (twoPlaneMatrix x v) (Q j)) '' Set.univ ⊆ S := by
      rintro _ ⟨a, _, rfl⟩
      have he : polynomialMap (fun j => restrict (twoPlaneMatrix x v) (Q j)) a =
          fun j => eval (a 0 • x + a 1 • v) (Q j) := by
        ext j
        simp [polynomialMap, eval_restrict, twoPlaneMatrix_mulVec]
      rw [he]
      exact quadraticTuple_two_vector_mem_envelope Q hQ x v (a 0) (a 1)
    have hcl := geometricClosure_subset_closed hsmall (algebraicallyClosedSet_submodule S)
    rw [heq] at hcl
    exact (Submodule.finrank_mono (Submodule.span_le.mpr
      ((subset_geometricClosure _).trans hcl))).trans
        (quadraticTuplePlaneEnvelope_finrank_le_three Q x v)
  · push_neg at hne
    have hs : Submodule.span GeometricField (polynomialMap Q '' Set.univ) = ⊥ := by
      apply le_antisymm _ bot_le
      apply Submodule.span_le.mpr
      rintro _ ⟨x, _, rfl⟩
      change polynomialMap Q x = 0
      ext j
      simp [polynomialMap, hne j]
    rw [hs]
    simp

end HessianTheorem11
