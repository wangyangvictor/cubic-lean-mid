import HessianTheorem11.AffineSubspaces
import HessianTheorem11.Concentration

/-! The Jacobian of an arbitrary homogeneous quadratic tuple is an actual
linear matrix pencil. The existing general generic-rank input identifies its
maximum rank with the dimension of the image closure. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
variable {n m : ℕ}

def quadraticJacobianLinearMap (Q : Fin m → GeometricPolynomial n)
    (hQ : ∀ j, (Q j).IsHomogeneous 2) :
    GeometricPoint n →ₗ[GeometricField] Matrix (Fin m) (Fin n) GeometricField where
  toFun x := fun i j => eval x (pderiv j (Q i))
  map_add' x y := by
    ext i j
    exact eval_add_homogeneous_one (hQ i).pderiv x y
  map_smul' a x := by
    ext i j
    exact eval_smul_homogeneous_one (hQ i).pderiv a x

theorem quadraticJacobian_mulVecLin (Q : Fin m → GeometricPolynomial n)
    (hQ : ∀ j, (Q j).IsHomogeneous 2) (x : GeometricPoint n) :
    (quadraticJacobianLinearMap Q hQ x).mulVecLin = polynomialMapDifferential Q x := by
  ext v i
  simp [quadraticJacobianLinearMap, Matrix.mulVec, dotProduct,
    polynomialMapDifferential, polynomialDifferential_apply]

theorem quadraticJacobian_mulVec_self (Q : Fin m → GeometricPolynomial n)
    (hQ : ∀ j, (Q j).IsHomogeneous 2) (x : GeometricPoint n) :
    (quadraticJacobianLinearMap Q hQ x).mulVec x = 2 • polynomialMap Q x := by
  ext i
  have h := congrArg (eval x) (hQ i).sum_X_mul_pderiv
  simpa [quadraticJacobianLinearMap, Matrix.mulVec, dotProduct, polynomialMap,
    nsmul_eq_mul, mul_comm] using h

theorem GenericRankOpen.quadratic_rank_eq
    {Q : Fin m → GeometricPolynomial n} {hQ : ∀ j, (Q j).IsHomogeneous 2}
    (G : GenericRankOpen Set.univ Q (quadraticJacobianLinearMap Q hQ))
    (x : GeometricPoint n) (hx : x ∈ G.openSet) :
    (quadraticJacobianLinearMap Q hQ x).rank = G.imageDimension := by
  have h := G.differential_rank x hx
  rw [affineTangentSpace_univ_geometric, LinearMap.range_domRestrict, Submodule.map_top,
    ← quadraticJacobian_mulVecLin Q hQ x] at h
  exact h

theorem GenericRankOpen.quadratic_rank_le
    {Q : Fin m → GeometricPolynomial n} {hQ : ∀ j, (Q j).IsHomogeneous 2}
    (G : GenericRankOpen Set.univ Q (quadraticJacobianLinearMap Q hQ))
    (y : GeometricPoint n) :
    (quadraticJacobianLinearMap Q hQ y).rank ≤ G.imageDimension := by
  obtain ⟨x, hx⟩ := G.nonempty
  rw [← G.quadratic_rank_eq x hx]
  exact G.maximal_rank x hx y (Set.mem_univ y)

/-- A nonzero polynomial is nonzero somewhere in the actual dense generic
open, proved directly from equality of vanishing ideals. -/
theorem GenericRankOpen.exists_polynomial_ne_zero
    {Q : Fin m → GeometricPolynomial n} {a b : ℕ}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField}
    (G : GenericRankOpen Set.univ Q M) (p : GeometricPolynomial n) (hp : p ≠ 0) :
    ∃ x ∈ G.openSet, eval x p ≠ 0 := by
  by_contra h
  push_neg at h
  have hv : p ∈ vanishingIdeal GeometricField G.openSet := h
  have he := vanishingIdeal_geometricClosure G.openSet
  rw [G.dense, vanishingIdeal_univ_eq_bot_geometric] at he
  have hz : p ∈ (⊥ : Ideal (GeometricPolynomial n)) := by rwa [he]
  exact hp (Ideal.mem_bot.mp hz)

end HessianTheorem11
