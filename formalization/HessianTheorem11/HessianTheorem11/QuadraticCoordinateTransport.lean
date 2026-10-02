import HessianTheorem11.GradedIndexCoordinates

/-! Quadratic Hessians, inverse-pairing polynomial relations and
independence commute with the actual block coordinate bijections. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix SingularNormalEquations
variable {K : Type*} [Field K]

theorem quadraticHessian_rename_equiv {σ τ : Type*} (e : σ ≃ τ)
    (q : MvPolynomial σ K) :
    quadraticHessian (rename e q) = (quadraticHessian q).submatrix e.symm e.symm := by
  ext i j
  change coeff 0 (pderiv j (pderiv i (rename e q))) =
    coeff 0 (pderiv (e.symm j) (pderiv (e.symm i) q))
  have hi := pderiv_rename e.injective (e.symm i) q
  have hj := pderiv_rename e.injective (e.symm j) (pderiv (e.symm i) q)
  simp only [e.apply_symm_apply] at hi hj
  rw [hi, hj]
  simpa only [Finsupp.mapDomain_zero] using
    coeff_rename_mapDomain e e.injective (pderiv (e.symm j) (pderiv (e.symm i) q)) 0

theorem quadraticRelation_reindex {σ τ α β : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (f : α → β) (R : Matrix τ τ K) (p : τ → MvPolynomial α K) :
    TangentHessianRank.quadraticRelation (R.submatrix e e) (fun i => rename f (p (e i))) =
      rename f (TangentHessianRank.quadraticRelation R p) := by
  simp only [TangentHessianRank.quadraticRelation, Matrix.submatrix_apply,
    map_sum, map_mul, rename_C]
  have h (i : τ) : (∑ j : σ, C (R i (e j)) * rename f (p i) * rename f (p (e j))) =
      ∑ j : τ, C (R i j) * rename f (p i) * rename f (p j) :=
    e.sum_comp (fun j => C (R i j) * rename f (p i) * rename f (p j))
  simp_rw [h]
  exact e.sum_comp (fun i => ∑ j : τ, C (R i j) * rename f (p i) * rename f (p j))

namespace GradedIndexCoordinates
variable {n r s : ℕ} {T : Finset (Fin n)} {c : Fin n}

theorem normalPolynomial_hessian (D : GradedIndexCoordinates T c r s)
    (q : MvPolynomial (↑Tᶜ : Type) K) :
    quadraticHessian (D.normalPolynomial q) = (quadraticHessian q).submatrix D.normal D.normal :=
  quadraticHessian_rename_equiv D.normal.symm q

theorem normalPolynomial_det_ne_zero (D : GradedIndexCoordinates T c r s)
    (q : MvPolynomial (↑Tᶜ : Type) K) [DecidableEq (↑Tᶜ : Type)]
    (hq : (quadraticHessian q).det ≠ 0) :
    (quadraticHessian (D.normalPolynomial q)).det ≠ 0 := by
  rw [D.normalPolynomial_hessian, Matrix.det_submatrix_equiv_self]
  exact hq

theorem normalTuple_independent (D : GradedIndexCoordinates T c r s)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) K)
    (hp : LinearIndependent K p) : LinearIndependent K (D.normalTuple p) := by
  let E := renameEquiv K D.tangent.symm
  exact (hp.comp D.normal D.normal.injective).map_injOn E.toLinearMap E.injective.injOn

theorem normalTuple_relation (D : GradedIndexCoordinates T c r s)
    (q : MvPolynomial (↑Tᶜ : Type) K)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) K)
    [DecidableEq (↑Tᶜ : Type)]
    (hrel : TangentHessianRank.quadraticRelation (quadraticHessian q)⁻¹ p = 0) :
    TangentHessianRank.quadraticRelation (quadraticHessian (D.normalPolynomial q))⁻¹
      (D.normalTuple p) = 0 := by
  rw [D.normalPolynomial_hessian, Matrix.inv_submatrix_equiv]
  change TangentHessianRank.quadraticRelation ((quadraticHessian q)⁻¹.submatrix D.normal D.normal)
    (fun i => rename D.tangent.symm (p (D.normal i))) = 0
  rw [quadraticRelation_reindex, hrel, map_zero]

end GradedIndexCoordinates
end HessianTheorem11
