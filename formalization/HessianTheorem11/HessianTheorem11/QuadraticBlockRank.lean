import HessianTheorem11.SingularNormalEquations
import HessianTheorem11.PolynomialRestriction

/-! The constant Hessian of an actual quadratic in a coordinate block.
Renaming into a larger ambient space does not increase its matrix rank. -/

noncomputable section
namespace HessianTheorem11.QuadraticBlockRank
open MvPolynomial Matrix Module PolynomialRestriction SingularNormalEquations

variable {K : Type*} [Field K] {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem coeff_zero_restrict (B : Matrix σ τ K) (P : MvPolynomial σ K) :
    coeff 0 (restrict B P) = coeff 0 P := by
  change constantCoeff (restrict B P) = constantCoeff P
  rw [← eval_zero, eval_restrict, Matrix.mulVec_zero]
  rw [eval_zero]

theorem coeff_mul_constant (d : σ →₀ ℕ) (P : MvPolynomial σ K) (a : K) :
    coeff d (P * C a) = coeff d P * a := by
  rw [mul_comm, coeff_C_mul, mul_comm]

theorem quadraticHessian_restrict (B : Matrix σ τ K) (P : MvPolynomial σ K) :
    quadraticHessian (restrict B P) = B.transpose * quadraticHessian P * B := by
  classical
  ext i j
  simp only [quadraticHessian, pderiv_restrict, map_sum, Derivation.leibniz,
    smul_eq_mul, pderiv_C, mul_zero, zero_add, coeff_sum, coeff_mul_constant, coeff_C_mul,
    coeff_zero_restrict, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem rank_quadraticHessian_restrict_le (B : Matrix σ τ K) (P : MvPolynomial σ K) :
    (quadraticHessian (restrict B P)).rank ≤ (quadraticHessian P).rank := by
  rw [quadraticHessian_restrict]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

variable [DecidableEq τ]

def renamingMatrix (f : σ → τ) : Matrix σ τ K := fun i j => if j = f i then 1 else 0

theorem restrict_renamingMatrix (f : σ → τ) (P : MvPolynomial σ K) :
    restrict (renamingMatrix (K := K) f) P = rename f P := by
  have hl : linearForms (renamingMatrix (K := K) f) = fun i => X (f i) := by
    funext i
    simp [linearForms, renamingMatrix, ite_mul]
  rw [restrict, hl]
  rfl

theorem rank_quadraticHessian_rename_le (f : σ → τ) (P : MvPolynomial σ K) :
    (quadraticHessian (rename f P)).rank ≤ (quadraticHessian P).rank := by
  rw [← restrict_renamingMatrix f P]
  exact rank_quadraticHessian_restrict_le _ P

theorem det_ne_zero_of_card_le_rank (A : Matrix τ τ K) (hA : Fintype.card τ ≤ A.rank) :
    A.det ≠ 0 := by
  have hn := A.mulVecLin.finrank_range_add_finrank_ker
  change A.rank + finrank K (LinearMap.ker A.mulVecLin) = finrank K (τ → K) at hn
  rw [Module.finrank_pi] at hn
  have hk : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hi : Function.Injective A.mulVec := LinearMap.ker_eq_bot.mp hk
  have hu : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hi
  exact (A.isUnit_iff_isUnit_det.mp hu).ne_zero

theorem typed_normal_det_ne_zero {n : ℕ} (T : Finset (Fin n))
    (q : MvPolynomial (↑Tᶜ : Type) K)
    (hfull : (Fintype.card (↑Tᶜ : Type)) ≤
      (quadraticHessian (rename (fun i : (↑Tᶜ : Type) => (i : Fin n)) q)).rank) :
    (quadraticHessian q).det ≠ 0 := by
  classical
  apply det_ne_zero_of_card_le_rank
  exact hfull.trans (rank_quadraticHessian_rename_le _ q)

end HessianTheorem11.QuadraticBlockRank
