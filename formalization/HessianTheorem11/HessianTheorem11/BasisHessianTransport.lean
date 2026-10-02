import HessianTheorem11.PolynomialCoordinateEquiv
import HessianTheorem11.PolynomialRestriction
import HessianTheorem11.HessianDeterminant
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Algebra.Group.Irreducible.Lemmas

/-! Actual polynomial, rank, and determinant transport along a basis with an
arbitrary finite index type. -/

noncomputable section
namespace HessianTheorem11.BasisHessianTransport
open MvPolynomial Module
open PolynomialRestriction

variable {ι : Type*} [Fintype ι] {n : ℕ}

def basisMatrix (b : Basis ι GeometricField (Fin n → GeometricField)) :
    Matrix (Fin n) ι GeometricField := fun i j => b j i

omit [Fintype ι] in
theorem basisMatrix_eq_toMatrix (b : Basis ι GeometricField (Fin n → GeometricField)) :
    basisMatrix b = (Pi.basisFun GeometricField (Fin n)).toMatrix b := by
  ext i j
  simp [basisMatrix, Basis.toMatrix_apply]

theorem basisMatrix_mulVec_eq (b : Basis ι GeometricField (Fin n → GeometricField))
    (y : ι → GeometricField) : (basisMatrix b).mulVec y = b.equivFun.symm y := by
  classical
  rw [Basis.equivFun_symm_apply]
  ext i
  simp [basisMatrix, Matrix.mulVec, dotProduct, mul_comm]

theorem restrict_eq_pullback (b : Basis ι GeometricField (Fin n → GeometricField))
    (F : MvPolynomial (Fin n) GeometricField) :
    restrict (basisMatrix b) F =
      (PolynomialCoordinateEquiv.ofLinearEquiv b.equivFun.symm).pullbackAlgEquiv F := by
  apply MvPolynomial.funext
  intro y
  rw [eval_restrict, basisMatrix_mulVec_eq,
    PolynomialCoordinateEquiv.pullbackAlgEquiv_apply, ← eval_polynomialMap]
  change eval (b.equivFun.symm y) F =
    eval ((PolynomialCoordinateEquiv.ofLinearEquiv b.equivFun.symm).forwardMap y) F
  rw [PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap]

theorem restrict_irreducible (b : Basis ι GeometricField (Fin n → GeometricField))
    (F : MvPolynomial (Fin n) GeometricField) (hF : Irreducible F) :
    Irreducible (restrict (basisMatrix b) F) := by
  rw [restrict_eq_pullback]
  exact hF.map (PolynomialCoordinateEquiv.ofLinearEquiv b.equivFun.symm).pullbackAlgEquiv.toMulEquiv

theorem hessian_restrict (B : Matrix (Fin n) ι GeometricField)
    (F : MvPolynomial (Fin n) GeometricField) (y : ι → GeometricField) :
    (fun i j => eval y (pderiv j (pderiv i (restrict B F)))) =
      B.transpose * hessian F (B.mulVec y) * B := by
  classical
  ext i j
  simp only [hessian, hessianPolynomial, pderiv_restrict, map_sum,
    Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add,
    map_mul, eval_C, eval_restrict, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem rank_congruence_basis (b : Basis ι GeometricField (Fin n → GeometricField))
    (H : Matrix (Fin n) (Fin n) GeometricField) :
    ((basisMatrix b).transpose * H * basisMatrix b).rank = H.rank := by
  classical
  let B := basisMatrix b
  let T := b.toMatrix (Pi.basisFun GeometricField (Fin n))
  have hBT : B * T = 1 := by
    rw [show B = (Pi.basisFun GeometricField (Fin n)).toMatrix b from basisMatrix_eq_toMatrix b]
    exact (Pi.basisFun GeometricField (Fin n)).toMatrix_mul_toMatrix_flip b
  have hrecover : T.transpose * (B.transpose * H * B) * T = H := by
    calc
      _ = (B * T).transpose * H * (B * T) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = H := by rw [hBT, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · calc
      H.rank = (T.transpose * (B.transpose * H * B) * T).rank :=
        congrArg Matrix.rank hrecover.symm
      _ ≤ (B.transpose * H * B).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem hessian_rank_restrict (b : Basis ι GeometricField (Fin n → GeometricField))
    (F : MvPolynomial (Fin n) GeometricField) (y : ι → GeometricField) :
    (show Matrix ι ι GeometricField from
      fun i j => eval y (pderiv j (pderiv i (restrict (basisMatrix b) F)))).rank =
      (hessian F ((basisMatrix b).mulVec y)).rank := by
  rw [hessian_restrict, rank_congruence_basis]

theorem exists_det_congruence_basis [DecidableEq ι]
    (b : Basis ι GeometricField (Fin n → GeometricField)) :
    ∃ c : GeometricField, c ≠ 0 ∧
      ∀ H : Matrix (Fin n) (Fin n) GeometricField,
        ((basisMatrix b).transpose * H * basisMatrix b).det = c * H.det := by
  classical
  let s := Pi.basisFun GeometricField (Fin n)
  have hc : Fintype.card ι = Fintype.card (Fin n) :=
    (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_eq_card_basis s)
  let e : ι ≃ Fin n := Fintype.equivOfCardEq hc
  let b' := b.reindex e
  let E := s.toMatrix b'
  have hE : E.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse
    (s.toMatrix_mul_toMatrix_flip b')
  have hB : E = (basisMatrix b).submatrix id e.symm := by
    ext i j
    simp [E, s, b', Basis.toMatrix_apply, basisMatrix]
  refine ⟨E.det * E.det, mul_ne_zero hE hE, ?_⟩
  intro H
  have hGram : ((basisMatrix b).transpose * H * basisMatrix b).submatrix e.symm e.symm =
      E.transpose * H * E := by
    rw [hB]
    rfl
  calc
    _ = (((basisMatrix b).transpose * H * basisMatrix b).submatrix e.symm e.symm).det :=
      (Matrix.det_submatrix_equiv_self e.symm _).symm
    _ = (E.transpose * H * E).det := congrArg Matrix.det hGram
    _ = _ := by rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring

/-- The actual polynomial Hessian determinant changes by a nonzero constant,
equal to the square of the determinant of the basis matrix after reindexing. -/
theorem hessian_determinant_restrict [DecidableEq ι]
    (b : Basis ι GeometricField (Fin n → GeometricField))
    (F : MvPolynomial (Fin n) GeometricField) :
    ∃ c : GeometricField, c ≠ 0 ∧
      (show Matrix ι ι (MvPolynomial ι GeometricField) from
        fun i j => pderiv j (pderiv i (restrict (basisMatrix b) F))).det =
        C c * restrict (basisMatrix b) (hessianDeterminantPolynomial F) := by
  obtain ⟨c, hc, hd⟩ := exists_det_congruence_basis b
  refine ⟨c, hc, ?_⟩
  apply MvPolynomial.funext
  intro y
  rw [eval_mul, eval_C, eval_restrict, eval_hessianDeterminantPolynomial,
    RingHom.map_det]
  change (show Matrix ι ι GeometricField from
    fun i j => eval y (pderiv j (pderiv i (restrict (basisMatrix b) F)))).det = _
  rw [hessian_restrict, hd]

end HessianTheorem11.BasisHessianTransport
