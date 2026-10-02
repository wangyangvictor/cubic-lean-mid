import HessianTheorem11.NormalPencil
import HessianTheorem11.LocalCubicNormalForm

/-! Concrete cofactor relations of the ternary quadratic Veronese map.
The determinant and adjugate identities below rule out rank five without
using a classification of quadratic maps as an external input. -/
noncomputable section
namespace HessianTheorem11.TernaryQuadricRelations
open Matrix MvPolynomial
open scoped BigOperators
variable {K : Type*} [CommRing K]

/-- The Hessian of `Tr(S adj Y)` in coordinates `(Y11,Y22,Y33,Y12,Y13,Y23)`. -/
def relationMatrix (s0 s1 s2 s3 s4 s5 : K) : Matrix (Fin 6) (Fin 6) K :=
  !![0,s2,s1,0,0,-2*s5;
     s2,0,s0,0,-2*s4,0;
     s1,s0,0,-2*s3,0,0;
     0,0,-2*s3,-2*s2,2*s5,2*s4;
     0,-2*s4,0,2*s5,-2*s1,2*s3;
     -2*s5,0,0,2*s4,2*s3,-2*s0]

def parameterDet (s0 s1 s2 s3 s4 s5 : K) : K :=
  s0*s1*s2 + 2*s3*s4*s5 - s0*s5^2 - s1*s4^2 - s2*s3^2

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem relationMatrix_det (s0 s1 s2 s3 s4 s5 : K) :
    (relationMatrix s0 s1 s2 s3 s4 s5).det =
      -16 * parameterDet s0 s1 s2 s3 s4 s5 ^ 2 := by
  simp [relationMatrix, parameterDet, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  ring
def adjugateFactor (s0 s1 s2 s3 s4 s5 : K) : Matrix (Fin 6) (Fin 6) K :=
  !![(8 * s0^2), (-8 * s0 * s1 + 16 * s3^2), (-8 * s0 * s2 + 16 * s4^2), (8 * s0 * s3), (8 * s0 * s4), (-8 * s0 * s5 + 16 * s3 * s4);
    (-8 * s0 * s1 + 16 * s3^2), (8 * s1^2), (-8 * s1 * s2 + 16 * s5^2), (8 * s1 * s3), (-8 * s1 * s4 + 16 * s3 * s5), (8 * s1 * s5);
    (-8 * s0 * s2 + 16 * s4^2), (-8 * s1 * s2 + 16 * s5^2), (8 * s2^2), (-8 * s2 * s3 + 16 * s4 * s5), (8 * s2 * s4), (8 * s2 * s5);
    (8 * s0 * s3), (8 * s1 * s3), (-8 * s2 * s3 + 16 * s4 * s5), (8 * s0 * s1), (8 * s0 * s5), (8 * s1 * s4);
    (8 * s0 * s4), (-8 * s1 * s4 + 16 * s3 * s5), (8 * s2 * s4), (8 * s0 * s5), (8 * s0 * s2), (8 * s2 * s3);
    (-8 * s0 * s5 + 16 * s3 * s4), (8 * s1 * s5), (8 * s2 * s5), (8 * s1 * s4), (8 * s2 * s3), (8 * s1 * s2)]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem relationMatrix_adjugate (s0 s1 s2 s3 s4 s5 : K) :
    (relationMatrix s0 s1 s2 s3 s4 s5).adjugate =
      parameterDet s0 s1 s2 s3 s4 s5 • adjugateFactor s0 s1 s2 s3 s4 s5 := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j <;>
    simp [relationMatrix, parameterDet, adjugateFactor, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove] <;> ring

section Field
variable {L : Type*} [Field L]

/-- Corank one is detected by the actual adjugate, using ordinary row and
column elimination and products of diagonal entries. -/
theorem adjugate_ne_zero_of_corank_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι L) (hr : M.rank + 1 = Fintype.card ι) :
    M.adjugate ≠ 0 := by
  classical
  obtain ⟨P,Q,D,hP,hQ,hdiag⟩ :=
    NormalPencil.exists_det_one_diagonal_residue (RingHom.id L)
      Function.surjective_id M
  change P * M * Q = Matrix.diagonal D at hdiag
  have hPunit : IsUnit P.det := by rw [hP]; exact isUnit_one
  have hQunit : IsUnit Q.det := by rw [hQ]; exact isUnit_one
  have hrank : (Matrix.diagonal D).rank = M.rank := by
    rw [← hdiag, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQunit,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPunit]
  have hcard : (Finset.univ.filter (fun i => D i = 0)).card = 1 := by
    have hsum := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.univ) (fun i : ι => D i = 0)
    rw [Matrix.rank_diagonal, Fintype.card_subtype] at hrank
    simp only [Finset.card_univ] at hsum
    have hsum' : (Finset.univ.filter (fun i => D i = 0)).card + M.rank =
        Fintype.card ι := by
      rw [← hrank]
      exact hsum
    omega
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hcard
  have hnonzero : ∏ j ∈ Finset.univ.erase i, D j ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj hz
    have hj' : j ∈ Finset.univ.filter (fun k => D k = 0) := by simp [hz]
    rw [hi, Finset.mem_singleton] at hj'
    exact (Finset.mem_erase.mp hj).1 hj'
  intro hz
  have hdiagzero : (Matrix.diagonal D).adjugate = 0 := by
    rw [← hdiag, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
      hz, zero_mul, mul_zero]
  have he := congrArg (fun A : Matrix ι ι L => A i i) hdiagzero
  apply hnonzero
  simpa only [Matrix.adjugate_diagonal, Matrix.diagonal_apply_eq,
    Matrix.zero_apply] using he

theorem relationMatrix_rank_ne_five [CharZero L] (s0 s1 s2 s3 s4 s5 : L) :
    (relationMatrix s0 s1 s2 s3 s4 s5).rank ≠ 5 := by
  intro hr
  have hdet : (relationMatrix s0 s1 s2 s3 s4 s5).det = 0 := by
    by_contra hn
    have he := Matrix.rank_of_isUnit (relationMatrix s0 s1 s2 s3 s4 s5)
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn))
    simp [hr] at he
  rw [relationMatrix_det] at hdet
  have hs : parameterDet s0 s1 s2 s3 s4 s5 = 0 := by
    have hn : (-16 : L) ≠ 0 := by norm_num
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hdet).resolve_left hn)
  apply adjugate_ne_zero_of_corank_one (relationMatrix s0 s1 s2 s3 s4 s5)
    (by simp [hr])
  rw [relationMatrix_adjugate, hs, zero_smul]

end Field
end HessianTheorem11.TernaryQuadricRelations
