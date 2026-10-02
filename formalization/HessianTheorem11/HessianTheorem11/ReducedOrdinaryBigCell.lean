import HessianTheorem11.ReducedBigCellMatrices
import HessianTheorem11.ReducedWeightUpper

/-! The ordinary weighted big cell is constructed by independent column
corrections using the smaller-weight principal blocks. Its open condition
is the product of their actual determinant polynomials. -/
noncomputable section
namespace HessianTheorem11.ReducedOrdinaryBigCell
open Matrix MvPolynomial NonzeroLimitTransport
variable {K : Type*} [Field K] {n : ℕ}

abbrev Smaller (w : Fin n → ℤ) (j : Fin n) := {i : Fin n // w i < w j}

def principalBlock (w : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) K) (j : Fin n) :
    Matrix (Smaller w j) (Smaller w j) K := A.submatrix Subtype.val Subtype.val

def correction (w : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) K) (j : Fin n) :
    Smaller w j → K := (principalBlock w A j)⁻¹.mulVec (fun i => A i.val j)

def correctingMatrix (w : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => (1 : Matrix (Fin n) (Fin n) K) i j -
    if h : w i < w j then correction w A j ⟨i,h⟩ else 0

theorem correctingMatrix_upper (w : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) K) :
    WeightUpperUnipotent w (correctingMatrix w A) := by
  constructor
  · intro i
    simp [correctingMatrix]
  · intro i j hij hw
    simp [correctingMatrix, hij, not_lt_of_ge hw]

theorem sum_dependent_subtype {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (f : ∀ i, p i → K) :
    (∑ i, if h : p i then f i h else 0) = ∑ i : Subtype p, f i.val i.property := by
  classical
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  exact (Equiv.subtypeEquivRight (by simp)).sum_comp (fun i : Subtype p => f i.val i.property)

theorem mul_correctingMatrix (w : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) :
    (A * correctingMatrix w A) i j = A i j -
      ∑ k : Smaller w j, A i k.val * correction w A j k := by
  classical
  simp only [Matrix.mul_apply, correctingMatrix, mul_sub, Finset.sum_sub_distrib]
  have hfirst : (∑ k, A i k * (1 : Matrix (Fin n) (Fin n) K) k j) = A i j := by
    simp [Matrix.one_apply, mul_ite]
  rw [hfirst]
  congr 1
  simp only [mul_dite, mul_zero]
  exact sum_dependent_subtype (fun k => w k < w j) (fun k hk => A i k * correction w A j ⟨k,hk⟩)

theorem corrected_lower (w : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ j, (principalBlock w A j).det ≠ 0) :
    WeightLowerTriangular w (A * correctingMatrix w A) := by
  intro i j hij
  by_contra hn
  have hlt : w i < w j := by omega
  have hu : IsUnit (principalBlock w A j).det := isUnit_iff_ne_zero.mpr (hA j)
  have he := congrFun (congrArg (fun M : Matrix (Smaller w j) (Smaller w j) K =>
      M.mulVec (fun k => A k.val j)) (Matrix.mul_nonsing_inv (principalBlock w A j) hu)) ⟨i,hlt⟩
  have hsum : (∑ k : Smaller w j, A i k.val * correction w A j k) = A i j := by
    simpa only [← Matrix.mulVec_mulVec, Matrix.one_mulVec, principalBlock,
      Matrix.submatrix_apply] using he
  exact hij (by rw [mul_correctingMatrix, hsum, sub_self])

def principalPolynomial (w : Fin n → ℤ) (j : Fin n) :
    MvPolynomial (Fin n × Fin n) K :=
  Matrix.det (fun i k : Smaller w j => X (i.val,k.val))

theorem eval_principalPolynomial (w : Fin n → ℤ) (j : Fin n)
    (A : Matrix (Fin n) (Fin n) K) :
    eval (fun ij => A ij.1 ij.2) (principalPolynomial w j) = (principalBlock w A j).det := by
  unfold principalPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i k
  simp [principalBlock]

def bigCellPolynomial (w : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) K :=
  ∏ j, principalPolynomial w j

theorem eval_bigCellPolynomial (w : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) K) :
    eval (fun ij => A ij.1 ij.2) (bigCellPolynomial w) = ∏ j, (principalBlock w A j).det := by
  simp [bigCellPolynomial, eval_principalPolynomial]

theorem principalBlock_one (w : Fin n → ℤ) (j : Fin n) :
    principalBlock w (1 : Matrix (Fin n) (Fin n) K) j = 1 := by
  ext i k
  simp [principalBlock, Matrix.one_apply, Subtype.val_inj]

/-- A complete elementary construction of the ordinary opposite big cell. -/
theorem specialLinearBigCellInput : ReducedBigCell.SpecialLinearBigCellInput where
  principal_neighborhood w := by
    classical
    refine ⟨bigCellPolynomial w, ?_, ?_⟩
    · rw [eval_bigCellPolynomial]
      simp [principalBlock_one]
    · intro A hAdet hq
      have hA : ∀ j, (principalBlock w A j).det ≠ 0 := by
        rw [eval_bigCellPolynomial] at hq
        exact fun j => Finset.prod_ne_zero_iff.mp hq j (Finset.mem_univ j)
      let V := correctingMatrix w A
      have hV := correctingMatrix_upper w A
      have hd : V.det = 1 := upper_det_one w V hV
      have hu : IsUnit V.det := by rw [hd]; exact isUnit_one
      refine ⟨V⁻¹,V,A*V,?_,Matrix.nonsing_inv_mul V hu,hd,upper_inverse w V hV,hV,corrected_lower w A hA⟩
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv V hu, mul_one]

end HessianTheorem11.ReducedOrdinaryBigCell
