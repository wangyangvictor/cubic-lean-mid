import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
Second-order coefficients of actual matrix power series, the hyperbolic
cross-block cancellation, and polarization. No geometric hypothesis and no
Clifford relation is postulated in this module.
-/

noncomputable section
namespace HessianTheorem11.SchurSecondOrder
open Matrix PowerSeries
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Entrywise coefficient of a matrix power series. -/
def matrixCoeff {ι κ : Type*} (d : ℕ) (M : Matrix ι κ (PowerSeries R)) : Matrix ι κ R :=
  fun i j => PowerSeries.coeff d (M i j)

@[simp] theorem matrixCoeff_zero {ι κ : Type*} (d : ℕ) :
    matrixCoeff d (0 : Matrix ι κ (PowerSeries R)) = 0 := by
  ext i j
  simp [matrixCoeff]

@[simp] theorem matrixCoeff_sub {ι κ : Type*} (d : ℕ)
    (A B : Matrix ι κ (PowerSeries R)) :
    matrixCoeff d (A - B) = matrixCoeff d A - matrixCoeff d B := by
  ext i j
  simp [matrixCoeff]

@[simp] theorem matrixCoeff_transpose {ι κ : Type*} (d : ℕ)
    (A : Matrix ι κ (PowerSeries R)) : matrixCoeff d A.transpose = (matrixCoeff d A).transpose := rfl

theorem coeff_mul_zero (a b : PowerSeries R) :
    coeff 0 (a * b) = coeff 0 a * coeff 0 b := by
  simp only [coeff_zero_eq_constantCoeff, map_mul]

theorem coeff_mul_one (a b : PowerSeries R) :
    coeff 1 (a * b) = coeff 0 a * coeff 1 b + coeff 1 a * coeff 0 b := by
  rw [coeff_mul]
  have h : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := rfl
  simp [h]

theorem coeff_mul_two (a b : PowerSeries R) :
    coeff 2 (a * b) = coeff 0 a * coeff 2 b + coeff 1 a * coeff 1 b +
      coeff 2 a * coeff 0 b := by
  rw [coeff_mul]
  have h : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := rfl
  simp [h, add_assoc]

theorem matrixCoeff_mul_zero {ι κ υ : Type*} [Fintype κ]
    (A : Matrix ι κ (PowerSeries R)) (B : Matrix κ υ (PowerSeries R)) :
    matrixCoeff 0 (A * B) = matrixCoeff 0 A * matrixCoeff 0 B := by
  ext i j
  simp [matrixCoeff, Matrix.mul_apply, map_sum, coeff_mul_zero]

theorem matrixCoeff_mul_one {ι κ υ : Type*} [Fintype κ]
    (A : Matrix ι κ (PowerSeries R)) (B : Matrix κ υ (PowerSeries R)) :
    matrixCoeff 1 (A * B) = matrixCoeff 0 A * matrixCoeff 1 B +
      matrixCoeff 1 A * matrixCoeff 0 B := by
  ext i j
  simp [matrixCoeff, Matrix.mul_apply, map_sum, coeff_mul_one, Finset.sum_add_distrib]

theorem matrixCoeff_mul_two {ι κ υ : Type*} [Fintype κ]
    (A : Matrix ι κ (PowerSeries R)) (B : Matrix κ υ (PowerSeries R)) :
    matrixCoeff 2 (A * B) = matrixCoeff 0 A * matrixCoeff 2 B +
      matrixCoeff 1 A * matrixCoeff 1 B + matrixCoeff 2 A * matrixCoeff 0 B := by
  ext i j
  simp [matrixCoeff, Matrix.mul_apply, map_sum, coeff_mul_two, Finset.sum_add_distrib]

/-- When both outer cross blocks start at order one, their quadratic
product depends only on the constant matrix in the middle. -/
theorem matrixCoeff_two_triple_of_outer_zero
    {ι κ υ μ : Type*} [Fintype κ] [Fintype υ]
    (C : Matrix ι κ (PowerSeries R)) (J : Matrix κ υ (PowerSeries R))
    (D : Matrix υ μ (PowerSeries R))
    (hC : matrixCoeff 0 C = 0) (hD : matrixCoeff 0 D = 0) :
    matrixCoeff 2 (C * J * D) = matrixCoeff 1 C * matrixCoeff 0 J * matrixCoeff 1 D := by
  rw [matrixCoeff_mul_two, matrixCoeff_mul_zero, matrixCoeff_mul_one, hC, hD]
  simp

/-- The constant coefficient of an actual right inverse is the inverse of
the constant block. Higher coefficients of the inverse need not be computed. -/
theorem matrixCoeff_zero_inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K J : Matrix ι ι (PowerSeries R)) [Invertible (matrixCoeff 0 K)]
    (hKJ : K * J = 1) : matrixCoeff 0 J = ⅟(matrixCoeff 0 K) := by
  have h := congrArg (matrixCoeff 0) hKJ
  rw [matrixCoeff_mul_zero] at h
  have h1 : matrixCoeff 0 (1 : Matrix ι ι (PowerSeries R)) = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [matrixCoeff, Matrix.one_apply, hij]
  rw [h1] at h
  calc
    matrixCoeff 0 J = ⅟(matrixCoeff 0 K) * (matrixCoeff 0 K * matrixCoeff 0 J) := by
      rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = ⅟(matrixCoeff 0 K) := by rw [h, mul_one]

/-- The exact second coefficient of a Schur block with zero constant cross
block, for an actual inverse power-series matrix. -/
theorem schur_second_coefficient
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι (PowerSeries R)) (C : Matrix ι κ (PowerSeries R))
    (K J : Matrix κ κ (PowerSeries R)) [Invertible (matrixCoeff 0 K)]
    (hKJ : K * J = 1) (hC : matrixCoeff 0 C = 0) :
    matrixCoeff 2 (A - C * J * C.transpose) =
      matrixCoeff 2 A - matrixCoeff 1 C * ⅟(matrixCoeff 0 K) * (matrixCoeff 1 C).transpose := by
  rw [matrixCoeff_sub, matrixCoeff_two_triple_of_outer_zero C J C.transpose hC
    (by simp [hC]), matrixCoeff_zero_inverse K J hKJ, matrixCoeff_transpose]

/-- Vanishing of the actual Schur block gives its quadratic matrix equation. -/
theorem schur_second_identity
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι (PowerSeries R)) (C : Matrix ι κ (PowerSeries R))
    (K J : Matrix κ κ (PowerSeries R)) [Invertible (matrixCoeff 0 K)]
    (hKJ : K * J = 1) (hC : matrixCoeff 0 C = 0)
    (hSchur : A - C * J * C.transpose = 0) :
    matrixCoeff 2 A = matrixCoeff 1 C * ⅟(matrixCoeff 0 K) * (matrixCoeff 1 C).transpose := by
  have h := congrArg (matrixCoeff 2) hSchur
  rw [schur_second_coefficient A C K J hKJ hC, matrixCoeff_zero] at h
  exact sub_eq_zero.mp h

/-- The inverse complementary block in the order `(b,X,z)`. The order differs
from the source only by the displayed permutation of the three blocks. -/
def normalInverse {κ : Type*} (B : Matrix κ κ R) (half : R) :
    Matrix (κ ⊕ Fin 2) (κ ⊕ Fin 2) R :=
  Matrix.fromBlocks B 0 0 !![0, half; half, 0]

/-- The first cross coefficient has zero `X` column; its `z` column is
arbitrary and can contain all the allowed remainder contributions. -/
def crossFirst {ι κ : Type*} (W : Matrix ι κ R) (z : ι → R) :
    Matrix ι (κ ⊕ Fin 2) R :=
  fun i => Sum.elim (W i) ![0, z i]

/-- The arbitrary `az` coefficients contribute nothing to the quadratic
Schur term, because the inverse hyperbolic plane pairs `z` only with `X`. -/
theorem hyperbolic_cross_cancellation {ι κ : Type*} [Fintype κ]
    (W : Matrix ι κ R) (z : ι → R) (B : Matrix κ κ R) (half : R) :
    crossFirst W z * normalInverse B half * (crossFirst W z).transpose =
      W * B * W.transpose := by
  ext i j
  simp [crossFirst, normalInverse, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.fromBlocks]

/-- Equality of quadratic functions determines the symmetric part of a
matrix, with no division or characteristic assumption. -/
theorem add_transpose_eq_of_quadratic_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M N : Matrix κ κ R) (hN : N.transpose = N)
    (hquad : ∀ v : κ → R, dotProduct v (M.mulVec v) = dotProduct v (N.mulVec v)) :
    M + M.transpose = (2 : R) • N := by
  ext i j
  have hi := hquad (Pi.single i 1)
  have hj := hquad (Pi.single j 1)
  have hij := hquad (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_single_one, single_dotProduct, one_mul] at hi hj hij
  simp only [Matrix.col, Matrix.transpose_apply] at hi hj hij
  have hsym : N j i = N i j := congrArg (fun A : Matrix κ κ R => A i j) hN
  change M i j + M j i = 2 * N i j
  linear_combination hij - hi - hj + hsym

/-- The source's scalar second-order identity, polarized in the vector.
Symmetry of each displayed matrix is retained as an actual matrix equality. -/
theorem clifford_relation_of_quadratic_identity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Bi Bj BInv B0 : Matrix κ κ R) (p : R)
    (hi : Bi.transpose = Bi) (hj : Bj.transpose = Bj)
    (hinv : BInv.transpose = BInv) (h0 : B0.transpose = B0)
    (hquad : ∀ v : κ → R,
      dotProduct v ((Bi * BInv * Bj).mulVec v) = -p * dotProduct v (B0.mulVec v)) :
    Bi * BInv * Bj + Bj * BInv * Bi = (-2 * p) • B0 := by
  have hN : ((-p) • B0).transpose = (-p) • B0 := by simp [h0]
  have hq : ∀ v : κ → R,
      dotProduct v ((Bi * BInv * Bj).mulVec v) = dotProduct v (((-p) • B0).mulVec v) := by
    intro v
    rw [hquad, Matrix.smul_mulVec, dotProduct_smul]
    rfl
  have h := add_transpose_eq_of_quadratic_eq (Bi * BInv * Bj) ((-p) • B0) hN hq
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hi, hj, hinv] at h
  simpa [mul_assoc, smul_smul] using h

def quadraticRows {ι κ : Type*} [Fintype κ]
    (B : ι → Matrix κ κ R) (v : κ → R) : Matrix ι κ R :=
  fun i j => (B i).mulVec v j

/-- A row matrix of the vectors `B_i v`, paired through `BInv`, gives the
quadratic function of `B_i BInv B_j` when `B_i` is symmetric. -/
theorem quadratic_row_product {ι κ : Type*} [Fintype κ]
    (B : ι → Matrix κ κ R) (BInv : Matrix κ κ R) (v : κ → R)
    (i j : ι) (hi : (B i).transpose = B i) :
    ((quadraticRows B v) * BInv *
      (quadraticRows B v).transpose) i j =
      dotProduct v ((B i * BInv * B j).mulVec v) := by
  have hrows : ((quadraticRows B v) * BInv *
      (quadraticRows B v).transpose) i j =
      dotProduct ((B i).mulVec v) (BInv.mulVec ((B j).mulVec v)) := by
    change dotProduct (Matrix.vecMul ((B i).mulVec v) BInv) ((B j).mulVec v) = _
    exact (dotProduct_mulVec ((B i).mulVec v) BInv ((B j).mulVec v)).symm
  have hv : Matrix.vecMul v (B i) = (B i).mulVec v := by
    simpa only [hi] using Matrix.vecMul_transpose (B i) v
  rw [hrows, ← hv]
  rw [← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- All the second-order premises are coefficients of actual power-series
matrices. The conclusion is derived by coefficient extraction, hyperbolic
cancellation, and polarization; it is not supplied as an assumption. -/
theorem clifford_relations_of_schur_coefficients
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Matrix ι ι R) (B : ι → Matrix κ κ R) (B0 BInv : Matrix κ κ R) (half : R)
    (hB : ∀ i, (B i).transpose = B i)
    (h0 : B0.transpose = B0) (hinv : BInv.transpose = BInv)
    (A : (κ → R) → Matrix ι ι (PowerSeries R))
    (C : (κ → R) → Matrix ι (κ ⊕ Fin 2) (PowerSeries R))
    (J : (κ → R) → Matrix (κ ⊕ Fin 2) (κ ⊕ Fin 2) (PowerSeries R))
    (hSchur : ∀ v, A v - C v * J v * (C v).transpose = 0)
    (hC0 : ∀ v, matrixCoeff 0 (C v) = 0)
    (hJ0 : ∀ v, matrixCoeff 0 (J v) = normalInverse BInv half)
    (hC1 : ∀ v, ∃ z : ι → R,
      matrixCoeff 1 (C v) = crossFirst (quadraticRows B v) z)
    (hA2 : ∀ v, matrixCoeff 2 (A v) = (-dotProduct v (B0.mulVec v)) • P) :
    ∀ i j, B i * BInv * B j + B j * BInv * B i = (-2 * P i j) • B0 := by
  intro i j
  apply clifford_relation_of_quadratic_identity (B i) (B j) BInv B0 (P i j)
    (hB i) (hB j) hinv h0
  intro v
  obtain ⟨z, hz⟩ := hC1 v
  have hs := congrArg (matrixCoeff 2) (hSchur v)
  rw [matrixCoeff_sub, matrixCoeff_two_triple_of_outer_zero (C v) (J v) (C v).transpose
    (hC0 v) (by simp [hC0 v]), matrixCoeff_transpose, hJ0 v, hz,
    hyperbolic_cross_cancellation, hA2 v, matrixCoeff_zero] at hs
  have he := congrArg (fun M : Matrix ι ι R => M i j) (sub_eq_zero.mp hs)
  change (-dotProduct v (B0.mulVec v)) * P i j =
    (quadraticRows B v * BInv * (quadraticRows B v).transpose) i j at he
  rw [quadratic_row_product B BInv v i j (hB i)] at he
  rw [← he]
  ring

/-- Multiplication verifies the displayed hyperbolic inverse block. -/
theorem normalInverse_mul {κ : Type*} [Fintype κ] [DecidableEq κ]
    (BInv B0 : Matrix κ κ R) (half two : R)
    (hB : BInv * B0 = 1) (hh : half * two = 1) :
    normalInverse BInv half * normalInverse B0 two = 1 := by
  ext (i | i) (j | j) <;>
    simp [normalInverse, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks, Fin.sum_univ_two]
  · simpa [Matrix.mul_apply, Matrix.one_apply] using
      congrArg (fun M : Matrix κ κ R => M i j) hB
  · fin_cases i <;> fin_cases j <;> simp [hh]

/-- Uniqueness of left/right inverse after taking constant coefficients. -/
theorem matrixCoeff_zero_inverse_of_left_inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K J : Matrix ι ι (PowerSeries R)) (N : Matrix ι ι R)
    (hKJ : K * J = 1) (hN : N * matrixCoeff 0 K = 1) : matrixCoeff 0 J = N := by
  have h := congrArg (matrixCoeff 0) hKJ
  rw [matrixCoeff_mul_zero] at h
  have h1 : matrixCoeff 0 (1 : Matrix ι ι (PowerSeries R)) = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [matrixCoeff, Matrix.one_apply, hij]
  rw [h1] at h
  calc
    matrixCoeff 0 J = N * (matrixCoeff 0 K * matrixCoeff 0 J) := by
      rw [← mul_assoc, hN, one_mul]
    _ = N := by rw [h, mul_one]

/-- Full power-series version of the source calculation. The inverse is an
actual right inverse of the complementary block; its constant coefficient is
proved from the displayed hyperbolic block, not provided as a premise. -/
theorem clifford_relations_of_schur_inverse
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Matrix ι ι R) (B : ι → Matrix κ κ R) (B0 BInv : Matrix κ κ R)
    (half two : R) (hhalf : half * two = 1) (hBinv : BInv * B0 = 1)
    (hB : ∀ i, (B i).transpose = B i)
    (h0 : B0.transpose = B0) (hinv : BInv.transpose = BInv)
    (A : (κ → R) → Matrix ι ι (PowerSeries R))
    (C : (κ → R) → Matrix ι (κ ⊕ Fin 2) (PowerSeries R))
    (K J : (κ → R) → Matrix (κ ⊕ Fin 2) (κ ⊕ Fin 2) (PowerSeries R))
    (hKJ : ∀ v, K v * J v = 1)
    (hK0 : ∀ v, matrixCoeff 0 (K v) = normalInverse B0 two)
    (hSchur : ∀ v, A v - C v * J v * (C v).transpose = 0)
    (hC0 : ∀ v, matrixCoeff 0 (C v) = 0)
    (hC1 : ∀ v, ∃ z : ι → R, matrixCoeff 1 (C v) = crossFirst (quadraticRows B v) z)
    (hA2 : ∀ v, matrixCoeff 2 (A v) = (-dotProduct v (B0.mulVec v)) • P) :
    ∀ i j, B i * BInv * B j + B j * BInv * B i = (-2 * P i j) • B0 := by
  apply clifford_relations_of_schur_coefficients P B B0 BInv half hB h0 hinv
    A C J hSchur hC0 _ hC1 hA2
  intro v
  apply matrixCoeff_zero_inverse_of_left_inverse (K v) (J v) _ (hKJ v)
  rw [hK0 v]
  exact normalInverse_mul BInv B0 half two hBinv hhalf

end HessianTheorem11.SchurSecondOrder
