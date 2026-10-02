import CubicTenVariables.CubicFactorCharts
import HessianTheorem11.CubicRankIrreducibility
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Multiplication by an actual homogeneous linear form, in finite
coefficient coordinates. Its matrix has full column rank away from the
zero linear form. Reducibility of a homogeneous cubic is therefore an
image-membership condition with only the projective linear factor varying.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.CubicLinearFactorMatrix
open MvPolynomial CubicFactorCharts

variable {R : Type*} [CommRing R] {n : ℕ}

def linearForm (a : Fin n → R) : MvPolynomial (Fin n) R :=
  ∑ i, C (a i) * X i

theorem linearForm_homogeneous (a : Fin n → R) : (linearForm a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

@[simp] theorem coeff_linearForm (a : Fin n → R) (i : Fin n) :
    coeff (Finsupp.single i 1) (linearForm a) = a i := by
  simp [linearForm, coeff_sum, coeff_C_mul, coeff_X]

@[simp] theorem linearForm_zero : linearForm (0 : Fin n → R) = 0 := by
  simp [linearForm]

theorem linearForm_ne_zero {a : Fin n → R} (ha : a ≠ 0) : linearForm a ≠ 0 := by
  intro h
  apply ha
  ext i
  have hh := congrArg (coeff (Finsupp.single i 1)) h
  simpa using hh

/-- Columns are the bounded quadratic monomials; rows are the bounded
cubic monomials. Every entry is an actual coefficient of a product. -/
def multiplicationMatrix (a : Fin n → R) :
    Matrix (Monomial n 3) (Monomial n 2) R :=
  fun row col ↦ coeff row.val (linearForm a * monomial col.val 1)

theorem multiplicationMatrix_mulVec (a : Fin n → R) (c : Monomial n 2 → R) :
    (multiplicationMatrix a).mulVec c =
      fun row : Monomial n 3 ↦ coeff row.val (linearForm a * polynomial c) := by
  ext row
  simp only [Matrix.mulVec, dotProduct, multiplicationMatrix, polynomial,
    Finset.mul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro col _
  have hm : monomial col.val (c col) = C (c col) * monomial col.val (1 : R) := by
    rw [C_mul_monomial, mul_one]
  rw [hm, mul_left_comm, coeff_C_mul]
  ring

/-- Reconstructing the output coefficient vector gives the literal
product polynomial, with no omitted terms above the truncation degree. -/
theorem polynomial_multiplicationMatrix_mulVec (a : Fin n → R) (c : Monomial n 2 → R) :
    polynomial ((multiplicationMatrix a).mulVec c) = linearForm a * polynomial c := by
  rw [multiplicationMatrix_mulVec]
  apply polynomial_coefficients
  exact (totalDegree_mul _ _).trans (add_le_add
    (linearForm_homogeneous a).totalDegree_le (polynomial_totalDegree_le c))

theorem multiplicationMatrix_injective [IsDomain R]
    (a : Fin n → R) (ha : a ≠ 0) : Function.Injective (multiplicationMatrix a).mulVec := by
  intro c d h
  have he := congrArg polynomial h
  rw [polynomial_multiplicationMatrix_mulVec, polynomial_multiplicationMatrix_mulVec] at he
  have hpoly := mul_left_cancel₀ (linearForm_ne_zero ha) he
  ext m
  simpa only [coeff_polynomial] using congrArg (coeff m.val) hpoly

theorem multiplicationMatrix_rank {K : Type*} [Field K]
    (a : Fin n → K) (ha : a ≠ 0) :
    (multiplicationMatrix a).rank = Fintype.card (Monomial n 2) := by
  have hi : Function.Injective (Matrix.mulVecLin (multiplicationMatrix a)) :=
    multiplicationMatrix_injective a ha
  change Module.finrank K (LinearMap.range (Matrix.mulVecLin (multiplicationMatrix a))) = _
  rw [LinearMap.finrank_range_of_inj hi, Module.finrank_pi]

/-- The entries of the universal multiplication matrix are homogeneous
linear polynomials in the coefficients of the potential linear factor. -/
def universalMatrix (n : ℕ) (R : Type*) [CommRing R] :
    Matrix (Monomial n 3) (Monomial n 2) (MvPolynomial (Fin n) R) :=
  fun row col ↦ ∑ i, C (coeff row.val (X i * monomial col.val (1 : R))) * X i

theorem universalMatrix_homogeneous (n : ℕ) (R : Type*) [CommRing R]
    (row : Monomial n 3) (col : Monomial n 2) :
    (universalMatrix n R row col).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

theorem eval_universalMatrix (a : Fin n → R) (row : Monomial n 3) (col : Monomial n 2) :
    eval a (universalMatrix n R row col) = multiplicationMatrix a row col := by
  simp only [universalMatrix, map_sum, map_mul, eval_C, eval_X,
    multiplicationMatrix, linearForm, Finset.sum_mul, coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, coeff_C_mul]
  ring

theorem map_universalMatrix {S : Type*} [CommRing S] (ρ : R →+* S)
    (row : Monomial n 3) (col : Monomial n 2) :
    map ρ (universalMatrix n R row col) = universalMatrix n S row col := by
  simp only [universalMatrix, map_sum, map_mul, map_C, map_X]
  apply Finset.sum_congr rfl
  intro i _
  rw [← coeff_map, map_mul, map_X, map_monomial, map_one]

theorem eval₂_universalMatrix {S : Type*} [CommRing S]
    (ρ : R →+* S) (a : Fin n → S) (row : Monomial n 3) (col : Monomial n 2) :
    eval₂ ρ a (universalMatrix n R row col) = multiplicationMatrix a row col := by
  rw [eval₂_eq_eval_map, map_universalMatrix, eval_universalMatrix]

/-- Image membership is precisely divisibility by the literal linear
form, with a quadratic quotient represented by its own coefficients. -/
theorem exists_coefficients_iff
    (a : Fin n → R) (F : MvPolynomial (Fin n) R) (hF : F.totalDegree ≤ 3) :
    (∃ c : Monomial n 2 → R,
      (multiplicationMatrix a).mulVec c = fun row : Monomial n 3 ↦ coeff row.val F) ↔
    ∃ Q : MvPolynomial (Fin n) R, Q.totalDegree ≤ 2 ∧ F = linearForm a * Q := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨polynomial c, polynomial_totalDegree_le c, ?_⟩
    have h := congrArg polynomial hc
    rw [polynomial_multiplicationMatrix_mulVec, polynomial_coefficients F hF] at h
    exact h.symm
  · rintro ⟨Q, hQ, he⟩
    refine ⟨fun m ↦ coeff m.val Q, ?_⟩
    rw [multiplicationMatrix_mulVec, polynomial_coefficients Q hQ, ← he]

/-- The only nonlinear witness needed for a reducible homogeneous cubic
is its nonzero vector of linear-factor coefficients. The quadratic factor
is exactly a solution to the displayed finite linear system. -/
theorem not_irreducible_iff_matrix_solution {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hFne : F ≠ 0) :
    (¬ Irreducible F) ↔ ∃ a : Fin n → K, a ≠ 0 ∧
      ∃ c : Monomial n 2 → K,
        (multiplicationMatrix a).mulVec c = fun row : Monomial n 3 ↦ coeff row.val F := by
  constructor
  · intro hred
    obtain ⟨L, Q, hL, hQ, hprod⟩ :=
      HessianTheorem11.reducible_homogeneous_cubic_linear_times_quadratic F hF hFne hred
    let a : Fin n → K := fun i ↦ coeff (Finsupp.single i 1) L
    have hL0 : coeff 0 L = 0 := hL.coeff_eq_zero (by simp)
    have hLa : linearForm a = L := by
      have h := HessianTheorem11.eq_affine_linear_of_totalDegree_le_one L hL.totalDegree_le
      simpa only [hL0, map_zero, zero_add, linearForm, a] using h.symm
    have ha : a ≠ 0 := by
      intro h
      apply hFne
      rw [hprod, ← hLa, h, linearForm_zero, zero_mul]
    refine ⟨a, ha, (exists_coefficients_iff a F hF.totalDegree_le).mpr ?_⟩
    exact ⟨Q, hQ.totalDegree_le, by rwa [hLa]⟩
  · rintro ⟨a, ha, hc⟩ hirr
    obtain ⟨Q, hQ, he⟩ := (exists_coefficients_iff a F hF.totalDegree_le).mp hc
    rcases hirr.isUnit_or_isUnit he with hunit | hunit
    · have hz := (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
      have hone := (linearForm_homogeneous a).totalDegree (linearForm_ne_zero ha)
      omega
    · have hQzero : Q ≠ 0 := by intro h; rw [h, mul_zero] at he; exact hFne he
      have hdeg := totalDegree_mul_of_isDomain (linearForm_ne_zero ha) hQzero
      rw [← he, hF.totalDegree hFne,
        (linearForm_homogeneous a).totalDegree (linearForm_ne_zero ha),
        (isUnit_iff_totalDegree_of_isReduced.mp hunit).2] at hdeg
      omega

end CubicTenVariables.CubicLinearFactorMatrix
