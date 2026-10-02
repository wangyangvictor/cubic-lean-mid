import HessianTheorem11.HessianDeterminant
import HessianTheorem11.PolynomialRestriction
import HessianTheorem11.Restriction

/-!
A polynomial that depends on fewer linear coordinates than the ambient
number of variables has zero Hessian determinant. Products of homogeneous
linear factors are factored through the actual matrix of their coefficients.
These are polynomial and matrix theorems, with no external geometric inputs.
-/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

section Rank
variable {K : Type*} [Field K] {m n : ℕ}

/-- The actual Hessian of a polynomial pulled back from `m` linear coordinates
has rank at most `m`, at every point. -/
theorem hessian_rank_restrict_le_variables
    (B : Matrix (Fin m) (Fin n) K) (Q : MvPolynomial (Fin m) K)
    (x : Fin n → K) :
    (hessian (PolynomialRestriction.restrict B Q) x).rank ≤ m := by
  rw [PolynomialRestriction.hessian_restrict]
  exact (Restriction.rank_congruence_le _ _).trans
    (Matrix.rank_le_width (A := hessian Q (B.mulVec x)))

/-- A square matrix of deficient rank has zero determinant. -/
theorem determinant_eq_zero_of_rank_lt
    (M : Matrix (Fin n) (Fin n) K) (hM : M.rank < n) : M.det = 0 := by
  by_contra hd
  have hunit : IsUnit M := M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd)
  have hr := Matrix.rank_of_isUnit M hunit
  simp only [Fintype.card_fin] at hr
  omega

variable [Infinite K]

/-- Pullback from fewer variables forces the actual Hessian determinant
polynomial to vanish. The conclusion follows from the formal Hessian chain
rule and polynomial extensionality over the infinite base field. -/
theorem hessianDeterminantPolynomial_restrict_eq_zero
    (B : Matrix (Fin m) (Fin n) K) (Q : MvPolynomial (Fin m) K) (hmn : m < n) :
    hessianDeterminantPolynomial (PolynomialRestriction.restrict B Q) = 0 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_hessianDeterminantPolynomial, map_zero]
  exact determinant_eq_zero_of_rank_lt _
    ((hessian_rank_restrict_le_variables B Q x).trans_lt hmn)

theorem hessianDeterminantPolynomial_eq_zero_of_fewer_variables
    (F : MvPolynomial (Fin n) K) (B : Matrix (Fin m) (Fin n) K)
    (Q : MvPolynomial (Fin m) K) (hF : F = PolynomialRestriction.restrict B Q)
    (hmn : m < n) : hessianDeterminantPolynomial F = 0 := by
  rw [hF]
  exact hessianDeterminantPolynomial_restrict_eq_zero B Q hmn

end Rank

section Products
variable {K : Type*} [CommRing K] {m n : ℕ}

/-- The actual linear coefficient matrix, extracted by formal differentiation. -/
def linearFormCoefficientMatrix (L : Fin m → MvPolynomial (Fin n) K) :
    Matrix (Fin m) (Fin n) K := fun i j => coeff 0 (pderiv j (L i))

theorem linearForms_linearFormCoefficientMatrix
    (L : Fin m → MvPolynomial (Fin n) K) (hL : ∀ i, (L i).IsHomogeneous 1)
    (i : Fin m) :
    PolynomialRestriction.linearForms (linearFormCoefficientMatrix L) i = L i := by
  rw [homogeneous_one_expansion (hL i)]
  unfold PolynomialRestriction.linearForms linearFormCoefficientMatrix
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- The scalar multiple of the product of all coordinate variables in the
smaller polynomial ring. -/
def variableProductPolynomial (a : K) (m : ℕ) : MvPolynomial (Fin m) K :=
  C a * ∏ i, X i

theorem restrict_variableProductPolynomial
    (B : Matrix (Fin m) (Fin n) K) (a : K) :
    PolynomialRestriction.restrict B (variableProductPolynomial a m) =
      C a * ∏ i, PolynomialRestriction.linearForms B i := by
  simp [PolynomialRestriction.restrict, variableProductPolynomial]

/-- A scalar times `m` homogeneous linear forms factors through the `m`
linear coordinates given by their explicit coefficient matrix. -/
theorem product_linearForms_eq_restrict
    (a : K) (L : Fin m → MvPolynomial (Fin n) K)
    (hL : ∀ i, (L i).IsHomogeneous 1) :
    C a * ∏ i, L i = PolynomialRestriction.restrict
      (linearFormCoefficientMatrix L) (variableProductPolynomial a m) := by
  rw [restrict_variableProductPolynomial]
  simp only [linearForms_linearFormCoefficientMatrix L hL]

end Products

section ProductDeterminant
variable {K : Type*} [Field K] [Infinite K] {m n : ℕ}

/-- A product of fewer homogeneous linear factors than ambient variables has
identically zero Hessian determinant, with any scalar prefactor. -/
theorem hessianDeterminantPolynomial_product_linearForms_eq_zero
    (a : K) (L : Fin m → MvPolynomial (Fin n) K)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hmn : m < n) :
    hessianDeterminantPolynomial (C a * ∏ i, L i) = 0 := by
  rw [product_linearForms_eq_restrict a L hL]
  exact hessianDeterminantPolynomial_restrict_eq_zero _ _ hmn

/-- The form needed to exclude a cubic splitting into three geometric linear
factors in at least four variables. -/
theorem hessianDeterminantPolynomial_eq_zero_of_three_linear_factors
    {F : MvPolynomial (Fin n) K} (a : K)
    (L : Fin 3 → MvPolynomial (Fin n) K)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hF : F = C a * ∏ i, L i) (hn : 4 ≤ n) :
    hessianDeterminantPolynomial F = 0 := by
  rw [hF]
  exact hessianDeterminantPolynomial_product_linearForms_eq_zero a L hL (by omega)

/-- Nonzero Hessian determinant therefore excludes such a factorization. -/
theorem not_three_linear_factors_of_hessianDeterminantPolynomial_ne_zero
    {F : MvPolynomial (Fin n) K} (hdet : hessianDeterminantPolynomial F ≠ 0)
    (hn : 4 ≤ n) :
    ¬ ∃ (a : K) (L : Fin 3 → MvPolynomial (Fin n) K),
      (∀ i, (L i).IsHomogeneous 1) ∧ F = C a * ∏ i, L i := by
  rintro ⟨a, L, hL, hF⟩
  exact hdet (hessianDeterminantPolynomial_eq_zero_of_three_linear_factors a L hL hF hn)

end ProductDeterminant
end HessianTheorem11
