import HessianTheorem11.GeometricInjectivity
import HessianTheorem11.PolynomialRestriction
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Essential variables after extension of the rational coefficient field

A polynomial whose actual Hessian pencil is injective cannot be a polynomial
in fewer linear forms than its number of variables. Indeed the chain rule
makes its Hessian constant on every fiber of the proposed linear map, so that
linear map must be injective.

For a rational anisotropic homogeneous cubic, the already proved injectivity
of its Hessian pencil survives every field extension of ℚ. Thus all its
variables remain essential over that extension. The pullback used below is
literal substitution of the forms `∑ j, C (A i j) * X j`; the polynomial in
those forms is arbitrary, with no assumed degree or homogeneity. This is the
algebraic variable-order adapter, and asserts no local zero-existence result.
-/

noncomputable section

namespace CubicTenVariables.EssentialVariables

open MvPolynomial HessianTheorem11
open HessianTheorem11.PolynomialRestriction

/-- Every linear factorization of a polynomial with injective Hessian pencil
uses an injective linear map. The factorization is an equality of actual
multivariate polynomials, not a factorization of a separately supplied invariant. -/
theorem linearMap_injective_of_hessian_injective
    {K : Type*} [Field K] {m n : ℕ}
    (F : MvPolynomial (Fin n) K) (hH : Function.Injective (hessian F))
    (A : Matrix (Fin m) (Fin n) K) (G : MvPolynomial (Fin m) K)
    (hFG : F = restrict A G) : Function.Injective A.mulVec := by
  intro x y hxy
  apply hH
  rw [hFG, hessian_restrict, hessian_restrict, hxy]

/-- The number of linear forms in any displayed polynomial pullback is at
least the ambient dimension, if the actual Hessian pencil is injective. -/
theorem variables_le_of_hessian_injective
    {K : Type*} [Field K] {m n : ℕ}
    (F : MvPolynomial (Fin n) K) (hH : Function.Injective (hessian F))
    (A : Matrix (Fin m) (Fin n) K) (G : MvPolynomial (Fin m) K)
    (hFG : F = restrict A G) : n ≤ m := by
  have hA : Function.Injective A.mulVecLin :=
    linearMap_injective_of_hessian_injective F hH A G hFG
  simpa using LinearMap.finrank_le_finrank_of_injective hA

/-- Every variable of a rational anisotropic cubic remains essential over
any extension field of ℚ, expressed as a bound for a literal polynomial
pullback along the proposed list of linear forms. -/
theorem variables_le_of_baseChange_eq_linear_pullback
    {K : Type*} [Field K] [Algebra ℚ K] {m n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F)
    (A : Matrix (Fin m) (Fin n) K) (G : MvPolynomial (Fin m) K)
    (hFG : map (algebraMap ℚ K) F = restrict A G) : n ≤ m :=
  variables_le_of_hessian_injective _
    (baseChange_hessian_injective ⟨F, hF, hA⟩) A G hFG

/-- In particular, the scalar-extended cubic cannot be written as a polynomial
in `m < n` actual linear forms, including after a linear change of coordinates. -/
theorem not_baseChange_eq_linear_pullback_of_lt
    {K : Type*} [Field K] [Algebra ℚ K] {m n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) (hmn : m < n)
    (A : Matrix (Fin m) (Fin n) K) (G : MvPolynomial (Fin m) K) :
    map (algebraMap ℚ K) F ≠ restrict A G := by
  intro hFG
  exact (Nat.not_le_of_lt hmn)
    (variables_le_of_baseChange_eq_linear_pullback F hF hA A G hFG)

/-- Fully expanded substitution formulation of essentiality: no hidden
coordinate or order invariant occurs in the conclusion. -/
theorem not_baseChange_eq_aeval_linearForms_of_lt
    {K : Type*} [Field K] [Algebra ℚ K] {m n : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic F) (hmn : m < n)
    (A : Matrix (Fin m) (Fin n) K) (G : MvPolynomial (Fin m) K) :
    map (algebraMap ℚ K) F ≠ aeval (fun i => ∑ j, C (A i j) * X j) G :=
  not_baseChange_eq_linear_pullback_of_lt F hF hA hmn A G

end CubicTenVariables.EssentialVariables
