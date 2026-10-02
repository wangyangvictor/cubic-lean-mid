import TranslatedDepthSeven.StarEquationBounds
import TranslatedDepthSeven.Parameters
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The tangent kernel of a literal finite equation family

For a displayed finite family of integral equations and an integral base
point, this file defines the evaluated rational Jacobian matrix and its
kernel.  Directions of integral affine lines on every displayed equation
belong to that kernel.  Taking their rational span and applying rank--nullity
gives the corresponding dimension bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

open Finset MvPolynomial

/-- The rational Jacobian matrix of a literal finite integral equation family
at an integral base point.  Rows are indexed by the equations themselves. -/
def equationFamilyRationalJacobianMatrix {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n) :
    Matrix {f // f ∈ equations} (Fin n) ℚ :=
  fun f i ↦ ((MvPolynomial.eval h (MvPolynomial.pderiv i f.1) : ℤ) : ℚ)

/-- The evaluated Jacobian as an explicit rational linear map. -/
def equationFamilyRationalJacobianLinearMap {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n) :
    (Fin n → ℚ) →ₗ[ℚ] ({f // f ∈ equations} → ℚ) :=
  (equationFamilyRationalJacobianMatrix equations h).mulVecLin

/-- The literal rational Zariski tangent kernel cut out by the displayed
Jacobian rows. -/
def equationFamilyRationalTangentKernel {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ)) (h : IntVector n) :
    Submodule ℚ (Fin n → ℚ) :=
  LinearMap.ker (equationFamilyRationalJacobianLinearMap equations h)

/-- An integral direction whose full affine line lies on every displayed
equation is annihilated by the rational Jacobian. -/
theorem intDirection_mem_equationFamilyRationalTangentKernel
    {n : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ))
    (h z : IntVector n)
    (hline : ∀ f ∈ equations, ∀ t : ℤ,
      MvPolynomial.eval (fun i ↦ h i + t * z i) f = 0) :
    (fun i ↦ (z i : ℚ)) ∈
      equationFamilyRationalTangentKernel equations h := by
  rw [equationFamilyRationalTangentKernel, LinearMap.mem_ker]
  funext f
  change ∑ i, (MvPolynomial.eval h (MvPolynomial.pderiv i f.1) : ℚ) *
    (z i : ℚ) = 0
  exact_mod_cast
    (eval_starCoefficient_one_eq_zero_of_eval_line_zero
      f.1 h z (hline f.1 f.2))

/-- The rational span of any family of such integral line directions is
contained in the literal tangent kernel. -/
theorem span_intDirections_le_equationFamilyRationalTangentKernel
    {n : ℕ} {I : Type*}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (h : IntVector n) (z : I → IntVector n)
    (hline : ∀ a f, f ∈ equations → ∀ t : ℤ,
      MvPolynomial.eval (fun i ↦ h i + t * z a i) f = 0) :
    Submodule.span ℚ (Set.range fun a i ↦ (z a i : ℚ)) ≤
      equationFamilyRationalTangentKernel equations h := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact intDirection_mem_equationFamilyRationalTangentKernel equations h (z a)
    (fun f hf ↦ hline a f hf)

/-- Rank--nullity for the displayed Jacobian gives the exact dimension of
its tangent kernel. -/
theorem finrank_equationFamilyRationalTangentKernel
    {n : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ))
    (h : IntVector n) :
    Module.finrank ℚ (equationFamilyRationalTangentKernel equations h) =
      n - (equationFamilyRationalJacobianMatrix equations h).rank := by
  have hrankNullity :=
    (equationFamilyRationalJacobianLinearMap equations h).finrank_range_add_finrank_ker
  have hsum :
      (equationFamilyRationalJacobianMatrix equations h).rank +
          Module.finrank ℚ (equationFamilyRationalTangentKernel equations h) = n := by
    simpa [equationFamilyRationalJacobianLinearMap,
      equationFamilyRationalTangentKernel, Matrix.rank] using hrankNullity
  omega

/-- Consequently every rational span of integral line directions has
dimension at most the Jacobian nullity. -/
theorem finrank_span_intDirections_le_jacobian_nullity
    {n : ℕ} {I : Type*}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (h : IntVector n) (z : I → IntVector n)
    (hline : ∀ a f, f ∈ equations → ∀ t : ℤ,
      MvPolynomial.eval (fun i ↦ h i + t * z a i) f = 0) :
    Module.finrank ℚ
        (Submodule.span ℚ (Set.range fun a i ↦ (z a i : ℚ))) ≤
      n - (equationFamilyRationalJacobianMatrix equations h).rank := by
  calc
    Module.finrank ℚ
        (Submodule.span ℚ (Set.range fun a i ↦ (z a i : ℚ))) ≤
        Module.finrank ℚ (equationFamilyRationalTangentKernel equations h) :=
      Submodule.finrank_mono
        (span_intDirections_le_equationFamilyRationalTangentKernel
          equations h z hline)
    _ = n - (equationFamilyRationalJacobianMatrix equations h).rank :=
      finrank_equationFamilyRationalTangentKernel equations h

end

end TranslatedDepthSeven
