import TranslatedDepthSeven.HomogeneousNormalizationMinpolyInternal
import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount

/-!
# Constant directional derivatives of normalization equations

These identities are purely polynomial identities.  A derivation that
annihilates the parameter forms differentiates a normalization equation
only in its additional variable.  No assertion that these equations
generate the source ideal is used or implied.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- The chain rule when the parameter forms are constant for the chosen
derivation. -/
theorem derivation_aeval_option_of_parameter_zero
    {K : Type*} [Field K] {σ τ : Type*}
    (D : Derivation K (MvPolynomial τ K) (MvPolynomial τ K))
    (l : Option σ → MvPolynomial τ K)
    (hl : ∀ i, D (l (some i)) = 0)
    (F : MvPolynomial (Option σ) K) :
    D (aeval l F) = aeval l (pderiv none F) * D (l none) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG => simp only [map_add, hF, hG, add_mul]
  | mul_X F i hF =>
      simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul,
        pderiv_X, map_add, hF]
      cases i with
      | none => simp [Pi.single_apply]; ring
      | some i => simp [Pi.single_apply, hl]; ring

/-- The distinguished partial derivative corresponds to the ordinary
derivative under the polynomial-in-one-variable equivalence. -/
theorem pderiv_none_optionEquivLeft_symm
    {K : Type*} [Field K] {σ : Type*}
    (p : Polynomial (MvPolynomial σ K)) :
    pderiv none ((optionEquivLeft K σ).symm p) =
      (optionEquivLeft K σ).symm p.derivative := by
  classical
  have h (F : MvPolynomial (Option σ) K) :
      (optionEquivLeft K σ) (pderiv none F) =
        ((optionEquivLeft K σ) F).derivative := by
    induction F using MvPolynomial.induction_on with
    | C c => simp [optionEquivLeft_C]
    | add F G hF hG => simp only [map_add, Polynomial.derivative_add, hF, hG]
    | mul_X F i hF =>
        simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
          Polynomial.derivative_mul, pderiv_X, hF]
        cases i with
        | none => simp [optionEquivLeft_X_none]; ring
        | some i => simp [optionEquivLeft_X_some]; ring
  apply (optionEquivLeft K σ).injective
  simpa only [AlgEquiv.apply_symm_apply] using h ((optionEquivLeft K σ).symm p)

/-- A constant-coordinate directional derivative. -/
def constantPolynomialDirectionalDerivative
    {K : Type*} [Field K] {σ : Type*} (v : σ → K) :
    Derivation K (MvPolynomial σ K) (MvPolynomial σ K) :=
  mkDerivation K (fun i ↦ C (v i))

/-- Constant directional derivatives are the corresponding linear
combination of the ordinary partial derivatives. -/
theorem constantPolynomialDirectionalDerivative_eq_sum
    {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (v : σ → K) (f : MvPolynomial σ K) :
    constantPolynomialDirectionalDerivative v f =
      ∑ i, C (v i) * pderiv i f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf, hg, mul_add, Finset.sum_add_distrib]
  | mul_X f j hf =>
      simp only [Derivation.leibniz, smul_eq_mul, hf, pderiv_X,
        mul_add, Finset.sum_add_distrib]
      rw [show constantPolynomialDirectionalDerivative v (X j) = C (v j) by
        exact mkDerivation_X (R := K) (fun i ↦ (C (v i) : MvPolynomial σ K)) j]
      simp only [Pi.single_apply]
      have hsum :
          (∑ i : σ, C (v i) * (f * (if j = i then 1 else 0))) =
            C (v j) * f := by
        simp [mul_ite]
      rw [hsum]
      have hsum' : (∑ i : σ, C (v i) * (X j * pderiv i f)) =
          X j * ∑ i : σ, C (v i) * pderiv i f := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum']
      ring

end

end TranslatedDepthSeven
