import CubicTenVariables.ProperHomogeneousNormalization
import TranslatedDepthSeven.LinearPolynomialComplementDirectionsInternal
import HessianTheorem11.PolynomialRestriction
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Actual integral invertible coordinates extending a homogeneous linear
normalization. These are coordinates on the original ambient affine space. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
noncomputable section
namespace CubicTenVariables.IntegralNormalizationCoordinates
open MvPolynomial TranslatedDepthSeven Module HessianTheorem11 PolynomialRestriction
open scoped BigOperators

variable {n : ℕ}

/-- The coefficient vector of a homogeneous linear polynomial. -/
def coefficients : homogeneousSubmodule (Fin n) ℚ 1 →ₗ[ℚ] (Fin n → ℚ) where
  toFun f j := (pderiv j (f : MvPolynomial (Fin n) ℚ)).coeff 0
  map_add' f g := by ext j; simp
  map_smul' a f := by ext j; simp

/-- Euler's degree-one identity reconstructs the original linear form. -/
theorem sum_coefficients (f : homogeneousSubmodule (Fin n) ℚ 1) :
    (∑ j, C (coefficients f j) * X j) = (f : MvPolynomial (Fin n) ℚ) := by
  have he := f.property.sum_X_mul_pderiv
  have hd (j : Fin n) : pderiv j (f : MvPolynomial (Fin n) ℚ) =
      C ((pderiv j (f : MvPolynomial (Fin n) ℚ)).coeff 0) :=
    eq_C_coeff_zero_of_isHomogeneous_zero (by simpa using f.property.pderiv (i := j))
  calc
    _ = ∑ j, X j * pderiv j (f : MvPolynomial (Fin n) ℚ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hd j]
      simp [coefficients, mul_comm]
    _ = _ := by simpa using he

theorem coefficients_injective : Function.Injective (@coefficients n) := by
  intro f g h
  apply Subtype.ext
  rw [← sum_coefficients f, ← sum_coefficients g, h]

/-- Independence already holds before passing to the quotient. -/
theorem forms_independent (I : Ideal (MvPolynomial (Fin n) ℚ))
    (D : HomogeneousLinearNormalizationData I) :
    LinearIndependent ℚ (fun i : Fin D.parameterCount =>
      (⟨D.forms i, D.forms_isHomogeneous i⟩ : homogeneousSubmodule (Fin n) ℚ 1)) := by
  have h : LinearIndependent ℚ (fun i : Fin D.parameterCount => D.hom (X i)) :=
    (MvPolynomial.linearIndependent_X (Fin D.parameterCount) ℚ).map'
      D.hom.toLinearMap (LinearMap.ker_eq_bot.mpr D.hom_injective)
  apply LinearIndependent.of_comp
    ((Ideal.Quotient.mkₐ ℚ I).toLinearMap.comp (homogeneousSubmodule (Fin n) ℚ 1).subtype)
  simpa [Function.comp_def, HomogeneousLinearNormalizationData.hom] using h

/-- A single positive matrix denominator clears every row. -/
theorem exists_integral_matrix (I : Ideal (MvPolynomial (Fin n) ℚ))
    (D : HomogeneousLinearNormalizationData I) :
    ∃ (A : Matrix (Fin n) (Fin n) ℤ) (β : Fin D.parameterCount ↪ Fin n)
      (L : ℕ), 0 < L ∧
      (A.map (Int.castRingHom ℚ)).det ≠ 0 ∧
      ∀ i, linearForms (A.map (Int.castRingHom ℚ)) (β i) = C (L : ℚ) * D.forms i := by
  classical
  let V := homogeneousSubmodule (Fin n) ℚ 1
  have hdim : finrank ℚ V = n := by
    simpa [V] using finrank_mvPolynomial_homogeneousSubmodule_fin ℚ n 1
  let u : Fin D.parameterCount → V := fun i => ⟨D.forms i,D.forms_isHomogeneous i⟩
  have hu : LinearIndependent ℚ u := forms_independent I D
  have hd : D.parameterCount ≤ n := by
    simpa only [Fintype.card_fin,hdim] using hu.fintype_card_le_finrank
  obtain ⟨b₀,hb₀⟩ := exists_basis_finSum_extending_independent_family u hu
  let e : (Fin D.parameterCount ⊕ Fin (finrank ℚ V - D.parameterCount)) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (by rw [hdim]; omega))
  let b := b₀.reindex e
  let β : Fin D.parameterCount ↪ Fin n :=
    ⟨fun i => e (Sum.inl i), e.injective.comp Sum.inl_injective⟩
  let B : Matrix (Fin n) (Fin n) ℚ := fun i => coefficients (b i)
  have hforms (i : Fin n) : linearForms B i = (b i : MvPolynomial (Fin n) ℚ) :=
    sum_coefficients (b i)
  have hBi : LinearIndependent ℚ B.row :=
    b.linearIndependent.map' coefficients (LinearMap.ker_eq_bot.mpr coefficients_injective)
  have hBdet : B.det ≠ 0 :=
    isUnit_iff_ne_zero.mp (((Matrix.isUnit_iff_isUnit_det B).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hBi)))
  have hL : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.den_ne_zero
  have hnum : B.num.map (Int.castRingHom ℚ) = (B.den : ℚ) • B := by
    ext i j
    exact (div_eq_iff hL).mp (B.num_div_den i j) |>.trans (mul_comm _ _)
  refine ⟨B.num,β,B.den,Nat.pos_of_ne_zero B.den_ne_zero,?_,?_⟩
  · rw [hnum,Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hL) hBdet
  · intro i
    rw [hnum]
    have hlin : linearForms ((B.den : ℚ) • B) (β i) =
        C (B.den : ℚ) * linearForms B (β i) := by
      simp only [linearForms, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
    rw [hlin,hforms]
    have hb : b (β i) = u i := by simpa [b,β] using hb₀ i
    rw [hb]

end CubicTenVariables.IntegralNormalizationCoordinates
