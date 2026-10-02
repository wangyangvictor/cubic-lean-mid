import HessianTheorem11.LocalCubicNormalForm
import HessianTheorem11.TextbookFormalGeometry

/-! Specialization of the general formal implicit-function theorem to the
actual normal-form polynomial, followed by the proved Schur coefficient
calculation. No bespoke normal-form or Clifford conclusion is an input. -/

noncomputable section
namespace HessianTheorem11.LocalCubicNormalForm
open MvPolynomial Matrix

variable {K : Type*} [Field K]

theorem polynomial_at_base {m q : ℕ} (D : Data (K := K) m q) :
    eval (basePoint m q) (polynomial D) = 0 := by
  have hQA : constantCoeff D.QA = 0 :=
    D.QA_homogeneous.coeff_eq_zero (by simp)
  have hQ0 : constantCoeff D.Q0 = 0 :=
    D.Q0_homogeneous.coeff_eq_zero (by simp)
  have hR : constantCoeff D.R = 0 :=
    D.R_homogeneous.coeff_eq_zero (by simp)
  simp only [polynomial, map_add, map_sum, map_mul, map_pow, eval_X, eval_C,
    eval_base_rename_a, eval_base_rename_b, eval_base_rename_residual,
    eval_zero, hQA, hQ0, hR]
  simp [basePoint, aIndex, bIndex, xIndex, zIndex]

theorem z_partial_at_base {m q : ℕ} (D : Data (K := K) m q) :
    eval (basePoint m q) (pderiv (zIndex m q) (polynomial D)) = 1 := by
  have hQA : constantCoeff D.QA = 0 :=
    D.QA_homogeneous.coeff_eq_zero (by simp)
  have hR : constantCoeff (pderiv (Sum.inr ()) D.R) = 0 :=
    D.R_homogeneous.pderiv.coeff_eq_zero (by simp)
  rw [z_partial]
  simp only [map_add, map_sum, map_mul, map_pow, eval_X, eval_C,
    eval_base_rename_a, eval_base_rename_residual, eval_zero, hQA, hR]
  simp [basePoint, aIndex, bIndex, xIndex, zIndex]

theorem curve_update_z {m q : ℕ} (v : Fin q → K) (z : PowerSeries K) :
    Function.update (curve (m := m) v 0) (zIndex m q) z = curve v z := by
  classical
  funext i
  rcases i with i | (i | i)
  · simp [curve, zIndex]
  · simp [curve, zIndex]
  · fin_cases i <;> simp [curve, zIndex]

theorem curve_constant_coordinates {m q : ℕ} (v : Fin q → K) :
    (fun i => PowerSeries.constantCoeff (curve (m := m) v 0 i)) = basePoint m q := by
  funext i
  rcases i with i | (i | i)
  · simp [curve, basePoint]
  · simp [curve, basePoint]
  · fin_cases i <;> simp [curve, basePoint]

section FormalInput
variable {k : Type} [Field k]

/-- Only the universal simple-root lifting theorem is supplied. Both the
base equation and the nonzero partial derivative are proved for the actual
normal-form polynomial. -/
theorem exists_formal_root (FI : FormalImplicitFunctionInput k)
    {m q : ℕ} (D : Data (K := k) m q) (v : Fin q → k) :
    ∃ z : PowerSeries k, PowerSeries.coeff 0 z = 0 ∧
      seriesEval v z (polynomial D) = 0 := by
  classical
  obtain ⟨z, hz, hroot⟩ := FI.lift (polynomial D) (zIndex m q) (curve v 0)
    (by simp [curve, zIndex])
    (by rw [curve_constant_coordinates]; exact polynomial_at_base D)
    (by rw [curve_constant_coordinates, z_partial_at_base D]; exact one_ne_zero)
  refine ⟨z, ?_, ?_⟩
  · simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hz
  · rw [curve_update_z] at hroot
    exact hroot

/-- The full first- and second-order expansion of the lifted root. -/
theorem exists_formal_root_coefficients (FI : FormalImplicitFunctionInput k)
    {m q : ℕ} (D : Data (K := k) m q) (v : Fin q → k) :
    ∃ z : PowerSeries k, PowerSeries.coeff 0 z = 0 ∧
      seriesEval v z (polynomial D) = 0 ∧
      PowerSeries.coeff 1 z = 0 ∧ PowerSeries.coeff 2 z = -eval v D.Q0 := by
  obtain ⟨z, hz, hroot⟩ := exists_formal_root FI D v
  exact ⟨z, hz, hroot, formal_root_first_two_coefficients D v z hz hroot⟩

end FormalInput

/-- The source's normal line has actual first kernel-block coefficient
`Hessian QA = 2P`. -/
theorem aBlock_normalLine_coeff_zero {m q : ℕ} (D : Data (K := K) m q) :
    SchurSecondOrder.matrixCoeff 0 (aBlock D 0 PowerSeries.X) = 0 := by
  rw [aBlock_coefficient]
  simp

theorem aBlock_normalLine_coeff_one {m q : ℕ} (D : Data (K := K) m q) :
    SchurSecondOrder.matrixCoeff 1 (aBlock D 0 PowerSeries.X) = quadraticMatrix D.QA := by
  rw [aBlock_coefficient]
  simp

theorem crossBlock_normalLine_coeff_zero {m q : ℕ} (D : Data (K := K) m q) :
    SchurSecondOrder.matrixCoeff 0 (crossBlock D 0 PowerSeries.X) = 0 :=
  crossBlock_coeff_zero D 0 PowerSeries.X (by simp)

theorem normalBlock_normalLine_coeff_zero {m q : ℕ} (D : Data (K := K) m q) :
    SchurSecondOrder.matrixCoeff 0 (normalBlock D 0 PowerSeries.X) =
      SchurSecondOrder.normalInverse (quadraticMatrix D.Q0) 2 :=
  normalBlock_coeff_zero D 0 PowerSeries.X (by simp)

theorem polynomial_normalLine_coeff_zero {m q : ℕ} (D : Data (K := K) m q) :
    PowerSeries.coeff 0 (seriesEval 0 PowerSeries.X (polynomial D)) = 0 := by
  rw [polynomial_on_curve, map_add, map_add,
    residualSeries_coeff_below D 0 PowerSeries.X (by simp) 0 (by decide)]
  simp [PowerSeries.coeff_X_pow]

theorem polynomial_normalLine_coeff_one {m q : ℕ} (D : Data (K := K) m q) :
    PowerSeries.coeff 1 (seriesEval 0 PowerSeries.X (polynomial D)) = 1 := by
  rw [polynomial_on_curve, map_add, map_add,
    residualSeries_coeff_below D 0 PowerSeries.X (by simp) 1 (by decide)]
  simp [PowerSeries.coeff_X_pow]

/-- Commutation of formal partials for the actual sum-coordinate index. -/
theorem partials_commute_general {σ : Type*} (F : MvPolynomial σ K) (i j : σ) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p l hp =>
    by_cases hij : i = j
    · subst j; rfl
    · by_cases hil : l = i <;> by_cases hjl : l = j <;>
        simp_all [pderiv_X, Pi.single_apply, eq_comm] <;> ring

theorem hessianSeries_symmetric {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) :
    (hessianSeries D v z).transpose = hessianSeries D v z := by
  apply Matrix.ext
  intro i j
  exact congrArg (seriesEval v z) (partials_commute_general (polynomial D) i j)

/-- All matrix identities now follow from the actual normal-form polynomial
and genuine formal roots. The only remaining Schur premise is its vanishing,
which is proved separately from the geometric rank bound. -/
theorem clifford_relations_of_formal_roots [CharZero K]
    {m q : ℕ} (D : Data (K := K) m q)
    (hdet : (quadraticMatrix D.Q0).det ≠ 0)
    (Z : (Fin q → K) → PowerSeries K)
    (hZ : ∀ v, PowerSeries.coeff 0 (Z v) = 0)
    (hroot : ∀ v, seriesEval v (Z v) (polynomial D) = 0)
    (J : (Fin q → K) → Matrix (Fin q ⊕ Fin 2) (Fin q ⊕ Fin 2) (PowerSeries K))
    (hInv : ∀ v, normalBlock D v (Z v) * J v = 1)
    (hSchur : ∀ v, aBlock D v (Z v) -
      crossBlock D v (Z v) * J v * (crossBlock D v (Z v)).transpose = 0) :
    ∀ i j,
      quadraticMatrix (D.Q i) * (quadraticMatrix D.Q0)⁻¹ * quadraticMatrix (D.Q j) +
        quadraticMatrix (D.Q j) * (quadraticMatrix D.Q0)⁻¹ * quadraticMatrix (D.Q i) =
      (-2 * (((2 : K)⁻¹ • quadraticMatrix D.QA) i j)) • quadraticMatrix D.Q0 := by
  apply SchurSecondOrder.clifford_relations_of_schur_inverse
    ((2 : K)⁻¹ • quadraticMatrix D.QA) (fun i => quadraticMatrix (D.Q i))
    (quadraticMatrix D.Q0) (quadraticMatrix D.Q0)⁻¹ (2 : K)⁻¹ 2
    (by apply inv_mul_cancel₀; norm_num)
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet))
    (fun i => quadraticMatrix_symmetric (D.Q i)) (quadraticMatrix_symmetric D.Q0)
    (by rw [Matrix.transpose_nonsing_inv, quadraticMatrix_symmetric])
    (fun v => aBlock D v (Z v)) (fun v => crossBlock D v (Z v))
    (fun v => normalBlock D v (Z v)) J hInv
    (fun v => normalBlock_coeff_zero D v (Z v) (hZ v)) hSchur
    (fun v => crossBlock_coeff_zero D v (Z v) (hZ v))
  · intro v
    refine ⟨D.abz.mulVec v, ?_⟩
    exact crossBlock_coeff_one D v (Z v)
      (formal_root_first_two_coefficients D v (Z v) (hZ v) (hroot v)).1
  · intro v
    exact aBlock_coeff_two D v (Z v)
      (formal_root_first_two_coefficients D v (Z v) (hZ v) (hroot v)).2

end HessianTheorem11.LocalCubicNormalForm
