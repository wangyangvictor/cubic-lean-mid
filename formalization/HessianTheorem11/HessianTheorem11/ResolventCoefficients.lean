import HessianTheorem11.PencilSchurVanishing
import HessianTheorem11.SchurSecondOrder

/-! Every coefficient of the inverse of a matrix linear pencil, and the
resulting polynomial identities of a vanishing formal resolvent. -/
noncomputable section
namespace HessianTheorem11.ResolventCoefficients
open Matrix PowerSeries SchurSecondOrder PencilSchurVanishing
variable {K α β γ : Type*} [Field K] [Fintype α] [Fintype β] [Fintype γ]

theorem coeff_left_constant (n : ℕ) (A : Matrix α β K)
    (J : Matrix β γ (PowerSeries K)) :
    matrixCoeff n (A.map C * J) = A * matrixCoeff n J := by
  ext i j
  simp [matrixCoeff, Matrix.mul_apply, map_sum, coeff_C_mul]

theorem coeff_right_constant (n : ℕ) (J : Matrix α β (PowerSeries K))
    (A : Matrix β γ K) :
    matrixCoeff n (J * A.map C) = matrixCoeff n J * A := by
  ext i j
  simp [matrixCoeff, Matrix.mul_apply, map_sum, coeff_mul_C]

theorem coeff_X_smul_succ (n : ℕ) (J : Matrix α β (PowerSeries K)) :
    matrixCoeff (n+1) ((X : PowerSeries K) • J) = matrixCoeff n J := by
  ext i j
  change coeff (n+1) (X * J i j) = coeff n (J i j)
  simpa only [pow_one] using coeff_X_pow_mul (J i j) 1 n

theorem coeff_one_succ [DecidableEq α] (n : ℕ) :
    matrixCoeff (n+1) (1 : Matrix α α (PowerSeries K)) = 0 := by
  ext i j
  by_cases hij : i=j <;> simp [matrixCoeff, Matrix.one_apply, hij, PowerSeries.coeff_one]

theorem coeff_add (n : ℕ) (A B : Matrix α β (PowerSeries K)) :
    matrixCoeff n (A+B) = matrixCoeff n A + matrixCoeff n B := by
  ext i j
  simp [matrixCoeff]

theorem inverse_coeff [DecidableEq α]
    (B Q R : Matrix α α K) (hRB : R * B = 1)
    (J : Matrix α α (PowerSeries K)) (hJ : seriesPencil B Q * J = 1) (n : ℕ) :
    matrixCoeff n J = (-(R*Q))^n * R := by
  have hrec (n : ℕ) : matrixCoeff (n+1) J = -(R*Q) * matrixCoeff n J := by
    have h := congrArg (matrixCoeff (n+1)) hJ
    rw [seriesPencil, Matrix.add_mul, Matrix.smul_mul, coeff_add,
      coeff_X_smul_succ, coeff_left_constant, coeff_left_constant, coeff_one_succ] at h
    have h' := congrArg (fun A => R*A) h
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hRB, Matrix.one_mul,
      Matrix.mul_zero] at h'
    exact (eq_neg_iff_add_eq_zero.mpr h').trans (by rw [Matrix.neg_mul])
  induction n with
  | zero =>
    simp only [pow_zero, Matrix.one_mul]
    apply matrixCoeff_zero_inverse_of_left_inverse (seriesPencil B Q) J R hJ
    have h₀ : matrixCoeff 0 (seriesPencil B Q) = B := by
      ext i j
      simp [matrixCoeff, seriesPencil, coeff_zero_eq_constantCoeff]
    rw [h₀]
    exact hRB
  | succ n ih =>
    rw [hrec, ih, pow_succ', Matrix.mul_assoc]

theorem vanishing_resolvent_coefficients [DecidableEq α]
    (B Q R : Matrix α α K) (hRB : R*B=1)
    (E : Matrix β α K) (F : Matrix α γ K)
    (J : Matrix α α (PowerSeries K)) (hJ : seriesPencil B Q * J = 1)
    (hz : E.map C * J * F.map C = 0) (n : ℕ) :
    E * (-(R*Q))^n * R * F = 0 := by
  have h := congrArg (matrixCoeff n) hz
  rw [coeff_right_constant, coeff_left_constant, inverse_coeff B Q R hRB J hJ,
    matrixCoeff_zero] at h
  simpa only [Matrix.mul_assoc] using h

end HessianTheorem11.ResolventCoefficients
