import CubicTenVariables.PrimeSumAdapter
import CubicTenVariables.QuadraticGaussBound

/-! Exact character scaling and finite orthogonality for the original
integer representatives. No primality or analytic bound is assumed. -/

noncomputable section
namespace CubicTenVariables.LiftingCharacters
open scoped BigOperators

theorem residueExponential_add (q : ℕ) (b c : ℤ) :
    residueExponential q (b+c) = residueExponential q b * residueExponential q c := by
  simp only [residueExponential, Int.cast_add, mul_add, add_div, Complex.exp_add]

theorem residueExponential_eq_of_cast_eq (q : ℕ) [NeZero q] {b c : ℤ}
    (h : (b : ZMod q) = (c : ZMod q)) :
    residueExponential q b = residueExponential q c := by
  rw [PrimeSumAdapter.residueExponential_eq_stdAddChar,
    PrimeSumAdapter.residueExponential_eq_stdAddChar, h]

/-- The step M cancels from the denominator A*M, with the original
positive 2πi convention and arbitrary integer phase, including negatives. -/
theorem residueExponential_mul_modulus (A M : ℕ) [NeZero M] (b : ℤ) :
    residueExponential (A*M) ((M : ℤ)*b) = residueExponential A b := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  unfold residueExponential
  congr 1
  push_cast
  field_simp

theorem sum_scalar_phase (A : ℕ) [NeZero A] (b : ℤ) :
    (∑ e : Fin A, residueExponential A ((e.val : ℤ)*b)) =
      if (A : ℤ) ∣ b then (A : ℂ) else 0 := by
  classical
  calc
    _ = ∑ e : ZMod A, ZMod.stdAddChar (e*(b : ZMod A)) := by
      apply Fintype.sum_equiv (PrimeSumAdapter.finResidueEquiv A)
      intro e
      rw [PrimeSumAdapter.residueExponential_eq_stdAddChar]
      simp [PrimeSumAdapter.finResidueEquiv_apply]
    _ = _ := by
      rw [AddChar.sum_mulShift (b : ZMod A) (ZMod.isPrimitive_stdAddChar A)]
      simp [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.card]

theorem sum_vector_phase (A n : ℕ) [NeZero A] (b : Fin n → ℤ) :
    (∑ h : Fin n → Fin A,
      residueExponential A (∑ i, (h i).val * b i)) =
      if ∀ i, (A : ℤ) ∣ b i then (A : ℂ)^n else 0 := by
  classical
  calc
    _ = ∑ h : Fin n → ZMod A,
        ZMod.stdAddChar (dotProduct h (fun i => (b i : ZMod A))) := by
      apply Fintype.sum_equiv (PrimeSumAdapter.vectorResidueEquiv A n)
      intro h
      rw [PrimeSumAdapter.residueExponential_eq_stdAddChar]
      simp [PrimeSumAdapter.vectorResidueEquiv_apply, dotProduct]
    _ = _ := by
      rw [QuadraticGaussBound.sum_linear_phase]
      simp only [funext_iff, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Scalar and vector orthogonality together, before applying them to F
and its actual gradient. The factor A^(n+1) includes both lift variables. -/
theorem sum_scalar_vector_phase (A n : ℕ) [NeZero A] (f : ℤ) (b : Fin n → ℤ) :
    (∑ e : Fin A, ∑ h : Fin n → Fin A,
      residueExponential A ((e.val : ℤ)*f + ∑ i, (h i).val*b i)) =
      if (A : ℤ) ∣ f ∧ ∀ i, (A : ℤ) ∣ b i then (A : ℂ)^(n+1) else 0 := by
  classical
  simp_rw [residueExponential_add, ← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_scalar_phase, sum_vector_phase]
  split_ifs <;> simp_all [pow_succ, mul_comm]

end CubicTenVariables.LiftingCharacters
