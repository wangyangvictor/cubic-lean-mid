import CubicTenVariables.HessianResidueKernel
import CubicTenVariables.SmithProfileLowExponent
import CubicTenVariables.QuadraticTerminalBound

/-! The actual attained terminal maximum satisfies the full low-branch
Smith-profile bound, using one integral Hessian diagonal and its valuations
at the fixed exponent a. Even primes and the level-zero case are included.
-/

noncomputable section
namespace CubicTenVariables.TerminalLowBound
open MvPolynomial HessianTheorem11 TerminalCubicSum PrimePowerKernelProfile
open SmithProfileNumerics SmithProfileMultiplicity
open scoped BigOperators

/-- The actual kernel-root estimate is evaluated using the same integral
Hessian diagonal chosen before the prime and both exponents. -/
theorem terminalMax_primePower_le_sqrt {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (y : Fin n → ℤ) (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) [NeZero p] (hp : p.Prime) (a t : ℕ) (hta : t ≤ a)
    (A : ℤ) (hA : ((p^a : ℕ) : ℤ) ∣ A) :
    terminalMax (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
      (A : ZMod (p^t)) (fun i => (y i : ZMod (p^t))) ≤
      Real.sqrt ((p : ℝ) ^ (n*t + ∑ i, min (truncatedValuation p a (d i)) t)) := by
  have hdiv : ((p^t : ℕ) : ℤ) ∣ A := by
    apply dvd_trans ?_ hA
    exact_mod_cast (pow_dvd_pow p hta)
  have hzero : (A : ZMod (p^t)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd A (p^t)).mpr hdiv
  rw [hzero]
  have hb := QuadraticTerminalBound.terminalMax_zero_le_sqrt (p^t) n
    (map (Int.castRingHom (ZMod (p^t))) F) (hF.map _) (fun i => (y i : ZMod (p^t)))
  rw [HessianResidueKernel.card_hessian_primePower_kernel_truncated F y U V d hD p hp a t hta] at hb
  convert hb using 1
  congr 1
  push_cast
  rw [← pow_mul, ← pow_add, Nat.mul_comm t n]

/-- The manuscript's complete low-branch terminal Smith bound, including
p=2, for the actual finite maximum over units and all linear frequencies. -/
theorem terminalMax_primePower_le_profile {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (y : Fin n → ℤ) (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) [NeZero p] (hp : p.Prime) (a t : ℕ) (hta : t ≤ a)
    (A : ℤ) (hA : ((p^a : ℕ) : ℤ) ∣ A) :
    terminalMax (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
      (A : ZMod (p^t)) (fun i => (y i : ZMod (p^t))) ≤
      Real.rpow (p : ℝ) (((n*t : ℕ) : ℝ) - ∑ i ∈ Finset.range a,
        (penaltyWeight a t i : ℝ) *
          (profile (fun ν => truncatedValuation p a (d ν)) i : ℝ)) := by
  have hb := terminalMax_primePower_le_sqrt F hF y U V d hD p hp a t hta A hA
  rwa [SmithProfileLowExponent.low_factor_eq_rpow (p : ℝ)
    (by exact_mod_cast hp.pos) _ hta] at hb

end CubicTenVariables.TerminalLowBound
