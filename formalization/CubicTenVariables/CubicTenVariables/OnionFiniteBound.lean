import CubicTenVariables.ResidueWeightedQuadraticGauss
import CubicTenVariables.WeightedHessianRootCRT

/-! The finite part of the onion estimate, before geometric mass bounds
or Poisson summation. The partial polynomial-zero condition is retained
in the first CRT factor only. The bound uses actual finite root and
kernel masses, rather than assuming an estimate for either of them. -/

noncomputable section
namespace CubicTenVariables.OnionFiniteBound
open MvPolynomial HessianTheorem11 CRTCharacters WeightedCRTAdapters
open WeightedHessianRootCRT HessianKernelCRT
open scoped BigOperators

/-- The unrestricted weighted quadratic character factor, expressed in
the same definitions used by the exact CRT factorization. -/
theorem norm_characterMass_sq_le {v : ℕ}
    (F : MvPolynomial (Fin v) ℤ) (hF : F.IsHomogeneous 3)
    (c d : ℕ) [NeZero c] [NeZero d] (hd : d ∣ c)
    (a : (ZMod c)ˣ) (h : Fin v → ℤ) :
    ‖characterMass F c d hd (a : ZMod c) h‖^2 ≤
      (∑ b : Fin v → ZMod d, (hessianKernelCard F d b : ℝ)) * (c : ℝ)^v *
        kernelCard (hessian F h) (c/d) := by
  simpa only [characterMass, kernelWeight, directionalPhase,
    ResidueWeightedQuadraticGauss.kernelCard, hessianKernelCard, kernelCard] using
      ResidueWeightedQuadraticGauss.norm_hessian_weighted_sum_sq_le F hF c d hd a h

/-- The complete finite character bound required inside the L1 onion
argument. The two geometric masses are left as their actual finite sums;
no assumed point-count estimate or literature premise occurs. -/
theorem norm_partialRootCharacterMass_sq_le {v m n d : ℕ}
    [NeZero m] [NeZero n] [NeZero d]
    (F : MvPolynomial (Fin v) ℤ) (hF : F.IsHomogeneous 3)
    (hc : m.Coprime n) (hd : d ∣ n)
    (a : (ZMod (m*n))ˣ) (h : Fin v → ℤ) :
    ‖partialRootCharacterMass F (m*n) (m*d) m
      (Nat.mul_dvd_mul (dvd_refl m) hd) (dvd_mul_right m n) (a : ZMod (m*n)) h‖^2 ≤
      (rootMass F m)^2 *
        (∑ b : Fin v → ZMod d, (hessianKernelCard F d b : ℝ)) *
        (n : ℝ)^v * kernelCard (hessian F h) (n/d) := by
  let b : (ZMod n)ˣ := rightTwist hc * (unitEquiv hc a).2
  have hr := norm_characterMass_sq_le F hF n d hd b h
  have hb : (b : ZMod n) = (rightTwist hc : ZMod n) *
      rightProjection hc (a : ZMod (m*n)) := by
    simp only [b, Units.val_mul, unitEquiv_snd_coe]
  rw [hb] at hr
  have hl := norm_rootCharacterMass_le_rootMass F
    ((leftTwist hc : ZMod m) * leftProjection hc (a : ZMod (m*n))) h
  rw [partialRootCharacterMass_crt F hc hd, norm_mul, mul_pow]
  have hprod := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hl 2) hr
    (sq_nonneg _) (sq_nonneg _)
  simpa only [mul_assoc] using hprod

end CubicTenVariables.OnionFiniteBound
