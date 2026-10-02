import CubicTenVariables.FiniteFiberCauchy
import CubicTenVariables.ResidueFiberQuadraticMoment
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The residue-weighted quadratic inequality used in the L1 onion
argument. Cauchy--Schwarz is applied to residue classes before the
summed second-moment estimate. The final Hessian-weighted endpoint has
no point-count, anisotropy, parity or literature premise. -/

noncomputable section
namespace CubicTenVariables.ResidueWeightedQuadraticGauss
open MvPolynomial HessianTheorem11
open scoped BigOperators

/-- Arbitrary complex weights depending only on reduction modulo d.
The right-hand kernel is the actual integral Hessian reduced modulo c/d. -/
theorem norm_weighted_sum_sq_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c)
    (a : (ZMod c)ˣ) (h : Fin n → ℤ) (w : (Fin n → ZMod d) → ℂ) :
    ‖∑ x : Fin n → ZMod c,
      w (fun i => ZMod.castHom hdc (ZMod d) (x i)) *
        ZMod.stdAddChar ((a : ZMod c) *
          ∑ i, (h i : ZMod c) * eval₂ (Int.castRingHom (ZMod c)) x (pderiv i F))‖^2 ≤
      (∑ b, ‖w b‖^2) * (c : ℝ)^n *
        Nat.card {t : Fin n → ZMod (c/d) //
          ((hessian F h).map (Int.castRingHom (ZMod (c/d)))).mulVec t = 0} := by
  classical
  have hcs := FiniteFiberCauchy.norm_weighted_sum_sq_le
    (fun x : Fin n → ZMod c => fun i => ZMod.castHom hdc (ZMod d) (x i)) w
    (fun x => ZMod.stdAddChar ((a : ZMod c) *
      ∑ i, (h i : ZMod c) * eval₂ (Int.castRingHom (ZMod c)) x (pderiv i F)))
  have hmoment := ResidueFiberQuadraticMoment.sum_norm_sq_le F hF c d hdc a h
  exact hcs.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hmoment (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The literal finite Hessian kernel at a residue center. -/
def kernelCard {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (d : ℕ)
    (b : Fin n → ZMod d) : ℕ :=
  Nat.card {z : Fin n → ZMod d //
    (hessian (map (Int.castRingHom (ZMod d)) F) b).mulVec z = 0}

/-- The actual square-root Hessian weights in the unrestricted quadratic
factor of the manuscript's onion argument. No estimate of their total
mass is supplied or claimed here. -/
theorem norm_hessian_weighted_sum_sq_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c)
    (a : (ZMod c)ˣ) (h : Fin n → ℤ) :
    ‖∑ x : Fin n → ZMod c,
      (Real.sqrt (kernelCard F d (fun i => ZMod.castHom hdc (ZMod d) (x i)) : ℝ) : ℂ) *
        ZMod.stdAddChar ((a : ZMod c) *
          ∑ i, (h i : ZMod c) * eval₂ (Int.castRingHom (ZMod c)) x (pderiv i F))‖^2 ≤
      (∑ b : Fin n → ZMod d, (kernelCard F d b : ℝ)) * (c : ℝ)^n *
        Nat.card {t : Fin n → ZMod (c/d) //
          ((hessian F h).map (Int.castRingHom (ZMod (c/d)))).mulVec t = 0} := by
  have hh := norm_weighted_sum_sq_le F hF c d hdc a h
    (fun b => (Real.sqrt (kernelCard F d b : ℝ) : ℂ))
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg _)] using hh

end CubicTenVariables.ResidueWeightedQuadraticGauss
