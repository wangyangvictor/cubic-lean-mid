import CubicTenVariables.PrimeFrogZeroMass
import CubicTenVariables.HessianKernelCRT
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighted Cauchy--Schwarz for the literal prime frog mass

The square-root Hessian weight is computed from the actual modular kernel.
Both source gcd factors may independently be omitted. This finite inequality
needs no homogeneity, anisotropy or counting hypothesis.
-/

noncomputable section
namespace CubicTenVariables.PrimeFrogOneMass
open MvPolynomial PrimeFrogZeroMass SquarefreeResidueFactors HessianKernelCRT
open scoped BigOperators

/-- Weighted Cauchy--Schwarz for arbitrary finite nonnegative real weights. -/
theorem weighted_cauchy {α : Type*} (S : Finset α) (w a : α → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (ha : ∀ x ∈ S, 0 ≤ a x) :
    (∑ x ∈ S, w x * Real.sqrt (a x)) ^ 2 ≤
      (∑ x ∈ S, w x) * ∑ x ∈ S, w x * a x := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul S hw
    (fun x hx => mul_nonneg (hw x hx) (ha x hx))
  intro x hx
  rw [mul_pow, Real.sq_sqrt (ha x hx)]
  ring

/-- The literal gcd weight with the source's two independent omission switches. -/
def optionalRootWeight {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (p : ℕ)
    (x : Fin n → ZMod p) (includeGradient includeCoordinates : Bool) : ℕ :=
  (if includeGradient then
    vectorGcd p (fun i => eval (integerLift p x) (pderiv i F)) else 1) *
  (if includeCoordinates then vectorGcd p (integerLift p x) else 1)

@[simp] theorem optionalRootWeight_true_true {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) (x : Fin n → ZMod p) :
    optionalRootWeight F p x true true = rootWeight F p x := by
  simp [optionalRootWeight, rootWeight]

/-- The actual root-filtered square-root mass, not a supplied numerical mass. -/
def oneMass {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [NeZero p]
    (includeGradient includeCoordinates : Bool) : ℝ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod p =>
    eval₂ (Int.castRingHom (ZMod p)) x F = 0),
    (optionalRootWeight F p x includeGradient includeCoordinates : ℝ) *
      Real.sqrt (hessianKernelCard F p x : ℝ)

theorem oneMass_nonneg {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [NeZero p] (includeGradient includeCoordinates : Bool) :
    0 ≤ oneMass F p includeGradient includeCoordinates := by
  classical
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))

/-- The exact finite Cauchy bound between the actual j=0, j=1 and j=2 masses. -/
theorem oneMass_sq_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [NeZero p] (includeGradient includeCoordinates : Bool) :
    (oneMass F p includeGradient includeCoordinates)^2 ≤
      ((∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod p =>
        eval₂ (Int.castRingHom (ZMod p)) x F = 0),
        optionalRootWeight F p x includeGradient includeCoordinates : ℕ) : ℝ) *
      ((∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod p =>
        eval₂ (Int.castRingHom (ZMod p)) x F = 0),
        optionalRootWeight F p x includeGradient includeCoordinates *
          hessianKernelCard F p x : ℕ) : ℝ) := by
  classical
  simpa only [oneMass, Nat.cast_sum, Nat.cast_mul] using
    weighted_cauchy (Finset.univ.filter (fun x : Fin n → ZMod p =>
      eval₂ (Int.castRingHom (ZMod p)) x F = 0))
      (fun x => (optionalRootWeight F p x includeGradient includeCoordinates : ℝ))
      (fun x => (hessianKernelCard F p x : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)

/-- The source's real exponent 1/2 agrees exactly with the square-root mass. -/
theorem oneMass_eq_rpow {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [NeZero p] (includeGradient includeCoordinates : Bool) :
    oneMass F p includeGradient includeCoordinates =
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod p =>
        eval₂ (Int.castRingHom (ZMod p)) x F = 0),
        (hessianKernelCard F p x : ℝ) ^ ((1 : ℝ) / 2) *
          (optionalRootWeight F p x includeGradient includeCoordinates : ℝ) := by
  classical
  simp only [oneMass, Real.sqrt_eq_rpow, mul_comm]

/-- A squared exponent-21 estimate implies the source exponent 21/2;
the same constant may be kept after increasing it to at least one. -/
theorem le_mul_rpow_of_sq_le {m C p : ℝ} (hC : 1 ≤ C) (hp : 0 ≤ p)
    (hm : m^2 ≤ C*p^21) : m ≤ C * p^((21 : ℝ)/2) := by
  have he : (p^((21 : ℝ)/2))^2 = p^21 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp]
    norm_num
  have hpow : 0 ≤ p^21 := pow_nonneg hp _
  have hC0 : 0 ≤ C := by linarith
  have hCC : C ≤ C^2 := by nlinarith
  have hb : m^2 ≤ (C*p^((21 : ℝ)/2))^2 := by
    rw [mul_pow, he]
    exact hm.trans (mul_le_mul_of_nonneg_right hCC hpow)
  have hn : 0 ≤ C*p^((21 : ℝ)/2) :=
    mul_nonneg hC0 (Real.rpow_nonneg hp _)
  nlinarith

end CubicTenVariables.PrimeFrogOneMass
