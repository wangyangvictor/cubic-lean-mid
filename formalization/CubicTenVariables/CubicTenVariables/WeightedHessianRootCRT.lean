import CubicTenVariables.WeightedCRTAdapters
import CubicTenVariables.HessianKernelCRT
import CubicTenVariables.QuadraticGaussBound
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Exact CRT identities for actual Hessian-kernel-weighted root masses and
partially constrained directional-character sums. The kernel is computed
from the original integral polynomial's formal second partials. No abstract
multiplicativity, counting estimate or literature premise is assumed.
-/

noncomputable section
namespace CubicTenVariables.WeightedHessianRootCRT

open MvPolynomial HessianTheorem11 CRTCharacters WeightedCRTAdapters HessianKernelCRT
open scoped BigOperators

/-- The nonnegative square-root weight of the actual modular Hessian kernel. -/
def kernelWeight {v : ℕ} (F : MvPolynomial (Fin v) ℤ)
    (q : ℕ) (x : Fin v → ZMod q) : ℝ := Real.sqrt (hessianKernelCard F q x : ℝ)

/-- The actual Hessian-weighted mass of the polynomial-zero residue set. -/
def rootMass {v : ℕ} (F : MvPolynomial (Fin v) ℤ) (q : ℕ) [NeZero q] : ℝ := by
  classical
  exact ∑ x : Fin v → ZMod q,
    if eval₂ (Int.castRingHom (ZMod q)) x F = 0 then kernelWeight F q x else 0

/-- Kernel weight factorization at the actual two CRT projections. -/
theorem kernelWeight_mul {v m n : ℕ} [NeZero m] [NeZero n]
    (F : MvPolynomial (Fin v) ℤ) (hc : m.Coprime n)
    (x : Fin v → ZMod (m*n)) :
    kernelWeight F (m*n) x =
      kernelWeight F m (fun i => leftProjection hc (x i)) *
      kernelWeight F n (fun i => rightProjection hc (x i)) := by
  unfold kernelWeight
  rw [hessianKernelCard_mul F hc, Nat.cast_mul, Real.sqrt_mul (by positivity)]

/-- Exact multiplicativity of the source's square-root-weighted cubic root
mass. In fact no degree or homogeneity assumption is needed. -/
theorem rootMass_mul {v m n : ℕ} [NeZero m] [NeZero n]
    (F : MvPolynomial (Fin v) ℤ) (hc : m.Coprime n) :
    rootMass F (m*n) = rootMass F m * rootMass F n := by
  classical
  unfold rootMass
  calc
    _ = ∑ x : Fin v → ZMod (m*n),
      (if eval₂ (Int.castRingHom (ZMod m)) (fun i => leftProjection hc (x i)) F = 0 then
        kernelWeight F m (fun i => leftProjection hc (x i)) else 0) *
      (if eval₂ (Int.castRingHom (ZMod n)) (fun i => rightProjection hc (x i)) F = 0 then
        kernelWeight F n (fun i => rightProjection hc (x i)) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [PolynomialResidueCRT.zero_crt_iff F hc, kernelWeight_mul F hc]
      split_ifs <;> simp_all
    _ = _ := sum_crt_product hc
      (fun x => if eval₂ (Int.castRingHom (ZMod m)) x F = 0 then kernelWeight F m x else 0)
      (fun x => if eval₂ (Int.castRingHom (ZMod n)) x F = 0 then kernelWeight F n x else 0)

/-- An unrestricted directional-character sum with a Hessian weight whose
modulus divides the character modulus. -/
def characterMass {v : ℕ} (F : MvPolynomial (Fin v) ℤ)
    (c d : ℕ) [NeZero c] (hd : d ∣ c) (a : ZMod c) (h : Fin v → ℤ) : ℂ :=
  ∑ x : Fin v → ZMod c,
    (kernelWeight F d (fun i => ZMod.castHom hd (ZMod d) (x i)) : ℂ) *
      ZMod.stdAddChar (a * directionalPhase F h x)

/-- The same character sum restricted by the literal polynomial equation
at the full character modulus. -/
def rootCharacterMass {v : ℕ} (F : MvPolynomial (Fin v) ℤ)
    (c d : ℕ) [NeZero c] (hd : d ∣ c) (a : ZMod c) (h : Fin v → ℤ) : ℂ := by
  classical
  exact ∑ x : Fin v → ZMod c,
    if eval₂ (Int.castRingHom (ZMod c)) x F = 0 then
      (kernelWeight F d (fun i => ZMod.castHom hd (ZMod d) (x i)) : ℂ) *
        ZMod.stdAddChar (a * directionalPhase F h x)
    else 0

/-- A partial polynomial-zero restriction at a divisor r of the character
modulus c. All three reductions are literal ring homomorphisms. -/
def partialRootCharacterMass {v : ℕ} (F : MvPolynomial (Fin v) ℤ)
    (c d r : ℕ) [NeZero c] (hd : d ∣ c) (hr : r ∣ c)
    (a : ZMod c) (h : Fin v → ℤ) : ℂ := by
  classical
  exact ∑ x : Fin v → ZMod c,
    if eval₂ (Int.castRingHom (ZMod r))
      (fun i => ZMod.castHom hr (ZMod r) (x i)) F = 0 then
      (kernelWeight F d (fun i => ZMod.castHom hd (ZMod d) (x i)) : ℂ) *
        ZMod.stdAddChar (a * directionalPhase F h x)
    else 0

theorem kernelWeight_nonneg {v : ℕ} (F : MvPolynomial (Fin v) ℤ)
    (q : ℕ) (x : Fin v → ZMod q) : 0 ≤ kernelWeight F q x := Real.sqrt_nonneg _

theorem rootMass_nonneg {v q : ℕ} [NeZero q] (F : MvPolynomial (Fin v) ℤ) :
    0 ≤ rootMass F q := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact kernelWeight_nonneg F q x
  · exact le_rfl

/-- Discarding a unit-modulus character gives the actual nonnegative root
mass. The scalar itself may be any residue, including zero. -/
theorem norm_rootCharacterMass_le_rootMass {v m : ℕ} [NeZero m]
    (F : MvPolynomial (Fin v) ℤ) (a : ZMod m) (h : Fin v → ℤ) :
    ‖rootCharacterMass F m m (dvd_refl m) a h‖ ≤ rootMass F m := by
  classical
  have hself : ZMod.castHom (dvd_refl m) (ZMod m) = RingHom.id (ZMod m) :=
    Subsingleton.elim _ _
  unfold rootCharacterMass rootMass
  simp only [hself, RingHom.id_apply]
  calc
    _ ≤ ∑ x : Fin v → ZMod m,
        ‖if eval₂ (Int.castRingHom (ZMod m)) x F = 0 then
          (kernelWeight F m x : ℂ) * ZMod.stdAddChar (a * directionalPhase F h x)
        else 0‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs
      · rw [norm_mul, QuadraticGaussBound.norm_stdAddChar, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kernelWeight_nonneg F m x)]
      · exact norm_zero

/-- Exact source onion factorization. The polynomial-zero condition is
retained only modulo m; the right factor is genuinely unrestricted. The
weight modulus is m*d with d|n, and both inverse-modulus twists are visible. -/
theorem partialRootCharacterMass_crt {v m n d : ℕ} [NeZero m] [NeZero n]
    (F : MvPolynomial (Fin v) ℤ) (hc : m.Coprime n) (hd : d ∣ n)
    (a : ZMod (m*n)) (h : Fin v → ℤ) :
    partialRootCharacterMass F (m*n) (m*d) m
      (Nat.mul_dvd_mul (dvd_refl m) hd) (dvd_mul_right m n) a h =
    rootCharacterMass F m m (dvd_refl m)
      ((leftTwist hc : ZMod m) * leftProjection hc a) h *
    characterMass F n d hd
      ((rightTwist hc : ZMod n) * rightProjection hc a) h := by
  classical
  have hd0 : d ≠ 0 := by
    intro he
    subst d
    exact NeZero.ne n (Nat.zero_dvd.mp hd)
  letI : NeZero d := ⟨hd0⟩
  let hc' : m.Coprime d := hc.of_dvd_right hd
  have hleft : (leftProjection hc').comp
      (ZMod.castHom (Nat.mul_dvd_mul (dvd_refl m) hd) (ZMod (m*d))) =
      leftProjection hc := Subsingleton.elim _ _
  have hright : (rightProjection hc').comp
      (ZMod.castHom (Nat.mul_dvd_mul (dvd_refl m) hd) (ZMod (m*d))) =
      (ZMod.castHom hd (ZMod d)).comp (rightProjection hc) := Subsingleton.elim _ _
  have hroot : ZMod.castHom (dvd_mul_right m n) (ZMod m) =
      leftProjection hc := Subsingleton.elim _ _
  have hself : ZMod.castHom (dvd_refl m) (ZMod m) = RingHom.id (ZMod m) :=
    Subsingleton.elim _ _
  have hw (x : Fin v → ZMod (m*n)) :
      kernelWeight F (m*d)
        (fun i => ZMod.castHom (Nat.mul_dvd_mul (dvd_refl m) hd) (ZMod (m*d)) (x i)) =
      kernelWeight F m (fun i => leftProjection hc (x i)) *
      kernelWeight F d (fun i => ZMod.castHom hd (ZMod d) (rightProjection hc (x i))) := by
    rw [kernelWeight_mul F hc']
    have hl (i : Fin v) := congrArg (fun f : ZMod (m*n) →+* ZMod m => f (x i)) hleft
    have hr (i : Fin v) := congrArg (fun f : ZMod (m*n) →+* ZMod d => f (x i)) hright
    simp only [RingHom.comp_apply] at hl hr
    simp only [hl, hr]
  let L (x : Fin v → ZMod m) : ℂ :=
    if eval₂ (Int.castRingHom (ZMod m)) x F = 0 then
      (kernelWeight F m x : ℂ) * ZMod.stdAddChar
        (((leftTwist hc : ZMod m) * leftProjection hc a) * directionalPhase F h x)
    else 0
  let R (y : Fin v → ZMod n) : ℂ :=
    (kernelWeight F d (fun i => ZMod.castHom hd (ZMod d) (y i)) : ℂ) *
      ZMod.stdAddChar
        (((rightTwist hc : ZMod n) * rightProjection hc a) * directionalPhase F h y)
  calc
    _ = ∑ x : Fin v → ZMod (m*n),
        L (fun i => leftProjection hc (x i)) * R (fun i => rightProjection hc (x i)) := by
      unfold partialRootCharacterMass
      apply Finset.sum_congr rfl
      intro x _
      rw [hroot, hw, stdAddChar_directionalPhase_crt hc]
      simp only [L, R, Complex.ofReal_mul]
      split_ifs <;> ring
    _ = (∑ x, L x) * ∑ y, R y := sum_crt_product hc L R
    _ = _ := by simp only [rootCharacterMass, characterMass, hself, RingHom.id_apply, L, R]

end CubicTenVariables.WeightedHessianRootCRT
