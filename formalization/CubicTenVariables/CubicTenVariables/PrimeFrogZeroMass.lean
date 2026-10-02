import CubicTenVariables.SquarefreeResidueFactors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The finite j=0 frog mass decomposition

The two literal vector gcds are taken on canonical integral lifts. Away
from the origin their product is either one or p according to whether
the actual reduced gradient vanishes. No point-count estimate is assumed.
-/

noncomputable section
namespace CubicTenVariables.PrimeFrogZeroMass
open MvPolynomial SquarefreeResidueFactors
open scoped BigOperators

variable {n : ℕ}

/-- Canonical integral representatives of the residue coordinates. -/
def integerLift (p : ℕ) (x : Fin n → ZMod p) : Fin n → ℤ := fun i => (x i).val

/-- The source's actual two gcd factors, with no exceptional primes removed. -/
def rootWeight (F : MvPolynomial (Fin n) ℤ) (p : ℕ) (x : Fin n → ZMod p) : ℕ :=
  vectorGcd p (fun i => eval (integerLift p x) (pderiv i F)) *
    vectorGcd p (integerLift p x)

theorem cast_eval_integerLift (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [NeZero p] (x : Fin n → ZMod p) :
    (eval (integerLift p x) F : ZMod p) = eval₂ (Int.castRingHom (ZMod p)) x F := by
  simpa only [integerLift, Int.coe_castRingHom, Int.cast_natCast,
    ZMod.natCast_zmod_val, Function.comp_def] using
    eval₂_comp (Int.castRingHom (ZMod p)) (integerLift p x) F

theorem dvd_lift_iff_zero (p : ℕ) [NeZero p] (x : Fin n → ZMod p) :
    (∀ i, (p : ℤ) ∣ integerLift p x i) ↔ x = 0 := by
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, integerLift,
    Int.cast_natCast, ZMod.natCast_zmod_val, funext_iff, Pi.zero_apply]

theorem dvd_gradient_lift_iff (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [NeZero p] (x : Fin n → ZMod p) :
    (∀ i, (p : ℤ) ∣ eval (integerLift p x) (pderiv i F)) ↔
      ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0 := by
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, cast_eval_integerLift]

/-- Exact dichotomy for each of the two actual gcd factors. -/
theorem rootWeight_eq (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) [NeZero p] (x : Fin n → ZMod p) :
    rootWeight F p x =
      (if ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0 then p else 1) *
      (if x = 0 then p else 1) := by
  simp only [rootWeight, vectorGcd_prime p hp, dvd_gradient_lift_iff, dvd_lift_iff_zero]

/-- The pointwise elementary majorant keeps the origin separate. -/
theorem rootWeight_le (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) [NeZero p] (x : Fin n → ZMod p) :
    rootWeight F p x ≤ 1 +
      (if ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0 then p else 0) +
      (if x = 0 then p^2 else 0) := by
  classical
  rw [rootWeight_eq F p hp x]
  have hp2 := hp.two_le
  split_ifs <;> simp_all only [mul_one, one_mul, add_zero, pow_two] <;> nlinarith

/-- The actual prime-root mass is bounded by the actual root count,
p times the actual gradient-zero count, and the origin contribution p².
This finite inequality needs neither homogeneity nor a counting input. -/
theorem sum_rootWeight_le (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) [NeZero p] :
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod p =>
      eval₂ (Int.castRingHom (ZMod p)) x F = 0), rootWeight F p x) ≤
    (Finset.univ.filter (fun x : Fin n → ZMod p =>
      eval₂ (Int.castRingHom (ZMod p)) x F = 0)).card +
    p * (Finset.univ.filter (fun x : Fin n → ZMod p =>
      ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0)).card + p^2 := by
  classical
  let S := Finset.univ.filter (fun x : Fin n → ZMod p =>
    eval₂ (Int.castRingHom (ZMod p)) x F = 0)
  let G := fun x : Fin n → ZMod p =>
    ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0
  have hgrad : (∑ x ∈ S, if G x then p else 0) ≤
      p * (Finset.univ.filter G).card := by
    calc
      _ ≤ ∑ x : Fin n → ZMod p, if G x then p else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
      _ = _ := by
        rw [← Finset.sum_filter]
        simp [Nat.mul_comm]
  have horigin : (∑ x ∈ S, if x = 0 then p^2 else 0) ≤ p^2 := by
    calc
      _ ≤ ∑ x : Fin n → ZMod p, if x = 0 then p^2 else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
      _ = _ := by simp
  have hpoint := Finset.sum_le_sum (s := S) (fun x _ => rootWeight_le F p hp x)
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hpoint
  change (∑ x ∈ S, rootWeight F p x) ≤ S.card + p * (Finset.univ.filter G).card + p^2
  change (∑ x ∈ S, rootWeight F p x) ≤ S.card +
    (∑ x ∈ S, if G x then p else 0) + (∑ x ∈ S, if x = 0 then p^2 else 0) at hpoint
  omega

end CubicTenVariables.PrimeFrogZeroMass
