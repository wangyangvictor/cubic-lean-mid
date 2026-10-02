import HessianTheorem11.FormalSmoothArc
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Factorial.Basic

/-! Exponentiating a derivation over a characteristic-zero field gives an
actual formal algebra homomorphism. Multiplicativity is proved by induction
on coefficients, using the ordinary Leibniz rule. -/

noncomputable section
namespace HessianTheorem11.ReducedDerivationExponential
open MvPolynomial
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]

def flowSeries (D : Derivation K A A) (e : A →ₐ[K] K) (p : A) : PowerSeries K :=
  PowerSeries.mk (fun k => e ((D.toLinearMap ^ k) p) / (Nat.factorial k : K))

@[simp] theorem coeff_flowSeries (D : Derivation K A A) (e : A →ₐ[K] K)
    (p : A) (k : ℕ) :
    PowerSeries.coeff k (flowSeries D e p) =
      e ((D.toLinearMap ^ k) p) / (Nat.factorial k : K) := by
  simp [flowSeries]

@[simp] theorem constantCoeff_flowSeries (D : Derivation K A A) (e : A →ₐ[K] K)
    (p : A) : PowerSeries.constantCoeff (flowSeries D e p) = e p := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

@[simp] theorem flowSeries_zero (D : Derivation K A A) (e : A →ₐ[K] K) :
    flowSeries D e 0 = 0 := by
  ext k
  simp

@[simp] theorem flowSeries_add (D : Derivation K A A) (e : A →ₐ[K] K) (p q : A) :
    flowSeries D e (p+q) = flowSeries D e p + flowSeries D e q := by
  ext k
  simp [add_div]

@[simp] theorem flowSeries_algebraMap (D : Derivation K A A) (e : A →ₐ[K] K)
    (c : K) : flowSeries D e (algebraMap K A c) = PowerSeries.C c := by
  ext k
  cases k with
  | zero => simp
  | succ k =>
    simp [pow_succ, Module.End.mul_apply, D.map_algebraMap]

@[simp] theorem flowSeries_one (D : Derivation K A A) (e : A →ₐ[K] K) :
    flowSeries D e 1 = 1 := by
  simpa only [map_one] using flowSeries_algebraMap D e 1

theorem derivative_flowSeries (D : Derivation K A A) (e : A →ₐ[K] K) (p : A) :
    PowerSeries.derivative K (flowSeries D e p) = flowSeries D e (D p) := by
  ext k
  rw [PowerSeries.coeff_derivative, coeff_flowSeries, coeff_flowSeries]
  simp only [pow_succ, Module.End.mul_apply, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hn : (k : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp
  rfl

/-- Coefficient induction proves the exponential preserves multiplication,
without assuming a formal-flow theorem or a binomial-series identity. -/
theorem flowSeries_mul (D : Derivation K A A) (e : A →ₐ[K] K) (p q : A) :
    flowSeries D e (p*q) = flowSeries D e p * flowSeries D e q := by
  have h (k : ℕ) : ∀ p q : A,
      PowerSeries.coeff k (flowSeries D e (p*q)) =
        PowerSeries.coeff k (flowSeries D e p * flowSeries D e q) := by
    induction k with
    | zero =>
      intro p q
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    | succ k ih =>
      intro p q
      apply mul_right_cancel₀ (show (k : K)+1 ≠ 0 by exact_mod_cast Nat.succ_ne_zero k)
      calc
        PowerSeries.coeff (k+1) (flowSeries D e (p*q)) * ((k:K)+1) =
            PowerSeries.coeff k (flowSeries D e (D (p*q))) := by
          rw [← PowerSeries.coeff_derivative, derivative_flowSeries]
        _ = PowerSeries.coeff k
            (flowSeries D e (p * D q) + flowSeries D e (q * D p)) := by
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, flowSeries_add]
        _ = PowerSeries.coeff k
            (flowSeries D e p * flowSeries D e (D q) +
             flowSeries D e q * flowSeries D e (D p)) := by
          rw [map_add, map_add, ih p (D q), ih q (D p)]
        _ = PowerSeries.coeff k
            (PowerSeries.derivative K (flowSeries D e p * flowSeries D e q)) := by
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
            derivative_flowSeries, derivative_flowSeries]
        _ = PowerSeries.coeff (k+1)
            (flowSeries D e p * flowSeries D e q) * ((k:K)+1) :=
          PowerSeries.coeff_derivative _ k
  exact PowerSeries.ext (h · p q)

def flowAlgHom (D : Derivation K A A) (e : A →ₐ[K] K) : A →ₐ[K] PowerSeries K where
  toFun := flowSeries D e
  map_zero' := flowSeries_zero D e
  map_one' := flowSeries_one D e
  map_add' := flowSeries_add D e
  map_mul' := flowSeries_mul D e
  commutes' := flowSeries_algebraMap D e

/-- An ideal-preserving polynomial derivation integrates to a formal arc.
This statement is algebraic and works over every characteristic-zero field. -/
theorem exists_formal_arc_of_derivation {n : ℕ}
    (D : Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : ∀ p ∈ I, D p ∈ I)
    (x v : Fin n → K) (hx : ∀ p ∈ I, eval x p = 0)
    (hv : ∀ i, eval x (D (X i)) = v i) :
    ∃ γ : Fin n → PowerSeries K,
      arcCoefficient γ 0 = x ∧ arcCoefficient γ 1 = v ∧
      ∀ p ∈ I, eval₂ PowerSeries.C γ p = 0 := by
  let e : MvPolynomial (Fin n) K →ₐ[K] K := aeval x
  let E := flowAlgHom D e
  let γ : Fin n → PowerSeries K := fun i => E (X i)
  have he : aeval γ = E := by
    apply MvPolynomial.algHom_ext
    intro i
    exact aeval_X γ i
  have hiter (k : ℕ) (p : MvPolynomial (Fin n) K) (hp : p ∈ I) :
      (D.toLinearMap ^ k) p ∈ I := by
    induction k with
    | zero => simpa using hp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hI _ ih
  refine ⟨γ, ?_, ?_, ?_⟩
  · funext i
    change PowerSeries.coeff 0 (flowSeries D e (X i)) = x i
    simp [e]
  · funext i
    change PowerSeries.coeff 1 (flowSeries D e (X i)) = v i
    simpa [e] using hv i
  · intro p hp
    change aeval γ p = 0
    rw [he]
    apply PowerSeries.ext
    intro k
    change PowerSeries.coeff k (flowSeries D e p) = PowerSeries.coeff k 0
    rw [coeff_flowSeries]
    change eval x ((D.toLinearMap ^ k) p) / (Nat.factorial k : K) = _
    rw [hx _ (hiter k p hp)]
    simp

end HessianTheorem11.ReducedDerivationExponential
