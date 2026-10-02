import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Descent of polynomial certificates on rational tuples

A nonzero polynomial over a field extension gives a nonzero polynomial over
the base field, of no larger total degree, whose nonvanishing certifies the
original polynomial's nonvanishing on base-field tuples. A linear functional
on coefficients suffices; no norm or finite-extension hypothesis is needed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CubicTenVariables.PolynomialCertificateDescent
open MvPolynomial

variable {K L σ : Type*} [Field K] [Field L] [Algebra K L]

/-- Apply a base-field linear functional to each coefficient. -/
def coefficientProjection (ℓ : L →ₗ[K] K) (P : MvPolynomial σ L) :
    MvPolynomial σ K :=
  Finsupp.mapRange ℓ ℓ.map_zero P

@[simp]
theorem coeff_coefficientProjection (ℓ : L →ₗ[K] K) (P : MvPolynomial σ L)
    (d : σ →₀ ℕ) :
    coeff d (coefficientProjection ℓ P) = ℓ (coeff d P) := by
  exact coeff_mapRange _ _ _ _

theorem totalDegree_coefficientProjection_le (ℓ : L →ₗ[K] K)
    (P : MvPolynomial σ L) :
    (coefficientProjection ℓ P).totalDegree ≤ P.totalDegree := by
  classical
  exact Finset.sup_mono Finsupp.support_mapRange

/-- Coefficient projection commutes with evaluation at a base-field tuple. -/
theorem eval_coefficientProjection (ℓ : L →ₗ[K] K) (P : MvPolynomial σ L)
    (x : σ → K) :
    eval x (coefficientProjection ℓ P) =
      ℓ (eval (algebraMap K L ∘ x) P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
      have hmap : coefficientProjection ℓ (monomial d a) = monomial d (ℓ a) :=
        Finsupp.mapRange_single
      rw [hmap, eval_monomial, eval_monomial]
      have hprod : d.prod (fun i n => (algebraMap K L (x i)) ^ n) =
          algebraMap K L (d.prod (fun i n => x i ^ n)) := by
        simp [Finsupp.prod, map_prod, map_pow]
      simp only [Function.comp_apply, hprod]
      rw [mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  | add P Q hP hQ =>
      have hadd : coefficientProjection ℓ (P + Q) =
          coefficientProjection ℓ P + coefficientProjection ℓ Q := by
        ext d
        simp
      rw [hadd, eval_add, eval_add, map_add, hP, hQ]

/-- Descend a polynomial certificate without increasing its degree.
The implication deliberately concerns tuples over `K`, not arbitrary
tuples over the extension field. -/
theorem exists_nonzero_polynomial_certificate (P : MvPolynomial σ L) (hP : P ≠ 0) :
    ∃ Δ : MvPolynomial σ K, Δ ≠ 0 ∧ Δ.totalDegree ≤ P.totalDegree ∧
      ∀ x : σ → K, eval x Δ ≠ 0 → eval (algebraMap K L ∘ x) P ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, coeff d P ≠ 0 := by
    by_contra! h
    exact hP (MvPolynomial.ext P 0 fun d => by simpa using h d)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero K hd
  refine ⟨coefficientProjection ℓ P, ?_, totalDegree_coefficientProjection_le ℓ P, ?_⟩
  · intro hzero
    have h := congrArg (coeff d) hzero
    simpa using hℓ h
  · intro x hx hzero
    apply hx
    rw [eval_coefficientProjection, hzero, map_zero]

end CubicTenVariables.PolynomialCertificateDescent
