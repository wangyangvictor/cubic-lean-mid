import HessianTheorem11.PolynomialRestriction

/-!
# A polynomial of total degree at most two has constant Hessian

Coefficient identities prove this over arbitrary commutative rings, including
finite fields of small characteristic. No separability or nondegeneracy is
required. This identifies the Hessian of every affine binary slice with the
same fixed quadratic matrix.
-/

noncomputable section
namespace CubicTenVariables.QuadraticHessianConstant
open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

theorem coeff_X_pderiv (P : MvPolynomial (Fin n) R) (i : Fin n)
    (d : Fin n →₀ ℕ) :
    coeff d (X i * pderiv i P) = (d i : R) * coeff d P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [X_mul_pderiv_monomial, coeff_smul]
    by_cases hd : u = d
    · subst u
      simp [coeff_monomial, nsmul_eq_mul]
    · simp [coeff_monomial, hd]
  | add P Q hP hQ =>
    simp only [map_add, mul_add, coeff_add, hP, hQ]

theorem coeff_pderiv (P : MvPolynomial (Fin n) R) (i : Fin n)
    (d : Fin n →₀ ℕ) :
    coeff d (pderiv i P) = ((1+d i : ℕ) : R) *
      coeff (Finsupp.single i 1+d) P := by
  classical
  rw [← coeff_X_mul d i (pderiv i P), coeff_X_pderiv]
  simp

theorem second_pderiv_eq_constant (P : MvPolynomial (Fin n) R)
    (hP : P.totalDegree ≤ 2) (i j : Fin n) :
    pderiv i (pderiv j P) = C (coeff 0 (pderiv i (pderiv j P))) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · have hpos : 0 < d.degree := Nat.pos_of_ne_zero
      (fun h => hd ((Finsupp.degree_eq_zero_iff d).mp h))
    have hdeg : P.totalDegree <
        (Finsupp.single j 1+(Finsupp.single i 1+d)).degree := by
      simp only [map_add, Finsupp.degree_single]
      omega
    have hz := coeff_eq_zero_of_totalDegree_lt (f := P) (by
      simpa only [Finsupp.degree_apply, Finsupp.sum] using hdeg)
    simp only [coeff_pderiv, hz, mul_zero, coeff_C, if_neg (Ne.symm hd)]

/-- Actual evaluated second derivatives are independent of the point. -/
theorem hessian_eq_origin (P : MvPolynomial (Fin n) R)
    (hP : P.totalDegree ≤ 2) (x : Fin n → R) :
    HessianTheorem11.hessian P x = HessianTheorem11.hessian P 0 := by
  ext i j
  change eval x (pderiv j (pderiv i P)) = eval 0 (pderiv j (pderiv i P))
  rw [second_pderiv_eq_constant P hP j i, eval_C, eval_C]

/-- Coefficient homomorphisms preserve the actual Hessian at the origin. -/
theorem hessian_map_origin {S : Type*} [CommRing S] (f : R →+* S)
    (P : MvPolynomial (Fin n) R) :
    HessianTheorem11.hessian (map f P) (0 : Fin n → S) =
      (HessianTheorem11.hessian P (0 : Fin n → R)).map f := by
  ext i j
  simp only [HessianTheorem11.hessian, HessianTheorem11.hessianPolynomial,
    pderiv_map, Matrix.map_apply, eval_zero, constantCoeff_eq, coeff_map]

end CubicTenVariables.QuadraticHessianConstant
