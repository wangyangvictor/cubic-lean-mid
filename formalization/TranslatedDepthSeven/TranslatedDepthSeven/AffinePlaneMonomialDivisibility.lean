import TranslatedDepthSeven.AffinePlaneMonomialEvaluation
import TranslatedDepthSeven.WeightedDeterminantDivisibility

/-!
# Local divisibility for the affine surface monomial block

If the two affine normalization coordinates of every point are divisible by
`p`, the column indexed by a monomial of affine weight `j` is divisible by
`p^j`.  Consequently the determinant of the complete degree-`k` block is
divisible by `p^W(k)`.  This is the literal monomial model behind the
multiplicity-one local determinant estimate.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- Pointwise divisibility by the exact affine monomial weight. -/
theorem pow_weight_dvd_eval_aeval_affinePlaneHomogeneousMonomial
    {σ : Type*} (L : Fin 3 → MvPolynomial σ ℤ)
    (y : σ → ℤ) (p : ℤ) (k : ℕ)
    (u : AffinePlaneMonomialIndex k)
    (hone : p ∣ MvPolynomial.eval y (L 1))
    (htwo : p ∣ MvPolynomial.eval y (L 2)) :
    p ^ affinePlaneMonomialIndexWeight u ∣
      MvPolynomial.eval y
        (MvPolynomial.aeval L
          (affinePlaneHomogeneousMonomial ℤ k u)) := by
  rw [eval_aeval_affinePlaneHomogeneousMonomial]
  have h₁ : p ^ u.2.1 ∣ MvPolynomial.eval y (L 1) ^ u.2.1 :=
    pow_dvd_pow_of_dvd hone u.2.1
  have h₂ : p ^ (u.1.1 - u.2.1) ∣
      MvPolynomial.eval y (L 2) ^ (u.1.1 - u.2.1) :=
    pow_dvd_pow_of_dvd htwo (u.1.1 - u.2.1)
  have hprod :
      p ^ u.2.1 * p ^ (u.1.1 - u.2.1) ∣
        MvPolynomial.eval y (L 1) ^ u.2.1 *
          MvPolynomial.eval y (L 2) ^ (u.1.1 - u.2.1) :=
    mul_dvd_mul h₁ h₂
  have hu : u.2.1 ≤ u.1.1 := Nat.lt_succ_iff.mp u.2.2
  rw [← pow_add, show u.2.1 + (u.1.1 - u.2.1) =
      affinePlaneMonomialIndexWeight u by
        simp only [affinePlaneMonomialIndexWeight]
        omega] at hprod
  simpa only [mul_assoc] using
    (dvd_mul_of_dvd_right hprod
      (MvPolynomial.eval y (L 0) ^ (k - u.1.1)))

/-- The determinant of the complete affine surface monomial block has the
exact local factor `p^W(k)`. -/
theorem pow_affinePlaneMonomialWeight_dvd_det
    {σ : Type*} (L : Fin 3 → MvPolynomial σ ℤ)
    (k : ℕ)
    (y : AffinePlaneMonomialIndex k → σ → ℤ)
    (p : ℤ)
    (hone : ∀ v, p ∣ MvPolynomial.eval (y v) (L 1))
    (htwo : ∀ v, p ∣ MvPolynomial.eval (y v) (L 2)) :
    p ^ affinePlaneMonomialWeight k ∣
      (Matrix.of (fun v u ↦
        MvPolynomial.eval (y v)
          (MvPolynomial.aeval L
            (affinePlaneHomogeneousMonomial ℤ k u)))).det := by
  classical
  have h := pow_sum_dvd_det_of_columns_pow_dvd
    (Matrix.of (fun v u ↦
      MvPolynomial.eval (y v)
        (MvPolynomial.aeval L
          (affinePlaneHomogeneousMonomial ℤ k u))))
    p affinePlaneMonomialIndexWeight
    (fun v u ↦
      pow_weight_dvd_eval_aeval_affinePlaneHomogeneousMonomial
        L (y v) p k u (hone v) (htwo v))
  rwa [sum_affinePlaneMonomialIndexWeight] at h

end

end TranslatedDepthSeven
