import CubicTenVariables.BinaryCubicPerturbation

/-!
# Prime-field zeros of a nondegenerate binary quadratic reduction

The cubic part vanishes modulo the prime. The remaining literal polynomial
has total degree at most two, and its nonzero quadratic Hessian determinant
forces it to be nonzero as a polynomial. Schwartz--Zippel therefore bounds
its actual affine zero set by twice the prime, including characteristic two.
-/

noncomputable section
namespace CubicTenVariables.BinaryCubicPerturbation
open MvPolynomial

theorem polynomial_zero_totalDegree_le_two (G : Coefficients) :
    (polynomial G 0).totalDegree ≤ 2 := by
  have hadd {A B : MvPolynomial (Fin 2) ℤ}
      (hA : A.totalDegree ≤ 2) (hB : B.totalDegree ≤ 2) :
      (A + B).totalDegree ≤ 2 := (totalDegree_add _ _).trans (max_le hA hB)
  have hCmul (c : ℤ) (Q : MvPolynomial (Fin 2) ℤ) :
      (C c * Q).totalDegree ≤ Q.totalDegree := by
    simpa only [totalDegree_C, zero_add] using totalDegree_mul (C c) Q
  simp only [polynomial, map_zero, zero_mul, add_zero]
  refine hadd (hadd (hadd (hadd (hadd ?_ ?_) ?_) ?_) ?_) ?_
  · simp only [totalDegree_C]; omega
  · exact (hCmul _ _).trans (by simp)
  · exact (hCmul _ _).trans (by simp)
  · exact (hCmul _ _).trans (by simp)
  · have h := totalDegree_mul (C G.qxy * X 0 : MvPolynomial (Fin 2) ℤ) (X 1)
    have h' := hCmul G.qxy (X 0)
    simp only [totalDegree_X] at h h'
    omega
  · exact (hCmul _ _).trans (by simp)

theorem polynomial_zero_reduction_ne_zero (G : Coefficients) (p : ℕ)
    [Fact p.Prime] (hD : (discriminant G : ZMod p) ≠ 0) :
    map (Int.castRingHom (ZMod p)) (polynomial G 0) ≠ 0 := by
  intro hz
  have hdx (x y : ZMod p) : dx G 0 x y = 0 := by
    have h := congrArg (fun f : MvPolynomial (Fin 2) (ZMod p) =>
      eval ![x,y] (pderiv 0 f)) hz
    simpa only [pderiv_map, ← eval₂_eq_eval_map, eval₂_pderiv_zero,
      Int.cast_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      map_zero, eval_zero] using h
  have hdy (x y : ZMod p) : dy G 0 x y = 0 := by
    have h := congrArg (fun f : MvPolynomial (Fin 2) (ZMod p) =>
      eval ![x,y] (pderiv 1 f)) hz
    simpa only [pderiv_map, ← eval₂_eq_eval_map, eval₂_pderiv_one,
      Int.cast_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      map_zero, eval_zero] using h
  exact zero_ne_one (critical_point_unique G hD
    (hdx 0 0) (hdy 0 0) (hdx 1 0) (hdy 1 0)).1

/-- The actual reduced binary equation has at most `2*p` solutions.
No oddness hypothesis on the prime is required. -/
theorem card_prime_zeros_le_two_mul (G : Coefficients) (p : ℕ)
    [Fact p.Prime] (hD : (discriminant G : ZMod p) ≠ 0) :
    (Finset.univ.filter fun z : Fin 2 → ZMod p =>
      value G 0 (z 0) (z 1) = 0).card ≤ 2*p := by
  have h := TranslatedDepthSeven.card_mvPolynomialZeroSet_le_degree_mul
    (Fact.out : p.Prime) (map (Int.castRingHom (ZMod p)) (polynomial G 0))
    (polynomial_zero_reduction_ne_zero G p hD)
    ((UniformPrimePolynomialZeros.totalDegree_reduction_le (polynomial G 0)).trans
      (polynomial_zero_totalDegree_le_two G))
  simpa only [TranslatedDepthSeven.mvPolynomialZeroSet, ← eval₂_eq_eval_map,
    eval₂_polynomial, Int.cast_zero, Nat.reduceSub, pow_one] using h

end CubicTenVariables.BinaryCubicPerturbation
