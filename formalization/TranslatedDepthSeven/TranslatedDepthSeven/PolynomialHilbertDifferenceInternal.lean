import TranslatedDepthSeven.HomogeneousComponentDegreeMassInternal
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The leading coefficient of a Hilbert-polynomial difference

Taylor coefficients are Hasse derivatives. For a polynomial of degree
`r+1`, its r-th Hasse derivative is affine-linear; this computes the
coefficient in degree r after the leading terms cancel.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- The backwards difference has degree at most r, and its coefficient in
degree r is the expected first finite difference of the leading term. -/
theorem polynomial_backwardDifference_degree_coeff
    (P : Polynomial ℚ) (r : ℕ) (a : ℚ) (hP : P.natDegree = r + 1) :
    (P - Polynomial.taylor (-a) P).natDegree ≤ r ∧
      (P - Polynomial.taylor (-a) P).coeff r =
        (r + 1 : ℚ) * a * P.leadingCoeff := by
  have hupper : (P - Polynomial.taylor (-a) P).natDegree ≤ r := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    by_cases htop : m = r + 1
    · rw [htop, ← hP, Polynomial.coeff_sub,
        Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]
      exact sub_self _
    · have hmP : P.natDegree < m := by omega
      rw [Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt hmP,
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (by simpa only [Polynomial.natDegree_taylor] using hmP)]
      exact sub_self _
  refine ⟨hupper, ?_⟩
  let L : Polynomial ℚ := Polynomial.hasseDeriv r P
  have hLdegree : L.natDegree ≤ 1 := by
    have h := Polynomial.natDegree_hasseDeriv_le P r
    simpa only [hP, Nat.add_sub_cancel_left] using h
  have hLzero : L.coeff 0 = P.coeff r := by
    simp only [L, Polynomial.hasseDeriv_coeff, Nat.zero_add, Nat.choose_self,
      Nat.cast_one, one_mul]
  have hLone : L.coeff 1 = (r + 1 : ℚ) * P.leadingCoeff := by
    rw [show L.coeff 1 = ((1 + r).choose r : ℚ) * P.coeff (1 + r) from
      Polynomial.hasseDeriv_coeff r P 1]
    rw [Nat.add_comm 1 r, Nat.choose_succ_self_right, ← hP, Polynomial.coeff_natDegree]
    simp only [hP, Nat.cast_add, Nat.cast_one]
  have hLeval : L.eval (-a) = ((r + 1 : ℚ) * P.leadingCoeff) * (-a) + P.coeff r := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hLdegree]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, hLzero, hLone]
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff]
  change P.coeff r - L.eval (-a) = _
  rw [hLeval]
  ring

/-- A positive proper hypersurface degree multiplies the leading Hilbert
multiplicity by its degree and lowers the polynomial degree by one. -/
theorem polynomial_backwardDifference_hilbert_data
    (P : Polynomial ℚ) (r d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hP : P.natDegree = r + 1)
    (hlc : P.leadingCoeff = (d : ℚ) / (r + 1).factorial) :
    (P - Polynomial.taylor (-(e : ℚ)) P).natDegree = r ∧
      (P - Polynomial.taylor (-(e : ℚ)) P).leadingCoeff =
        (d * e : ℕ) / (r.factorial : ℚ) := by
  obtain ⟨hupper, hcoeff⟩ := polynomial_backwardDifference_degree_coeff P r (e : ℚ) hP
  have hfact : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hsucc : (r + 1 : ℚ) ≠ 0 := by positivity
  have hcoeff' : (P - Polynomial.taylor (-(e : ℚ)) P).coeff r =
      (d * e : ℕ) / (r.factorial : ℚ) := by
    rw [hcoeff, hlc, Nat.factorial_succ]
    push_cast
    field_simp
  have hcoeffne : (P - Polynomial.taylor (-(e : ℚ)) P).coeff r ≠ 0 := by
    rw [hcoeff']
    exact div_ne_zero (by exact_mod_cast (Nat.mul_pos hd he).ne') hfact
  have hdegree := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hupper hcoeffne
  exact ⟨hdegree, by simpa only [Polynomial.leadingCoeff, hdegree] using hcoeff'⟩

end

end TranslatedDepthSeven
