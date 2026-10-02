import TranslatedDepthSeven.FilteredAffinePlaneCurveMonomialWeights
import TranslatedDepthSeven.PrincipalCurveStandardMonomialIndependence
import TranslatedDepthSeven.AffinePlaneMonomialEvaluation

/-!
# The affine-weight monomial block for a plane curve

The leading monomial of the actual first-chart equation selects the
standard monomials. Their degree-`k` homogeneous lifts are independent
modulo the original homogeneous equation, and their integral evaluations
have the exact affine weights counted in the companion file.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators

/-- First-chart dehomogenization in three coordinates, over any coefficient
field. -/
def affinePlaneDehomogenization (K : Type*) [CommSemiring K] :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval (Fin.cases 1 (fun j => X j))

/-- The two actual affine exponents of a triangular-block index. -/
def affinePlaneMonomialAffineExponent {k : ℕ}
    (u : AffinePlaneMonomialIndex k) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![u.2.1, u.1.1 - u.2.1]

theorem affinePlaneMonomialAffineExponent_injective (k : ℕ) :
    Function.Injective (@affinePlaneMonomialAffineExponent k) := by
  intro u v huv
  have ha : u.2.1 = v.2.1 := by
    simpa [affinePlaneMonomialAffineExponent] using congrArg (fun d => d 0) huv
  have hb : u.1.1 - u.2.1 = v.1.1 - v.2.1 := by
    simpa [affinePlaneMonomialAffineExponent] using congrArg (fun d => d 1) huv
  have hu := u.2.2
  have hv := v.2.2
  have hj : u.1.1 = v.1.1 := by omega
  apply Sigma.ext (Fin.ext hj)
  exact (Fin.heq_ext_iff (by omega)).mpr ha

theorem affinePlaneDehomogenization_homogeneousMonomial
    (K : Type*) [CommSemiring K] (k : ℕ)
    (u : AffinePlaneMonomialIndex k) :
    affinePlaneDehomogenization K (affinePlaneHomogeneousMonomial K k u) =
      monomial (affinePlaneMonomialAffineExponent u) 1 := by
  classical
  rw [affinePlaneDehomogenization, affinePlaneHomogeneousMonomial,
    MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_three]
    simp only [affinePlaneMonomialExponent, Finsupp.equivFunOnFinite_symm_apply_toFun,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Fin.cases_zero, one_pow, one_mul]
    change X (0 : Fin 2) ^ u.2.1 * X (1 : Fin 2) ^ (u.1.1 - u.2.1) = _
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul]
    simp only [mul_one]
    apply congrArg (fun e : Fin 2 →₀ ℕ => monomial e (1 : K))
    ext i
    fin_cases i <;> simp [affinePlaneMonomialAffineExponent]
  · intro i
    simp

/-- Standard monomials for the actual first-chart equation are independent
in the homogeneous principal quotient after lifting to a common degree. -/
theorem linearIndependent_filteredAffinePlaneCurveMonomials_of_leadingDivisor
    {K : Type*} [Field K] (P : MvPolynomial (Fin 3) K)
    (hdehom : affinePlaneDehomogenization K P ≠ 0) (k a b : ℕ)
    (ha : a ≤ (MonomialOrder.degLex.degree (affinePlaneDehomogenization K P)) 0)
    (hb : b ≤ (MonomialOrder.degLex.degree (affinePlaneDehomogenization K P)) 1) :
    let m := MonomialOrder.degLex.degree (affinePlaneDehomogenization K P)
    LinearIndependent K
      (fun u : FilteredAffinePlaneCurveMonomialIndex a b k =>
        Ideal.Quotient.mk (Ideal.span ({P} : Set _))
          (affinePlaneHomogeneousMonomial K k u.1)) := by
  classical
  dsimp only
  let f := affinePlaneDehomogenization K P
  let m := MonomialOrder.degLex.degree f
  let T := FilteredAffinePlaneCurveMonomialIndex a b k
  let d : T → Fin 2 →₀ ℕ := fun u => affinePlaneMonomialAffineExponent u.1
  have hd : Function.Injective d :=
    (affinePlaneMonomialAffineExponent_injective k).comp Subtype.val_injective
  have hstandard : ∀ u : T, ¬ MonomialOrder.degLex.degree f ≤ d u := by
    intro u h
    apply u.2
    exact ⟨ha.trans (by simpa [d, affinePlaneMonomialAffineExponent] using h 0),
      hb.trans (by simpa [d, affinePlaneMonomialAffineExponent] using h 1)⟩
  have haff := linearIndependent_standardMonomials_quotient_principal
    MonomialOrder.degLex f hdehom d hd hstandard
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let G := ∑ u : T, c u • affinePlaneHomogeneousMonomial K k u.1
  have hGmem : G ∈ Ideal.span ({P} : Set _) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ K (Ideal.span ({P} : Set _)) G = 0
    simpa only [G, map_sum, map_smul] using hc
  have hdiv : f ∣ affinePlaneDehomogenization K G :=
    map_dvd (affinePlaneDehomogenization K) (Ideal.mem_span_singleton.mp hGmem)
  have hzero : Ideal.Quotient.mk (Ideal.span ({f} : Set _))
      (affinePlaneDehomogenization K G) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  apply Fintype.linearIndependent_iff.mp haff c
  change Ideal.Quotient.mkₐ K (Ideal.span ({f} : Set _))
      (affinePlaneDehomogenization K G) = 0 at hzero
  simpa only [G, map_sum, map_smul,
    affinePlaneDehomogenization_homogeneousMonomial, d] using hzero

theorem linearIndependent_filteredAffinePlaneCurveMonomials
    {K : Type*} [Field K] (P : MvPolynomial (Fin 3) K)
    (hdehom : affinePlaneDehomogenization K P ≠ 0) (k : ℕ) :
    let m := MonomialOrder.degLex.degree (affinePlaneDehomogenization K P)
    LinearIndependent K
      (fun u : FilteredAffinePlaneCurveMonomialIndex (m 0) (m 1) k =>
        Ideal.Quotient.mk (Ideal.span ({P} : Set _))
          (affinePlaneHomogeneousMonomial K k u.1)) :=
  linearIndependent_filteredAffinePlaneCurveMonomials_of_leadingDivisor
    P hdehom k _ _ le_rfl le_rfl

/-- Each integer lift obeys its own affine weight, independently of the
coefficient size of the defining equation. -/
theorem eval_filteredAffinePlaneCurveMonomial_natAbs_le
    (a b k R : ℕ) (u : FilteredAffinePlaneCurveMonomialIndex a b k)
    (x : Fin 3 → ℤ) (hx0 : x 0 = 1)
    (hx1 : (x 1).natAbs ≤ R) (hx2 : (x 2).natAbs ≤ R) :
    (eval x (affinePlaneHomogeneousMonomial ℤ k u.1)).natAbs ≤
      R ^ affinePlaneMonomialIndexWeight u.1 := by
  have h := eval_aeval_affinePlaneHomogeneousMonomial_natAbs_le
    (fun i : Fin 3 => X i) x R k u.1
    (by simpa using hx0) (by simpa using hx1) (by simpa using hx2)
  simpa only [aeval_X_left_apply] using h

end
end TranslatedDepthSeven
