import HessianTheorem11.SmoothCubicPoint

/-! Nonconstant characteristic-zero polynomials have a nonzero partial
derivative of strictly smaller total degree. Coefficient proofs supply the
ordinary smooth-point argument for every irreducible hypersurface. -/

noncomputable section
namespace HessianTheorem11.ReducedHypersurfacePartials
open MvPolynomial
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem coeff_X_pderiv (P : MvPolynomial (Fin n) K) (i : Fin n)
    (e : Fin n →₀ ℕ) :
    coeff e (X i * pderiv i P) = (e i : K) * coeff e P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [X_mul_pderiv_monomial, coeff_smul]
    by_cases he : u = e
    · subst u
      simp [coeff_monomial, nsmul_eq_mul]
    · simp [coeff_monomial, he, nsmul_eq_mul]
  | add P Q hP hQ =>
    simp only [map_add, mul_add, coeff_add, hP, hQ]

theorem coeff_pderiv (P : MvPolynomial (Fin n) K) (i : Fin n)
    (e : Fin n →₀ ℕ) :
    coeff e (pderiv i P) = ((1 + e i : ℕ) : K) *
      coeff (Finsupp.single i 1 + e) P := by
  classical
  rw [← coeff_X_mul e i (pderiv i P), coeff_X_pderiv]
  simp

theorem eq_constant_of_partials_zero (P : MvPolynomial (Fin n) K)
    (hP : ∀ i, pderiv i P = 0) : P = C (coeff 0 P) := by
  classical
  ext e
  by_cases he : e = 0
  · subst e
    simp
  · obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    have h := coeff_X_pderiv P i e
    rw [hP i, mul_zero, coeff_zero] at h
    have hc : coeff e P = 0 := (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hi)
    simp [coeff_C, Ne.symm he, hc]

theorem exists_nonzero_partial (P : MvPolynomial (Fin n) K)
    (hP : Irreducible P) : ∃ i, pderiv i P ≠ 0 := by
  by_contra h
  push_neg at h
  have he := eq_constant_of_partials_zero P h
  have hc : coeff 0 P ≠ 0 := by
    intro hz
    exact hP.ne_zero (by simpa [hz] using he)
  exact hP.not_isUnit (he ▸ (isUnit_iff_ne_zero.mpr hc).map C)

theorem partial_support_degree_lt (P : MvPolynomial (Fin n) K) (i : Fin n)
    (e : Fin n →₀ ℕ) (he : e ∈ (pderiv i P).support) :
    e.sum (fun _ k => k) < P.totalDegree := by
  classical
  have hp : coeff (Finsupp.single i 1 + e) P ≠ 0 := by
    intro hz
    have h := MvPolynomial.mem_support_iff.mp he
    exact h (by rw [coeff_pderiv, hz, mul_zero])
  have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hp)
  have hs : (Finsupp.single i 1 + e).sum (fun _ k => k) =
      1 + e.sum (fun _ k => k) := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  rw [hs] at hd
  omega

theorem totalDegree_partial_lt (P : MvPolynomial (Fin n) K) (i : Fin n)
    (hi : pderiv i P ≠ 0) : (pderiv i P).totalDegree < P.totalDegree := by
  classical
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hi
  have hd : 0 < P.totalDegree := lt_of_le_of_lt (Nat.zero_le _)
    (partial_support_degree_lt P i e he)
  exact (Finset.sup_lt_iff hd).mpr (fun e he => partial_support_degree_lt P i e he)

theorem not_dvd_partial (P : MvPolynomial (Fin n) K) (i : Fin n)
    (hi : pderiv i P ≠ 0) : ¬ P ∣ pderiv i P := by
  intro h
  exact (not_le_of_gt (totalDegree_partial_lt P i hi))
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain h hi)

end HessianTheorem11.ReducedHypersurfacePartials
