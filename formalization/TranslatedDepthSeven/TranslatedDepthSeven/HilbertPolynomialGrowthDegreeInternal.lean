import TranslatedDepthSeven.HomogeneousHilbertPolynomialExistenceInternal
import TranslatedDepthSeven.HomogeneousNormalizationHilbertGrowthInternal
import Mathlib.Analysis.Polynomial.Basic

/-!
# Identifying degree and positivity from Hilbert growth

A polynomial bounded above and below by positive constant multiples of a
positive-leading-coefficient polynomial has the same degree and positive
leading coefficient. We apply this elementary comparison to the actual
homogeneous Hilbert function and its normalization binomial bounds.
-/

namespace TranslatedDepthSeven

noncomputable section
open Filter
open scoped Topology
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000

theorem polynomial_degree_eq_and_leadingCoeff_pos_of_nat_squeeze
    (P Q : Polynomial ℚ) (C : ℚ) (n₀ : ℕ)
    (hQlc : 0 < Q.leadingCoeff)
    (hQpositive : ∀ n ≥ n₀, 0 < Q.eval (n : ℚ))
    (hbound : ∀ n ≥ n₀,
      Q.eval (n : ℚ) ≤ P.eval (n : ℚ) ∧
      P.eval (n : ℚ) ≤ C * Q.eval (n : ℚ)) :
    P.degree = Q.degree ∧ 0 < P.leadingCoeff := by
  have hPpositive : ∀ n ≥ n₀, 0 < P.eval (n : ℚ) :=
    fun n hn ↦ (hQpositive n hn).trans_le (hbound n hn).1
  have hlower : ∀ᶠ n : ℕ in atTop, 1 ≤ P.eval (n : ℚ) / Q.eval (n : ℚ) := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    rw [le_div_iff₀ (hQpositive n hn), one_mul]
    exact (hbound n hn).1
  have hdegree : P.degree = Q.degree := by
    rcases lt_trichotomy P.degree Q.degree with hlt | heq | hgt
    · have hlimit : Tendsto (fun n : ℕ ↦ P.eval (n : ℚ) / Q.eval (n : ℚ))
          atTop (nhds 0) :=
        (Polynomial.div_tendsto_zero_of_degree_lt P Q hlt).comp tendsto_natCast_atTop_atTop
      have h := ge_of_tendsto hlimit hlower
      norm_num at h
    · exact heq
    · have hlimit : Tendsto (fun n : ℕ ↦ Q.eval (n : ℚ) / P.eval (n : ℚ))
          atTop (nhds 0) :=
        (Polynomial.div_tendsto_zero_of_degree_lt Q P hgt).comp tendsto_natCast_atTop_atTop
      have hC : Tendsto (fun n : ℕ ↦ C * (Q.eval (n : ℚ) / P.eval (n : ℚ)))
          atTop (nhds 0) := by
        simpa only [mul_zero] using tendsto_const_nhds.mul hlimit
      have hClower : ∀ᶠ n : ℕ in atTop,
          1 ≤ C * (Q.eval (n : ℚ) / P.eval (n : ℚ)) := by
        filter_upwards [eventually_ge_atTop n₀] with n hn
        rw [← mul_div_assoc, le_div_iff₀ (hPpositive n hn), one_mul]
        exact (hbound n hn).2
      have h := ge_of_tendsto hC hClower
      norm_num at h
  refine ⟨hdegree, ?_⟩
  have hlimit : Tendsto (fun n : ℕ ↦ P.eval (n : ℚ) / Q.eval (n : ℚ))
      atTop (nhds (P.leadingCoeff / Q.leadingCoeff)) :=
    (Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq P Q hdegree).comp
      tendsto_natCast_atTop_atTop
  have h := ge_of_tendsto hlimit hlower
  have hle : Q.leadingCoeff ≤ P.leadingCoeff := by
    simpa only [one_mul] using (le_div_iff₀ hQlc).mp h
  exact hQlc.trans_le hle

/-- The eventual normalization binomial bounds determine the precise
degree and positivity of any eventual Hilbert polynomial. -/
theorem polynomial_natDegree_eq_and_leadingCoeff_pos_of_binomial_squeeze
    (P : Polynomial ℚ) (r C n₀ : ℕ) (hr : 0 < r)
    (hbound : ∀ n ≥ n₀,
      ((r + n - 1).choose n : ℚ) ≤ P.eval (n : ℚ) ∧
      P.eval (n : ℚ) ≤ (C * (r + n - 1).choose n : ℕ)) :
    P.natDegree = r - 1 ∧ 0 < P.leadingCoeff := by
  let Q := Polynomial.preHilbertPoly ℚ (r - 1) 0
  have hQlc : 0 < Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_preHilbertPoly]
    positivity
  have hQeval (n : ℕ) : Q.eval (n : ℚ) = ((r + n - 1).choose n : ℚ) := by
    dsimp only [Q]
    rw [Polynomial.preHilbertPoly_eq_choose_sub_add ℚ (r - 1) (k := 0) (n := n) (by omega)]
    have hnr : n - 0 + (r - 1) = r + n - 1 := by omega
    rw [hnr, ← Nat.choose_symm (by omega : r - 1 ≤ r + n - 1)]
    congr 2
    omega
  have hQpositive : ∀ n ≥ n₀, 0 < Q.eval (n : ℚ) := by
    intro n _
    rw [hQeval]
    exact_mod_cast Nat.choose_pos (by omega : n ≤ r + n - 1)
  have hbound' : ∀ n ≥ n₀,
      Q.eval (n : ℚ) ≤ P.eval (n : ℚ) ∧
      P.eval (n : ℚ) ≤ (C : ℚ) * Q.eval (n : ℚ) := by
    intro n hn
    rw [hQeval]
    simpa only [Nat.cast_mul] using hbound n hn
  obtain ⟨hdegree, hpositive⟩ :=
    polynomial_degree_eq_and_leadingCoeff_pos_of_nat_squeeze
      P Q C n₀ hQlc hQpositive hbound'
  refine ⟨?_, hpositive⟩
  have hnat := Polynomial.natDegree_eq_of_degree_eq hdegree
  simpa only [Q, Polynomial.natDegree_preHilbertPoly] using hnat

/-- For a homogeneous quotient admitting a positive-parameter finite
linear normalization, the Hilbert polynomial exists and has exactly the
expected degree and positive leading coefficient. -/
theorem exists_homogeneousHilbertPolynomial_of_normalization
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (D : HomogeneousLinearNormalizationData I) (hr : 0 < D.parameterCount) :
    ∃ P : Polynomial ℚ, P.natDegree = D.parameterCount - 1 ∧
      0 < P.leadingCoeff ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (Module.finrank K (quotientHomogeneousComponent K σ I n) : ℚ) =
        P.eval (n : ℚ) := by
  obtain ⟨P, n₀, hP⟩ := exists_eventual_homogeneousHilbertPolynomial I hI
  obtain ⟨C, n₁, hbound⟩ := normalizationData_exists_homogeneousHilbert_squeeze I hI D hr
  obtain ⟨hdegree, hpositive⟩ :=
    polynomial_natDegree_eq_and_leadingCoeff_pos_of_binomial_squeeze
      P D.parameterCount C (max n₀ n₁) hr (by
        intro n hn
        rw [← hP n (by omega)]
        exact_mod_cast hbound n (by omega))
  exact ⟨P, hdegree, hpositive, n₀, hP⟩

end
end TranslatedDepthSeven
