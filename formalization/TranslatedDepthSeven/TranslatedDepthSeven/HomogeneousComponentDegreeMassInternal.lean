import TranslatedDepthSeven.HomogeneousComponentSeparatorsInternal
import TranslatedDepthSeven.ProjectiveDegreeOneSurfaceLinearInternal

/-!
# The sum of the degrees of top-dimensional prime components

The component-separating Hilbert injection is divided by the polynomial
`binomial(n+r,r)`. Each quotient tends to the relevant degree. Finite sums
commute with this limit, including the empty family and dimension zero.
Neither radicality nor reducedness of the containing ideal is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published Filter

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

universe u v

/-- After any fixed nonnegative shift, a Hilbert polynomial of dimension
`r` and degree `d`, divided by `binomial(n+r,r)`, tends to `d`. -/
theorem tendsto_projectiveHilbertPolynomial_div_binomial
    (P : Polynomial ℚ) (r d E : ℕ) (hd : 0 < d)
    (hdegree : P.natDegree = r)
    (hleading : P.leadingCoeff = (d : ℚ) / r.factorial) :
    Tendsto
      (fun n : ℕ ↦ P.eval ((n + E : ℕ) : ℚ) /
        (Polynomial.preHilbertPoly ℚ r 0).eval (n : ℚ))
      atTop (nhds (d : ℚ)) := by
  let S : Polynomial ℚ := P.comp (Polynomial.X + Polynomial.C (E : ℚ))
  let B : Polynomial ℚ := Polynomial.preHilbertPoly ℚ r 0
  have hlin : (Polynomial.X + Polynomial.C (E : ℚ)).natDegree = 1 :=
    Polynomial.natDegree_X_add_C _
  have hSdegree : S.natDegree = r := by
    simp only [S, Polynomial.natDegree_comp, hdegree, hlin, mul_one]
  have hBdegree : B.natDegree = r := Polynomial.natDegree_preHilbertPoly ℚ r 0
  have hSlc : S.leadingCoeff = (d : ℚ) / r.factorial := by
    dsimp only [S]
    rw [Polynomial.leadingCoeff_comp (by rw [hlin]; omega),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one, hleading]
  have hBlc : B.leadingCoeff = (r.factorial : ℚ)⁻¹ :=
    Polynomial.leadingCoeff_preHilbertPoly ℚ r 0
  have hfactorial : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hSne : S ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [hSlc]
    exact div_ne_zero (by exact_mod_cast hd.ne') hfactorial
  have hBne : B ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [hBlc]
    exact inv_ne_zero hfactorial
  have hdegrees : S.degree = B.degree := by
    rw [Polynomial.degree_eq_natDegree hSne, Polynomial.degree_eq_natDegree hBne,
      hSdegree, hBdegree]
  have hratio : S.leadingCoeff / B.leadingCoeff = (d : ℚ) := by
    rw [hSlc, hBlc]
    field_simp
  have hlimit : Tendsto (fun q : ℚ ↦ S.eval q / B.eval q) atTop (nhds (d : ℚ)) := by
    simpa only [hratio] using
      Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq S B hdegrees
  have hlimitN := hlimit.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℚ)) atTop atTop)
  simpa [S, B] using hlimitN

/-- A finite sum of Hilbert polynomials below one shifted Hilbert
polynomial has at most its total leading multiplicity. -/
theorem sum_degrees_le_of_shifted_hilbertPolynomial_comparison
    {ι : Type u} [Fintype ι]
    (P : ι → Polynomial ℚ) (Q : Polynomial ℚ)
    (r d E k₀ : ℕ) (di : ι → ℕ)
    (hd : 0 < d) (hdi : ∀ i, 0 < di i)
    (hPdegree : ∀ i, (P i).natDegree = r)
    (hPleading : ∀ i, (P i).leadingCoeff = (di i : ℚ) / r.factorial)
    (hQdegree : Q.natDegree = r)
    (hQleading : Q.leadingCoeff = (d : ℚ) / r.factorial)
    (hlower : ∀ n ≥ k₀,
      (∑ i, (P i).eval (n : ℚ)) ≤ Q.eval ((n + E : ℕ) : ℚ)) :
    ∑ i, di i ≤ d := by
  classical
  let B : Polynomial ℚ := Polynomial.preHilbertPoly ℚ r 0
  have hPi (i : ι) : Tendsto
      (fun n : ℕ ↦ (P i).eval (n : ℚ) / B.eval (n : ℚ))
      atTop (nhds (di i : ℚ)) := by
    simpa only [Nat.add_zero] using tendsto_projectiveHilbertPolynomial_div_binomial
      (P i) r (di i) 0 (hdi i) (hPdegree i) (hPleading i)
  have hsum : Tendsto
      (fun n : ℕ ↦ ∑ i, (P i).eval (n : ℚ) / B.eval (n : ℚ))
      atTop (nhds (∑ i, (di i : ℚ))) :=
    tendsto_finset_sum Finset.univ (fun i _ ↦ hPi i)
  have hQ := tendsto_projectiveHilbertPolynomial_div_binomial
    Q r d E hd hQdegree hQleading
  have hle : (∑ i, (di i : ℚ)) ≤ (d : ℚ) := by
    apply le_of_tendsto_of_tendsto hsum hQ
    filter_upwards [eventually_ge_atTop k₀] with n hn
    have hB : 0 < B.eval (n : ℚ) := by
      have heval : B.eval (n : ℚ) = ((n + r).choose r : ℚ) := by
        dsimp only [B]
        simpa using Polynomial.preHilbertPoly_eq_choose_sub_add ℚ r
          (k := 0) (n := n) (by omega)
      rw [heval]
      exact_mod_cast Nat.choose_pos (by omega : r ≤ n + r)
    rw [← Finset.sum_div]
    exact (div_le_div_iff_of_pos_right hB).mpr (hlower n hn)
  exact_mod_cast hle

/-- The degrees of finitely many distinct top-dimensional homogeneous
prime ideals containing `I` sum to at most its Hilbert degree.

The only datum required of `I` is the stated eventual homogeneous Hilbert
polynomial. In particular, the result does not assume that `I` is prime,
radical, reduced, or saturated. -/
theorem sum_projectiveDegrees_le_of_distinct_prime_components
    {K : Type u} [Field K] {N r d : ℕ}
    {ι : Type v} [Fintype ι]
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (P : ι → Ideal (MvPolynomial (Fin (N + 1)) K))
    (di : ι → ℕ) (hinjective : Function.Injective P)
    (hprime : ∀ i, (P i).IsPrime)
    (hhom : ∀ i, (P i).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K))
    (hdim : ∀ i, HasProjectiveDimensionDegree (P i) r (di i))
    (hcontain : ∀ i, I ≤ P i)
    (hI : HasProjectiveHilbertDimensionDegree I r d) :
    ∑ i, di i ≤ d := by
  classical
  obtain ⟨E, hbound⟩ := exists_shift_sum_finrank_homogeneousComponents_le
    I P di hinjective hprime hhom hdim hcontain
  obtain ⟨hd, Q, hQdegree, hQleading, k₀, hQeval⟩ := hI
  choose Pi hPdegree hPleading ki hPeval using fun i ↦ (hdim i).2.2
  let kbase : ℕ := max k₀ (Finset.univ.sup ki)
  apply sum_degrees_le_of_shifted_hilbertPolynomial_comparison
    Pi Q r d E kbase di hd (fun i ↦ (hdim i).2.1)
    hPdegree hPleading hQdegree hQleading
  intro n hn
  have hki (i : ι) : ki i ≤ n :=
    (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hn)
  have hkQ : k₀ ≤ n + E := by
    have hk : k₀ ≤ n := (le_max_left _ _).trans hn
    omega
  have hleft : (∑ i, (Pi i).eval (n : ℚ)) =
      ∑ i, (Module.finrank K (projectiveHilbertPiece K N (P i) n) : ℚ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hPeval i n (hki i)).symm
  rw [hleft, ← hQeval (n + E) hkQ]
  exact_mod_cast hbound n

end

end TranslatedDepthSeven
