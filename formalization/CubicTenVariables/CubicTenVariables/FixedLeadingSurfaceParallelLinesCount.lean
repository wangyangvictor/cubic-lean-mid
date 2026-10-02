import CubicTenVariables.FixedLeadingSurfaceParallelLines
import TranslatedDepthSeven.PerfectFieldPolynomialKrullDimension

/-!
# A uniform count of rational parallel lines

For an irreducible affine surface depending on the chosen line coordinate,
the coefficient locus has only maximal-ideal components. Its rational
points therefore inject into its components, and the proved component
Bézout bound gives at most `d²` parallel lines. The dependence on the
chosen coordinate is an explicit hypothesis here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceParallelLines

open MvPolynomial TranslatedDepthSeven

section PerfectField

variable {K : Type*} [Field K] [PerfectField K]

/-- Every prime containing all coefficient equations is maximal. A prime
element in a nonzero such prime ideal either divides every coefficient,
or supplies a strict chain of length two below it. The first possibility
contradicts irreducibility and directional dependence; the second forces
maximality because the transverse polynomial ring has dimension two. -/
theorem isMaximal_of_contains_coefficients
    (g : MvPolynomial (Fin 3) K) (hg : Irreducible g)
    (hdir : 0 < g.degreeOf 0)
    (P : Ideal (MvPolynomial (Fin 2) K)) (hP : P.IsPrime)
    (hcoeff : ∀ i, (MvPolynomial.finSuccEquiv K 2 g).coeff i ∈ P) :
    P.IsMaximal := by
  letI : P.IsPrime := hP
  letI : (⊥ : Ideal (MvPolynomial (Fin 2) K)).IsPrime := Ideal.bot_prime
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hz : MvPolynomial.finSuccEquiv K 2 g = 0 := by
      apply Polynomial.ext
      intro i
      simpa only [hbot, Ideal.mem_bot, Polynomial.coeff_zero] using hcoeff i
    exact hg.ne_zero ((MvPolynomial.finSuccEquiv K 2).injective (by simpa using hz))
  obtain ⟨q, hqP, hqprime⟩ := hP.exists_mem_prime_of_ne_bot hPne
  let Q : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {q}
  have hQprime : Q.IsPrime := (Ideal.span_singleton_prime hqprime.ne_zero).mpr hqprime
  letI : Q.IsPrime := hQprime
  have hQP : Q ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqP)
  have hQPne : Q ≠ P := by
    intro heq
    apply hqprime.not_unit
    apply isUnit_of_dvd_all_coefficients g hg hdir q
    intro i
    apply Ideal.mem_span_singleton.mp
    change (MvPolynomial.finSuccEquiv K 2 g).coeff i ∈ Q
    rw [heq]
    exact hcoeff i
  have hQPstrict : Q < P := lt_of_le_of_ne hQP hQPne
  have hbotQ : (⊥ : Ideal (MvPolynomial (Fin 2) K)) < Q :=
    bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr hqprime.ne_zero)
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hP.ne_top
  letI : M.IsMaximal := hM
  have heq : P = M := by
    by_contra hne
    have hPMstrict : P < M := lt_of_le_of_ne hPM hne
    have hQ1 : (1 : ℕ∞) ≤ Q.primeHeight := by
      calc
        (1 : ℕ∞) = 0 + 1 := by simp
        _ ≤ (⊥ : Ideal (MvPolynomial (Fin 2) K)).primeHeight + 1 :=
          add_le_add (zero_le _) le_rfl
        _ ≤ Q.primeHeight := Ideal.primeHeight_add_one_le_of_lt hbotQ
    have hP2 : (2 : ℕ∞) ≤ P.primeHeight := by
      calc
        (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ Q.primeHeight + 1 := add_le_add hQ1 le_rfl
        _ ≤ P.primeHeight := Ideal.primeHeight_add_one_le_of_lt hQPstrict
    have hM3 : (3 : ℕ∞) ≤ M.primeHeight := by
      calc
        (3 : ℕ∞) = 2 + 1 := by norm_num
        _ ≤ P.primeHeight + 1 := add_le_add hP2 le_rfl
        _ ≤ M.primeHeight := Ideal.primeHeight_add_one_le_of_lt hPMstrict
    have hM2 : M.primeHeight ≤ 2 := by
      rw [← Ideal.height_eq_primeHeight]
      exact mvPolynomial_maximal_height_le_of_perfectField K 2 M
    have hfalse := hM3.trans hM2
    norm_num at hfalse
  simpa only [heq] using hM

theorem isMaximal_of_contains_coefficientIdeal
    (g : MvPolynomial (Fin 3) K) (hg : Irreducible g)
    (hdir : 0 < g.degreeOf 0)
    (P : Ideal (MvPolynomial (Fin 2) K)) (hP : P.IsPrime)
    (hIP : finiteEquationIdeal (coefficientEquations g) ≤ P) : P.IsMaximal := by
  classical
  apply isMaximal_of_contains_coefficients g hg hdir P hP
  intro i
  by_cases hi : i < g.totalDegree + 1
  · exact hIP (Ideal.subset_span
      (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩))
  · rw [coefficient_eq_zero_of_totalDegree_lt g (by omega)]
    exact P.zero_mem

end PerfectField

section Rational

/-- Different transverse points give different evaluation kernels. -/
theorem eval_kernel_injective {n : ℕ} :
    Function.Injective (fun a : Fin n → ℚ ↦ RingHom.ker (eval a)) := by
  intro a b hab
  change RingHom.ker (eval a) = RingHom.ker (eval b) at hab
  funext i
  have hmem : X i - C (a i) ∈ RingHom.ker (eval a) := by
    simp only [RingHom.mem_ker, map_sub, eval_X, eval_C, sub_self]
  rw [hab] at hmem
  have hzero : b i - a i = 0 := by
    simpa only [RingHom.mem_ker, map_sub, eval_X, eval_C] using hmem
  exact (sub_eq_zero.mp hzero).symm

/-- The kernel attached to a parallel line is one of the finitely many
minimal components of the actual coefficient equations. -/
theorem eval_kernel_mem_coefficientMinimalPrimes
    (g : MvPolynomial (Fin 3) ℚ) (hg : Irreducible g)
    (hdir : 0 < g.degreeOf 0) (a : Fin 2 → ℚ)
    (ha : lineRestriction g a = 0) :
    RingHom.ker (eval a) ∈ finiteMinimalPrimes
      (finiteEquationIdeal (coefficientEquations g)) := by
  classical
  have hz := (lineRestriction_eq_zero_iff_mem_coefficientLocus g a).mp ha
  have hI : finiteEquationIdeal (coefficientEquations g) ≤ RingHom.ker (eval a) := by
    apply Ideal.span_le.mpr
    intro f hf
    exact RingHom.mem_ker.mpr (hz f hf)
  obtain ⟨P, hP, hPa⟩ := exists_finiteMinimalPrime_le hI
  have hPmax := isMaximal_of_contains_coefficientIdeal g hg hdir P
    (isPrime_of_mem_finiteMinimalPrimes hP) (le_of_mem_finiteMinimalPrimes hP)
  have heq : P = RingHom.ker (eval a) := hPmax.eq_of_le (RingHom.ker_ne_top _) hPa
  rwa [← heq]

/-- Any finite set of distinct rational lines in the first coordinate
direction on an irreducible degree-at-most-`d` surface has size at most
`d²`, provided the surface depends on that coordinate. -/
theorem rational_parallel_lines_card_le
    {d : ℕ} (hd : 1 ≤ d) (g : MvPolynomial (Fin 3) ℚ)
    (hdegree : g.totalDegree ≤ d) (hg : Irreducible g)
    (hdir : 0 < g.degreeOf 0)
    (S : Finset (Fin 2 → ℚ)) (hS : ∀ a ∈ S, lineRestriction g a = 0) :
    S.card ≤ d ^ 2 := by
  apply (Finset.card_le_card_of_injOn
    (fun a : Fin 2 → ℚ ↦ RingHom.ker (eval a))
    (fun a ha ↦ eval_kernel_mem_coefficientMinimalPrimes g hg hdir a (hS a ha))
    eval_kernel_injective.injOn).trans
  exact rational_coefficientLocus_component_card_le hd g hdegree

theorem rational_parallel_lines_card_le_of_irreducible_top
    {d : ℕ} (hd : 1 ≤ d) (g : MvPolynomial (Fin 3) ℚ)
    (hdegree : g.totalDegree ≤ d)
    (htop : Irreducible (homogeneousComponent g.totalDegree g))
    (hdir : 0 < g.degreeOf 0)
    (S : Finset (Fin 2 → ℚ)) (hS : ∀ a ∈ S, lineRestriction g a = 0) :
    S.card ≤ d ^ 2 :=
  rational_parallel_lines_card_le hd g hdegree
    (IrreducibleFromTopHomogeneousPart.irreducible_of_irreducible_topComponent g htop)
    hdir S hS

end Rational
end CubicTenVariables.FixedLeadingSurfaceParallelLines
