import CubicTenVariables.PolynomialRootPrimeFactorization
import CubicTenVariables.SquarefreeResidueFactors
import CubicTenVariables.CubicResidueGcdBound

/-!
# Local factors indexed by the quotient modulus

The squarefree prescribed modulus consumes exactly one prime-power digit
at each of its primes. A consumed prime of total exponent one contributes
exactly one, so no counting constant is assigned to primes absent from c/d.
-/

noncomputable section
namespace CubicTenVariables.CubicPrimeFactorLocalBound
open MvPolynomial PolynomialRootPrimeFactorization SquarefreeResidueFactors

/-- Arithmetic assembly at one prime, from explicit unrestricted and
prime-class bounds. The final cubic endpoint below supplies both bounds. -/
theorem prime_factor_count_le
    (F : MvPolynomial (Fin 10) ℤ) (K c d : ℕ) (hc : 0 < c)
    (hd : Squarefree d) (hdc : d ∣ c) (k : Fin 10 → ℤ)
    (hk : (d : ℤ) ∣ eval k F) (p : ℕ) [Fact p.Prime]
    (hpc : p ∈ c.primeFactors)
    (hU : ∀ s : ℕ, count F k (p^s) 1 (one_dvd _) ≤ K*p^(9*s))
    (hL : (p : ℤ) ∣ eval k F → ∀ (r : ℕ) (hr : 2 ≤ r),
      count F k (p^r) p (dvd_pow_self p (by omega)) ≤
        K*(r-1)*p^(9*(r-1))*
          vectorGcd p (fun i => eval k (pderiv i F))*vectorGcd p k) :
    count F k (p ^ c.factorization p) ((p ^ c.factorization p).gcd d)
      (Nat.gcd_dvd_left _ _) ≤
        (if (c/d).factorization p = 0 then 1 else K*(c/d).factorization p) *
          p^(9*(c/d).factorization p) *
            (if p ∣ d2 c d then
              vectorGcd p (fun i => eval k (pderiv i F))*vectorGcd p k else 1) := by
  have hp : p.Prime := Fact.out
  have hr : 1 ≤ c.factorization p :=
    hp.factorization_pos_of_dvd hc.ne' (Nat.dvd_of_mem_primeFactors hpc)
  have hq := factorization_div_squarefree c d p hp hd hdc
  have hg := gcd_prime_pow_squarefree p hp (c.factorization p) hr d hd
  by_cases hpd : p ∣ d
  · have hpd' : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast hpd
    have hpk : (p : ℤ) ∣ eval k F := hpd'.trans hk
    simp only [if_pos hpd] at hq hg
    by_cases hr1 : c.factorization p = 1
    · have ha : (c/d).factorization p = 0 := by omega
      have hpd2 : ¬p ∣ d2 c d := by
        intro h
        have := ((prime_dvd_d2_iff c d p hc hd hdc hp).mp h).2
        omega
      have hcount : count F k (p ^ c.factorization p)
          ((p ^ c.factorization p).gcd d) (Nat.gcd_dvd_left _ _) = 1 := by
        simpa only [hr1, pow_one, Nat.gcd_eq_left_iff_dvd.mpr hpd] using
          count_full_residue F k p hpk
      simp [hcount, ha, hpd2]
    · have hr2 : 2 ≤ c.factorization p := by omega
      have ha' : c.factorization p - 1 ≠ 0 := by omega
      have hpd2 : p ∣ d2 c d :=
        (prime_dvd_d2_iff c d p hc hd hdc hp).mpr ⟨hpd,hr2⟩
      have hbound := hL hpk (c.factorization p) hr2
      simpa only [hg, hq, if_neg ha', if_pos hpd2, mul_assoc] using hbound
  · simp only [if_neg hpd, Nat.sub_zero] at hq hg
    have hr0 : c.factorization p ≠ 0 := by omega
    have hpd2 : ¬p ∣ d2 c d :=
      fun h => hpd ((prime_dvd_d2_iff c d p hc hd hdc hp).mp h).1
    have hK : K ≤ K*c.factorization p := by
      simpa only [mul_one] using Nat.mul_le_mul_left K hr
    have hbound := (hU (c.factorization p)).trans
      (Nat.mul_le_mul_right (p^(9*c.factorization p)) hK)
    simpa only [hg, hq, if_neg hr0, if_neg hpd2, mul_one] using hbound

/-- A common constant precedes every composite modulus and its prime
factors. Unrestricted and prime-class bounds and the squarefree arithmetic are supplied internally. -/
theorem exists_uniform_prime_factor_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (c d : ℕ) (_hc : 0 < c) (_hd : Squarefree d)
      (_hdc : d ∣ c) (k : Fin 10 → ℤ) (_hk : (d : ℤ) ∣ eval k F)
      (p : ℕ) (_hpc : p ∈ c.primeFactors),
        count F k (p ^ c.factorization p) ((p ^ c.factorization p).gcd d)
          (Nat.gcd_dvd_left _ _) ≤
            (if (c/d).factorization p = 0 then 1 else K*(c/d).factorization p) *
              p^(9*(c/d).factorization p) *
                (if p ∣ d2 c d then
                  vectorGcd p (fun i => eval k (pderiv i F))*vectorGcd p k else 1) := by
  obtain ⟨K,hK,hU,hL⟩ :=
    CubicResidueGcdBound.exists_uniform_local_gcd_bound  F hF hA
  refine ⟨K,hK,?_⟩
  intro c d hc hd hdc k hk p hpc
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpc
  letI : Fact p.Prime := ⟨hp⟩
  apply prime_factor_count_le F K c d hc hd hdc k hk p hpc
  · intro s
    rw [count_residue_one]
    exact hU p hp s
  · intro hpk r hr
    rw [count_prime_class F k p r (by omega)]
    exact hL p hp k hpk r hr

end CubicTenVariables.CubicPrimeFactorLocalBound
