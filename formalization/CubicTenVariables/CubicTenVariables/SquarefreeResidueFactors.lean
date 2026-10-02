import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# The squarefree factors and vector gcds in the composite residue bound

The source factor `d1` is the product of the primes dividing `d` whose
valuation in `c` is exactly one; it is unrelated to any exceptional-prime
integer. Its complementary factor `d2` is proved equal to `gcd d (c/d)`.
Vector gcds use the actual greatest common divisor of the absolute values
of the integer coordinates, including the all-zero and empty vectors.
-/

namespace CubicTenVariables.SquarefreeResidueFactors
open scoped BigOperators

/-- The literal filtered prime product in the manuscript's definition. -/
def d1 (c d : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors.filter (fun p => c.factorization p = 1), p

/-- The manuscript's complementary squarefree factor. -/
def d2 (c d : ℕ) : ℕ := d / d1 c d

/-- Nonnegative content of an actual integer vector. -/
def content {n : ℕ} (v : Fin n → ℤ) : ℕ :=
  Finset.univ.gcd (fun i => (v i).natAbs)

/-- The positive vector gcd when the scalar modulus is positive. -/
def vectorGcd {n : ℕ} (e : ℕ) (v : Fin n → ℤ) : ℕ :=
  Nat.gcd e (content v)

/-- Divisibility of content is exactly coordinatewise integer divisibility;
neither primality nor a nonzero coordinate is required. -/
theorem dvd_content_iff {n : ℕ} (a : ℕ) (v : Fin n → ℤ) :
    a ∣ content v ↔ ∀ i, (a : ℤ) ∣ v i := by
  simp only [content, Finset.dvd_gcd_iff, Finset.mem_univ, forall_const,
    Int.natCast_dvd]

@[simp] theorem content_zero (n : ℕ) : content (0 : Fin n → ℤ) = 0 := by
  apply Finset.gcd_eq_zero_iff.mpr
  intro i hi
  simp

@[simp] theorem vectorGcd_zero (e n : ℕ) : vectorGcd e (0 : Fin n → ℤ) = e := by
  simp [vectorGcd]

theorem vectorGcd_pos {n : ℕ} (e : ℕ) (he : 0 < e) (v : Fin n → ℤ) :
    0 < vectorGcd e v := Nat.gcd_pos_of_pos_left _ he

/-- At a prime, the vector gcd is the prime precisely when every coordinate
is divisible by it, and is otherwise one. -/
theorem vectorGcd_prime {n : ℕ} (p : ℕ) (hp : p.Prime) (v : Fin n → ℤ) :
    vectorGcd p v = if ∀ i, (p : ℤ) ∣ v i then p else 1 := by
  unfold vectorGcd
  by_cases h : ∀ i, (p : ℤ) ∣ v i
  · rw [if_pos h]
    exact Nat.gcd_eq_left_iff_dvd.mpr ((dvd_content_iff p v).mpr h)
  · rw [if_neg h]
    exact (hp.coprime_iff_not_dvd.mpr (fun hd => h ((dvd_content_iff p v).mp hd))).gcd_eq_one

private theorem gcd_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (a : ℕ) :
    Nat.gcd (∏ p ∈ s, p) a = ∏ p ∈ s, Nat.gcd p a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hp (hs' q hq)).mpr
      exact fun h => hps (h ▸ hq)
    rw [Finset.prod_insert hps, Finset.prod_insert hps, hcop.mul_gcd, ih hs']

/-- The product of local vector gcds equals the literal global vector gcd.
The proof remains valid when every coordinate is zero. -/
theorem prod_primeFactors_vectorGcd {n : ℕ} (e : ℕ) (he : Squarefree e)
    (v : Fin n → ℤ) :
    (∏ p ∈ e.primeFactors, vectorGcd p v) = vectorGcd e v := by
  simpa only [vectorGcd, Nat.prod_primeFactors_of_squarefree he] using
    (gcd_prod_primes e.primeFactors
      (fun _ hp => Nat.prime_of_mem_primeFactors hp) (content v)).symm

/-- A squarefree second argument removes all higher prime-power gcd depth. -/
theorem gcd_prime_pow_squarefree (p : ℕ) (hp : p.Prime) (r : ℕ) (hr : 1 ≤ r)
    (d : ℕ) (hd : Squarefree d) :
    Nat.gcd (p^r) d = if p ∣ d then p else 1 := by
  have hg : Nat.gcd (p^r) d = Nat.gcd p d := by
    apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd
      · exact ((hd.squarefree_of_dvd (Nat.gcd_dvd_right (p^r) d)).dvd_pow_iff_dvd
          (by omega : r ≠ 0)).mp (Nat.gcd_dvd_left (p^r) d)
      · exact Nat.gcd_dvd_right (p^r) d
    · exact Nat.dvd_gcd
        ((Nat.gcd_dvd_left p d).trans (dvd_pow_self p (by omega)))
        (Nat.gcd_dvd_right p d)
  rw [hg]
  by_cases hpd : p ∣ d
  · rw [if_pos hpd]
    exact Nat.gcd_eq_left_iff_dvd.mpr hpd
  · rw [if_neg hpd]
    exact (hp.coprime_iff_not_dvd.mpr hpd).gcd_eq_one

/-- Prime valuations in the quotient by a squarefree divisor. -/
theorem factorization_div_squarefree (c d p : ℕ) (hp : p.Prime)
    (hd : Squarefree d) (hdc : d ∣ c) :
    (c/d).factorization p = c.factorization p - if p ∣ d then 1 else 0 := by
  rw [Nat.factorization_div hdc, Finsupp.tsub_apply]
  congr 1
  by_cases hpd : p ∣ d
  · rw [if_pos hpd]
    exact Nat.factorization_eq_one_of_squarefree hd hp hpd
  · rw [if_neg hpd]
    exact Nat.factorization_eq_zero_of_not_dvd hpd

/-- The quotient is positive under the manuscript's divisor hypotheses. -/
theorem quotient_pos (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    0 < c/d := Nat.div_pos (Nat.le_of_dvd hc hdc) (Nat.pos_of_ne_zero hd.ne_zero)

/-- Among the primes dividing d, those occurring to exponent one in c
are exactly the primes absent from c/d. -/
theorem factorization_eq_one_iff_not_dvd_quotient (c d p : ℕ)
    (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c)
    (hp : p.Prime) (hpd : p ∣ d) :
    c.factorization p = 1 ↔ ¬ p ∣ c/d := by
  have hcp : 1 ≤ c.factorization p :=
    (hp.dvd_iff_one_le_factorization hc.ne').mp (hpd.trans hdc)
  rw [hp.dvd_iff_one_le_factorization (quotient_pos c d hc hd hdc).ne',
    factorization_div_squarefree c d p hp hd hdc, if_pos hpd]
  omega

/-- The filtered definition of d1 agrees with the complement of the gcd. -/
theorem d1_eq_div_gcd (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    d1 c d = d / Nat.gcd d (c/d) := by
  have hm : c/d ≠ 0 := (quotient_pos c d hc hd hdc).ne'
  have hfilter : d.primeFactors.filter (fun p => c.factorization p = 1) =
      d.primeFactors \ (c/d).primeFactors := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hpd,hval⟩
      refine ⟨hpd, ?_⟩
      intro hpm
      exact (factorization_eq_one_iff_not_dvd_quotient c d p hc hd hdc
        (Nat.prime_of_mem_primeFactors hpd) (Nat.dvd_of_mem_primeFactors hpd)).mp hval
          (Nat.dvd_of_mem_primeFactors hpm)
    · rintro ⟨hpd,hpm⟩
      refine ⟨hpd, ?_⟩
      apply (factorization_eq_one_iff_not_dvd_quotient c d p hc hd hdc
        (Nat.prime_of_mem_primeFactors hpd) (Nat.dvd_of_mem_primeFactors hpd)).mpr
      intro hpdiv
      exact hpm ((Nat.mem_primeFactors_of_ne_zero hm).mpr
        ⟨Nat.prime_of_mem_primeFactors hpd, hpdiv⟩)
  rw [d1, hfilter, ← Nat.primeFactors_div_gcd hd hm]
  exact Nat.prod_primeFactors_of_squarefree
    (hd.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d (c/d))))

/-- The manuscript's d2 is exactly gcd(d,c/d), with no exceptional-prime
integer entering its definition. -/
theorem d2_eq_gcd (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    d2 c d = Nat.gcd d (c/d) := by
  rw [d2, d1_eq_div_gcd c d hc hd hdc]
  exact Nat.div_div_self (Nat.gcd_dvd_left d (c/d)) hd.ne_zero

theorem d2_squarefree (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    Squarefree (d2 c d) := by
  rw [d2_eq_gcd c d hc hd hdc]
  exact hd.squarefree_of_dvd (Nat.gcd_dvd_left d (c/d))

theorem d2_pos (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    0 < d2 c d := by
  rw [d2_eq_gcd c d hc hd hdc]
  exact Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hd.ne_zero)

theorem d2_dvd_left (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    d2 c d ∣ d := by
  rw [d2_eq_gcd c d hc hd hdc]
  exact Nat.gcd_dvd_left d (c/d)

theorem d2_dvd_quotient (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    d2 c d ∣ c/d := by
  rw [d2_eq_gcd c d hc hd hdc]
  exact Nat.gcd_dvd_right d (c/d)

/-- Precisely the prescribed prime classes with at least two ambient
prime-power digits contribute to d2. -/
theorem prime_dvd_d2_iff (c d p : ℕ) (hc : 0 < c) (hd : Squarefree d)
    (hdc : d ∣ c) (hp : p.Prime) :
    p ∣ d2 c d ↔ p ∣ d ∧ 2 ≤ c.factorization p := by
  rw [d2_eq_gcd c d hc hd hdc, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨hpd,hpm⟩
    refine ⟨hpd, ?_⟩
    rw [hp.dvd_iff_one_le_factorization (quotient_pos c d hc hd hdc).ne',
      factorization_div_squarefree c d p hp hd hdc, if_pos hpd] at hpm
    omega
  · rintro ⟨hpd,hval⟩
    refine ⟨hpd, ?_⟩
    rw [hp.dvd_iff_one_le_factorization (quotient_pos c d hc hd hdc).ne',
      factorization_div_squarefree c d p hp hd hdc, if_pos hpd]
    omega

theorem d2_primeFactors (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    (d2 c d).primeFactors = d.primeFactors ∩ (c/d).primeFactors := by
  rw [d2_eq_gcd c d hc hd hdc]
  exact Nat.primeFactors_gcd hd.ne_zero (quotient_pos c d hc hd hdc).ne'

/-- The local vector factors indexed by the quotient's primes assemble to
the source's vector gcd at d2. Primes not dividing d contribute one. -/
theorem prod_quotient_primeFactors_vectorGcd {n : ℕ} (c d : ℕ) (hc : 0 < c)
    (hd : Squarefree d) (hdc : d ∣ c) (v : Fin n → ℤ) :
    (∏ p ∈ (c/d).primeFactors, if p ∣ d then vectorGcd p v else 1) =
      vectorGcd (d2 c d) v := by
  classical
  have hf : (c/d).primeFactors.filter (fun p => p ∣ d) = (d2 c d).primeFactors := by
    rw [d2_primeFactors c d hc hd hdc]
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hpm,hpd⟩
      exact ⟨(Nat.mem_primeFactors_of_ne_zero hd.ne_zero).mpr
        ⟨Nat.prime_of_mem_primeFactors hpm,hpd⟩,hpm⟩
    · rintro ⟨hpd,hpm⟩
      exact ⟨hpm,Nat.dvd_of_mem_primeFactors hpd⟩
  rw [← Finset.prod_filter, hf]
  exact prod_primeFactors_vectorGcd _ (d2_squarefree c d hc hd hdc) v

end CubicTenVariables.SquarefreeResidueFactors
