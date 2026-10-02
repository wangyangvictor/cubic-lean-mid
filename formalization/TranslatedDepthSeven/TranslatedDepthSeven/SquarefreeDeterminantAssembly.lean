import TranslatedDepthSeven.ColumnwiseDeterminantBound
import TranslatedDepthSeven.TangentMinors

/-!
# Square-free assembly of local determinant divisibilities

This file separates the elementary global arithmetic in the several-prime
determinant method.  Equal prime-power divisibilities combine to a power of
the square-free modulus.  If that divisor exceeds the columnwise
archimedean bound, the determinant is zero.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

/-- Prime powers with the same exponent multiply without loss over a
square-free modulus. -/
theorem squarefreePower_dvd_of_primePower_dvd
    {q r : ℕ} {a : ℤ} (hq : Squarefree q)
    (hlocal : ∀ p, p.Prime → p ∣ q → (p : ℤ) ^ r ∣ a) :
    (q : ℤ) ^ r ∣ a := by
  let f : ℕ → ℤ := fun p ↦ (p : ℤ) ^ r
  have hpair : (q.primeFactors : Set ℕ).Pairwise
      (Function.onFun IsCoprime f) := by
    intro p hpMem p' hp'Mem hne
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hp' : p'.Prime := Nat.prime_of_mem_primeFactors hp'Mem
    have hcop : p.Coprime p' := (Nat.coprime_primes hp hp').2 hne
    exact (Nat.Coprime.pow r r hcop).isCoprime
  have heach : ∀ p ∈ q.primeFactors, f p ∣ a := by
    intro p hpMem
    exact hlocal p (Nat.prime_of_mem_primeFactors hpMem)
      (Nat.dvd_of_mem_primeFactors hpMem)
  have hprod : (∏ p ∈ q.primeFactors, f p) ∣ a :=
    Finset.prod_dvd_of_coprime hpair heach
  have hprodEq : ∏ p ∈ q.primeFactors, f p = (q : ℤ) ^ r := by
    change (∏ p ∈ q.primeFactors, (p : ℤ) ^ r) = (q : ℤ) ^ r
    rw [Finset.prod_pow]
    congr 1
    simpa only [Nat.cast_prod] using congrArg (fun m : ℕ ↦ (m : ℤ))
      (Nat.prod_primeFactors_of_squarefree hq)
  rwa [hprodEq] at hprod

/-- Local prime-power divisibility plus a strictly smaller columnwise
archimedean bound forces the integral determinant to vanish. -/
theorem det_eq_zero_of_squarefree_local_divisibility_and_column_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (C : ι → ℕ) (q r : ℕ)
    (hq : Squarefree q)
    (hlocal : ∀ p, p.Prime → p ∣ q → (p : ℤ) ^ r ∣ A.det)
    (hentry : ∀ i j, (A i j).natAbs ≤ C j)
    (hlarge : (Fintype.card ι).factorial * ∏ j, C j < q ^ r) :
    A.det = 0 := by
  have hdiv : (q : ℤ) ^ r ∣ A.det :=
    squarefreePower_dvd_of_primePower_dvd hq hlocal
  apply TangentMinors.eq_zero_of_dvd_of_natAbs_lt hdiv
  have hbound :
      A.det.natAbs ≤ (Fintype.card ι).factorial * ∏ j, C j :=
    det_natAbs_le_factorial_mul_prod_column_bounds A C hentry
  simpa using hbound.trans_lt hlarge

end

end TranslatedDepthSeven
