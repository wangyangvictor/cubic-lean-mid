import TranslatedDepthSeven.FiniteEquationComponentLabel
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Literal frontiers of distinct minimal-prime components

If `P` and `Q` are distinct minimal primes over one ideal, their intersection
as closed sets is defined by `P ⊔ Q`, which strictly contains both `P` and
`Q`.  This file records the corresponding statement for every minimal prime
over `P ⊔ Q`.  It also specializes the result to the finite component lists
through an affine point.

The final lemmas express the standard dimension drop without introducing a
geometric dimension interface.  They use only the literal Krull dimensions
of quotient rings and Mathlib's order-theoretic coheight.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open Order

universe u v

variable {R : Type u} [CommRing R]

/-- For a prime ideal, the Krull dimension of its quotient is its coheight in
the prime spectrum. -/
theorem ringKrullDim_quotient_prime_eq_coheight
    (P : Ideal R) [P.IsPrime] :
    ringKrullDim (R ⧸ P) =
      (Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  congr 1

/-- Strict inclusion of prime ideals gives strict dimension drop between the
corresponding irreducible closed sets, provided the lower prime has finite
coheight. -/
theorem ringKrullDim_quotient_lt_of_prime_lt
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P < Q)
    (hfinite : ringKrullDim (R ⧸ P) < ⊤) :
    ringKrullDim (R ⧸ Q) < ringKrullDim (R ⧸ P) := by
  have hPfinite : Order.coheight
      (⟨P, inferInstance⟩ : PrimeSpectrum R) < ⊤ := by
    rw [ringKrullDim_quotient_prime_eq_coheight P] at hfinite
    exact WithBot.coe_lt_coe.mp hfinite
  have hQfinite : Order.coheight
      (⟨Q, inferInstance⟩ : PrimeSpectrum R) < ⊤ :=
    lt_of_le_of_lt
      (Order.coheight_anti (show
        (⟨P, inferInstance⟩ : PrimeSpectrum R) ≤
          ⟨Q, inferInstance⟩ from hPQ.le))
      hPfinite
  rw [ringKrullDim_quotient_prime_eq_coheight Q,
    ringKrullDim_quotient_prime_eq_coheight P]
  exact_mod_cast Order.coheight_strictAnti (show
    (⟨P, inferInstance⟩ : PrimeSpectrum R) <
      ⟨Q, inferInstance⟩ from hPQ) hQfinite

/-- Distinct prime ideals whose quotient rings have the same finite Krull
dimension are incomparable.  No hypothesis that the primes arise from the
same equation family is needed. -/
theorem incomparable_of_distinct_primes_same_finite_quotient_dimension
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] {s : ℕ}
    (hne : P ≠ Q)
    (hPdim : ringKrullDim (R ⧸ P) = s)
    (hQdim : ringKrullDim (R ⧸ Q) = s) :
    (¬ P ≤ Q) ∧ (¬ Q ≤ P) := by
  have hPfinite : ringKrullDim (R ⧸ P) < ⊤ := by
    rw [hPdim]
    change (↑(s : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top s)
  have hQfinite : ringKrullDim (R ⧸ Q) < ⊤ := by
    rw [hQdim]
    change (↑(s : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top s)
  constructor
  · intro hPQ
    have hPQ' : P < Q := lt_of_le_of_ne hPQ hne
    have hdrop :=
      ringKrullDim_quotient_lt_of_prime_lt P Q hPQ' hPfinite
    rw [hPdim, hQdim] at hdrop
    exact (lt_irrefl _ hdrop)
  · intro hQP
    have hQP' : Q < P := lt_of_le_of_ne hQP hne.symm
    have hdrop :=
      ringKrullDim_quotient_lt_of_prime_lt Q P hQP' hQfinite
    rw [hPdim, hQdim] at hdrop
    exact (lt_irrefl _ hdrop)

variable [IsNoetherianRing R]

/-- A minimal prime over the supremum of two distinct equal-dimensional
prime ideals strictly contains each of them.  The two primes may come from
different finite equation families. -/
theorem lt_frontierMinimalPrime_of_distinct_primes_same_dimension
    {P Q L : Ideal R} [P.IsPrime] [Q.IsPrime] {s : ℕ}
    (hne : P ≠ Q)
    (hPdim : ringKrullDim (R ⧸ P) = s)
    (hQdim : ringKrullDim (R ⧸ Q) = s)
    (hL : L ∈ finiteMinimalPrimes (P ⊔ Q)) :
    P < L ∧ Q < L := by
  have hincomparable :=
    incomparable_of_distinct_primes_same_finite_quotient_dimension
      P Q hne hPdim hQdim
  have hsupL : P ⊔ Q ≤ L := le_of_mem_finiteMinimalPrimes hL
  constructor
  · refine lt_of_le_not_ge (le_sup_left.trans hsupL) ?_
    intro hLP
    exact hincomparable.2 (le_sup_right.trans (hsupL.trans hLP))
  · refine lt_of_le_not_ge (le_sup_right.trans hsupL) ?_
    intro hLQ
    exact hincomparable.1 (le_sup_left.trans (hsupL.trans hLQ))

/-- Complete equal-dimensional frontier statement: the original primes are
incomparable, every displayed minimal frontier prime strictly contains both,
and its quotient dimension is strictly smaller. -/
theorem strict_frontier_and_dimension_drop_of_distinct_primes_same_dimension
    {P Q L : Ideal R} [P.IsPrime] [Q.IsPrime] {s : ℕ}
    (hne : P ≠ Q)
    (hPdim : ringKrullDim (R ⧸ P) = s)
    (hQdim : ringKrullDim (R ⧸ Q) = s)
    (hL : L ∈ finiteMinimalPrimes (P ⊔ Q)) :
    (¬ P ≤ Q) ∧ (¬ Q ≤ P) ∧ P < L ∧ Q < L ∧
      ringKrullDim (R ⧸ L) < s := by
  letI : L.IsPrime := isPrime_of_mem_finiteMinimalPrimes hL
  have hincomparable :=
    incomparable_of_distinct_primes_same_finite_quotient_dimension
      P Q hne hPdim hQdim
  have hstrict :=
    lt_frontierMinimalPrime_of_distinct_primes_same_dimension
      hne hPdim hQdim hL
  have hPfinite : ringKrullDim (R ⧸ P) < ⊤ := by
    rw [hPdim]
    change (↑(s : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top s)
  have hdrop :=
    ringKrullDim_quotient_lt_of_prime_lt P L hstrict.1 hPfinite
  rw [hPdim] at hdrop
  exact ⟨hincomparable.1, hincomparable.2, hstrict.1, hstrict.2, hdrop⟩

/-- Every minimal prime over the supremum of two distinct minimal components
strictly contains both component ideals. -/
theorem lt_frontierMinimalPrime_of_distinct_finiteMinimalPrimes
    {I P Q L : Ideal R}
    (hP : P ∈ finiteMinimalPrimes I)
    (hQ : Q ∈ finiteMinimalPrimes I)
    (hne : P ≠ Q)
    (hL : L ∈ finiteMinimalPrimes (P ⊔ Q)) :
    P < L ∧ Q < L := by
  have hintersection := lt_sup_of_distinct_finiteMinimalPrimes hP hQ hne
  have hsupL : P ⊔ Q ≤ L := le_of_mem_finiteMinimalPrimes hL
  exact ⟨hintersection.1.trans_le hsupL,
    hintersection.2.trans_le hsupL⟩

/-- If a prime `T` contains two distinct minimal components, one of the
finitely many minimal primes over their supremum lies below `T`, and that
prime strictly contains both component ideals. -/
theorem exists_strict_frontierMinimalPrime_le
    {I P Q T : Ideal R} [T.IsPrime]
    (hP : P ∈ finiteMinimalPrimes I)
    (hQ : Q ∈ finiteMinimalPrimes I)
    (hne : P ≠ Q)
    (hPT : P ≤ T) (hQT : Q ≤ T) :
    ∃ L ∈ finiteMinimalPrimes (P ⊔ Q),
      P < L ∧ Q < L ∧ L ≤ T := by
  obtain ⟨L, hL, hLT⟩ :=
    exists_finiteMinimalPrime_le (I := P ⊔ Q) (P := T) (sup_le hPT hQT)
  exact ⟨L, hL,
    (lt_frontierMinimalPrime_of_distinct_finiteMinimalPrimes
      hP hQ hne hL).1,
    (lt_frontierMinimalPrime_of_distinct_finiteMinimalPrimes
      hP hQ hne hL).2,
    hLT⟩

/-- Each irreducible component of the literal frontier has smaller Krull
dimension than either finite-dimensional original component. -/
theorem ringKrullDim_frontier_lt_of_distinct_finiteMinimalPrimes
    {I P Q L : Ideal R}
    (hP : P ∈ finiteMinimalPrimes I)
    (hQ : Q ∈ finiteMinimalPrimes I)
    (hne : P ≠ Q)
    (hL : L ∈ finiteMinimalPrimes (P ⊔ Q))
    (hPfinite : ringKrullDim (R ⧸ P) < ⊤)
    (hQfinite : ringKrullDim (R ⧸ Q) < ⊤) :
    ringKrullDim (R ⧸ L) < ringKrullDim (R ⧸ P) ∧
      ringKrullDim (R ⧸ L) < ringKrullDim (R ⧸ Q) := by
  letI : P.IsPrime := isPrime_of_mem_finiteMinimalPrimes hP
  letI : Q.IsPrime := isPrime_of_mem_finiteMinimalPrimes hQ
  letI : L.IsPrime := isPrime_of_mem_finiteMinimalPrimes hL
  have hstrict :=
    lt_frontierMinimalPrime_of_distinct_finiteMinimalPrimes hP hQ hne hL
  exact ⟨ringKrullDim_quotient_lt_of_prime_lt P L hstrict.1 hPfinite,
    ringKrullDim_quotient_lt_of_prime_lt Q L hstrict.2 hQfinite⟩

/-- Numerical form used in a dimension induction: if one original component
has the literal finite dimension `s`, every minimal component of its frontier
with a distinct component has dimension strictly below `s`. -/
theorem ringKrullDim_frontier_lt_nat_of_distinct_finiteMinimalPrimes
    {I P Q L : Ideal R} {s : ℕ}
    (hP : P ∈ finiteMinimalPrimes I)
    (hQ : Q ∈ finiteMinimalPrimes I)
    (hne : P ≠ Q)
    (hL : L ∈ finiteMinimalPrimes (P ⊔ Q))
    (hPdim : ringKrullDim (R ⧸ P) = s) :
    ringKrullDim (R ⧸ L) < s := by
  letI : P.IsPrime := isPrime_of_mem_finiteMinimalPrimes hP
  letI : L.IsPrime := isPrime_of_mem_finiteMinimalPrimes hL
  have hPL :=
    (lt_frontierMinimalPrime_of_distinct_finiteMinimalPrimes
      hP hQ hne hL).1
  have hPfinite : ringKrullDim (R ⧸ P) < ⊤ := by
    rw [hPdim]
    change (↑(s : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top s)
  have hdrop :=
    ringKrullDim_quotient_lt_of_prime_lt P L hPL hPfinite
  rwa [hPdim] at hdrop

variable {K : Type u} {σ : Type v} [Field K] [Fintype σ]

/-- If two distinct members of the finite component list pass through an
affine point, the point lies on one of the finitely many strict frontier
components over their supremum. -/
theorem exists_strict_frontierMinimalPrime_through_affinePoint
    (equations : Finset (MvPolynomial σ K)) (z : σ → K)
    {P Q : Ideal (MvPolynomial σ K)}
    (hP : P ∈ finiteEquationComponentsThroughPoint equations z)
    (hQ : Q ∈ finiteEquationComponentsThroughPoint equations z)
    (hne : P ≠ Q) :
    ∃ L ∈ finiteMinimalPrimes (P ⊔ Q),
      P < L ∧ Q < L ∧
        L ≤ RingHom.ker (MvPolynomial.eval z) := by
  have hPspec :=
    (mem_finiteEquationComponentsThroughPoint_iff equations z P).mp hP
  have hQspec :=
    (mem_finiteEquationComponentsThroughPoint_iff equations z Q).mp hQ
  let T : Ideal (MvPolynomial σ K) :=
    RingHom.ker (MvPolynomial.eval z)
  letI : T.IsPrime := RingHom.ker_isPrime (MvPolynomial.eval z)
  exact exists_strict_frontierMinimalPrime_le
    hPspec.1 hQspec.1 hne hPspec.2 hQspec.2

end

end TranslatedDepthSeven
