import TranslatedDepthSeven.ComparablePrimePool
import TranslatedDepthSeven.PrimeReservoir

/-!
# Identification of the comparable-prime candidate sets

The finite combinatorics in `ComparablePrimePool` is independent of the
prime-number theorem.  This file makes the extensional identification with
the interval set used by `PrimeReservoir`.
-/

namespace TranslatedDepthSeven

/-- The two concrete descriptions of the primes in
`(floor x, floor (2x)]` are extensionally equal. -/
theorem comparablePrimeCandidates_eq_dyadicPrimes (x : ℝ) :
    comparablePrimeCandidates x = dyadicPrimes x := by
  ext p
  rw [mem_comparablePrimeCandidates_iff, mem_dyadicPrimes]

end TranslatedDepthSeven
