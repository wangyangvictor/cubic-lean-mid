import CubicTenVariables.PrimeLocalizationMultiplicativity

/-! Exact prime support of the actual finite localization modulus. Positive
local exponents ensure that no selected prime disappears from the product. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables
open MvPolynomial
open scoped BigOperators Classical

namespace LocalizedFinitePrimeAssembly

theorem primeFactors_modulus (s : Finset ℕ) (M : ℕ → ℕ)
    (hprimes : ∀ p ∈ s, p.Prime) (hM : ∀ p ∈ s, 1 ≤ M p) :
    (modulus s M).primeFactors = s := by
  have hW : modulus s M ≠ 0 := Nat.ne_of_gt (modulus_pos s M hprimes)
  ext p
  constructor
  · intro hp
    obtain ⟨hpp,hpW,_⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨r,hrs,hpr⟩ := (hpp.prime.dvd_finset_prod_iff (fun r => r^(M r))).mp hpW
    have hpr' : p ∣ r := hpp.dvd_of_dvd_pow hpr
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hpp (hprimes r hrs)).mp hpr'
    exact heq ▸ hrs
  · intro hp
    apply Nat.mem_primeFactors.mpr
    refine ⟨hprimes p hp,?_,hW⟩
    apply (show p ∣ p^(M p) by simpa only [pow_one] using pow_dvd_pow p (hM p hp)).trans
    exact primePower_dvd_modulus s M p hp

end LocalizedFinitePrimeAssembly

namespace PrimeLocalizationSeries
variable {F : MvPolynomial (Fin 10) ℤ}

theorem primeFactors_modulus (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F) :
    (modulus s hprimes D).primeFactors = s := by
  apply LocalizedFinitePrimeAssembly.primeFactors_modulus s
    (exponent s hprimes D) hprimes
  intro p hp
  rw [exponent_of_mem s hprimes D p hp]
  exact @PrimeLocalizationData.modulus_positive p ⟨hprimes p hp⟩ F (D p hp)

/-- Support on the chosen finite set is exactly the source condition
that every prime divisor of q divides the actual localization modulus. -/
theorem primeFactors_subset_iff (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (q : ℕ) (hq : q ≠ 0) :
    q.primeFactors ⊆ s ↔
      ∀ p : ℕ, p.Prime → p ∣ q → p ∣ modulus s hprimes D := by
  constructor
  · intro hs p hp hpq
    have hps := hs (Nat.mem_primeFactors.mpr ⟨hp,hpq,hq⟩)
    rw [←primeFactors_modulus s hprimes D] at hps
    exact Nat.dvd_of_mem_primeFactors hps
  · intro hs p hpq
    obtain ⟨hp,hpq',_⟩ := Nat.mem_primeFactors.mp hpq
    rw [←primeFactors_modulus s hprimes D]
    exact Nat.mem_primeFactors.mpr
      ⟨hp,hs p hp hpq',Nat.ne_of_gt (modulus_pos s hprimes D)⟩

/-- Literal source formulation: the product is over exactly the primes
dividing the chosen W, retaining the local factor at exponent zero. -/
theorem complete_sum_factorization_over_primeFactors (hF : F.IsHomogeneous 3)
    (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (q : ℕ) (hq : q ≠ 0)
    (hs : q.primeFactors ⊆ (modulus s hprimes D).primeFactors) (v : Fin 10 → ℤ) :
    localizedCompleteCubicSum F q (modulus s hprimes D) (restriction s hprimes D) v =
      ∏ p ∈ (modulus s hprimes D).primeFactors,
        localizedCompleteCubicSum F (p^(q.factorization p))
          (p^(exponent s hprimes D p)) (localResidues s hprimes D p) v := by
  rw [primeFactors_modulus s hprimes D] at hs ⊢
  apply LocalizedRestrictedMultiplicativity.localized_factorization F hF q hq s hs
    (exponent s hprimes D) (localResidues s hprimes D) hprimes
  intro p hp
  letI : Fact p.Prime := ⟨hprimes p hp⟩
  exact (congrArg (fun spec : Σ M : ℕ, Set (Fin 10 → ZMod (p^M)) =>
    ResidueUnitInvariant spec.2) (localSpecification_of_mem s hprimes D p hp)).mpr
      (D p hp).residueSet_unitInvariant

end PrimeLocalizationSeries
end CubicTenVariables
