import CubicTenVariables.PlanAlphaModulusDecomposition
import CubicTenVariables.LocalizedCompositeMajorant
import CubicTenVariables.PlanAlphaParameterRatios
import CubicTenVariables.PrimeLocalizationPrimeSupport

/-! Arithmetic eligibility of the canonical factors of an actual modulus.
The excluded set, localization data, exceptional integer, and prime cutoff
are explicit. No analytic estimate or literature input is used here. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaFactorEligibility
open PlanAlphaModulusDecomposition
open CubeFullSmithParameters (A)
variable {F : MvPolynomial (Fin 10) ℤ}

/-- The cube-free factor avoids every positive integer supported on the
excluded primes. -/
theorem d_coprime_supported (s : Finset ℕ) (q N : ℕ) (hN : 0 < N)
    (hs : N.primeFactors ⊆ s) : (d s q).Coprime N := by
  apply (Nat.disjoint_primeFactors (d_pos s q).ne' hN.ne').mp
  exact Finset.disjoint_left.mpr (fun p hp hN =>
    Finset.disjoint_left.mp (d_disjoint s q) hp (hs hN))

/-- The cube-full factor avoids every positive integer supported on the
excluded primes. -/
theorem r_coprime_supported (s : Finset ℕ) (q N : ℕ) (hN : 0 < N)
    (hs : N.primeFactors ⊆ s) : (r s q).Coprime N := by
  apply (Nat.disjoint_primeFactors (r_pos s q).ne' hN.ne').mp
  exact Finset.disjoint_left.mpr (fun p hp hN =>
    Finset.disjoint_left.mp (r_disjoint s q) hp (hs hN))

/-- Putting all smaller primes into the excluded set forces the actual
cube-full factor to satisfy the cutoff in the Smith-moment estimate. -/
theorem r_prime_cutoff (s : Finset ℕ) (q p₀ : ℕ)
    (hsmall : ∀ p : ℕ, p.Prime → p < p₀ → p ∈ s) :
    ∀ p ∈ (r s q).primeFactors, p₀ ≤ p := by
  intro p hp
  by_contra hn
  have hps := hsmall p (Nat.prime_of_mem_primeFactors hp) (by omega)
  exact Finset.disjoint_left.mp (r_disjoint s q) hp hps

/-- The actual localization modulus can accompany the excluded factor
in the coprime factorization separating the cube-full factor. -/
theorem gW_coprime_r (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (q : ℕ) :
    (g s q * PrimeLocalizationSeries.modulus s hprimes D).Coprime (r s q) := by
  apply Nat.coprime_mul_iff_left.mpr
  refine ⟨coprime_g_r s q,?_⟩
  apply Nat.Coprime.symm
  apply r_coprime_supported s q _ (PrimeLocalizationSeries.modulus_pos s hprimes D)
  rw [PrimeLocalizationSeries.primeFactors_modulus s hprimes D]

/-- The actual localization modulus can also accompany both fixed
factors in the coprime factorization separating the cube-free factor. -/
theorem grW_coprime_d (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (q : ℕ) :
    ((g s q * r s q) * PrimeLocalizationSeries.modulus s hprimes D).Coprime
      (d s q) := by
  apply Nat.coprime_mul_iff_left.mpr
  refine ⟨Nat.coprime_mul_iff_left.mpr
    ⟨coprime_g_d s q,(coprime_d_r s q).symm⟩,?_⟩
  apply Nat.Coprime.symm
  apply d_coprime_supported s q _ (PrimeLocalizationSeries.modulus_pos s hprimes D)
  rw [PrimeLocalizationSeries.primeFactors_modulus s hprimes D]

/-- The two residue moduli divide their respective canonical factors. -/
theorem residue_moduli_dvd_factors (s : Finset ℕ) (q : ℕ) :
    LocalizedCompositeMajorant.modulus s (g s q) ∣ g s q ∧ A (r s q) ∣ r s q :=
  ⟨LocalizedCompositeMajorant.modulus_dvd s (g s q) (g_pos s q) (g_supported s q),
    PlanAlphaParameterRatios.A_dvd (r s q) (r_pos s q)⟩

/-- The actual residue moduli can be combined by the coprime CRT. -/
theorem residue_moduli_coprime (s : Finset ℕ) (q : ℕ) :
    (LocalizedCompositeMajorant.modulus s (g s q)).Coprime (A (r s q)) :=
  Nat.Coprime.of_dvd (residue_moduli_dvd_factors s q).1
    (residue_moduli_dvd_factors s q).2 (coprime_g_r s q)

/-- The cube-free factor satisfies the full exceptional-modulus
coprimality needed by the weighted cube-free estimate. -/
theorem d_coprime_residue_moduli_mul (s : Finset ℕ) (q N : ℕ) (hN : 1 ≤ N)
    (hs : N.primeFactors ⊆ s) :
    (d s q).Coprime
      ((LocalizedCompositeMajorant.modulus s (g s q) * A (r s q)) * N) := by
  apply Nat.coprime_mul_iff_right.mpr
  refine ⟨Nat.coprime_mul_iff_right.mpr ⟨?_,?_⟩,
    d_coprime_supported s q N hN hs⟩
  · exact Nat.Coprime.of_dvd_right (residue_moduli_dvd_factors s q).1
      (coprime_g_d s q).symm
  · exact Nat.Coprime.of_dvd_right (residue_moduli_dvd_factors s q).2
      (coprime_d_r s q)

/-- The product of the actual residue moduli divides the original
positive modulus. -/
theorem residue_moduli_dvd (s : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    LocalizedCompositeMajorant.modulus s (g s q) * A (r s q) ∣ q := by
  apply (mul_dvd_mul (residue_moduli_dvd_factors s q).1
    (residue_moduli_dvd_factors s q).2).trans
  refine ⟨d s q,?_⟩
  calc
    q = g s q*d s q*r s q := reconstruction s q hq
    _ = _ := by ring

theorem residue_moduli_le (s : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    LocalizedCompositeMajorant.modulus s (g s q) * A (r s q) ≤ q :=
  Nat.le_of_dvd hq (residue_moduli_dvd s q hq)

/-- All additional arithmetic conditions for applying the fixed-factor
and Smith-majorant estimates to the canonical split of an actual q. -/
theorem eligibility (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (D : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F)
    (N p₀ : ℕ) (hN : 1 ≤ N) (hsN : N.primeFactors ⊆ s)
    (hsmall : ∀ p : ℕ, p.Prime → p < p₀ → p ∈ s) (q : ℕ) (hq : 0 < q) :
    (∀ p ∈ (r s q).primeFactors, p₀ ≤ p) ∧
    (g s q * PrimeLocalizationSeries.modulus s hprimes D).Coprime (r s q) ∧
    ((g s q * r s q) * PrimeLocalizationSeries.modulus s hprimes D).Coprime (d s q) ∧
    (d s q).Coprime
      ((LocalizedCompositeMajorant.modulus s (g s q) * A (r s q)) * N) ∧
    (LocalizedCompositeMajorant.modulus s (g s q)).Coprime (A (r s q)) ∧
    LocalizedCompositeMajorant.modulus s (g s q) * A (r s q) ∣ q ∧
    LocalizedCompositeMajorant.modulus s (g s q) * A (r s q) ≤ q :=
  ⟨r_prime_cutoff s q p₀ hsmall,gW_coprime_r s hprimes D q,
    grW_coprime_d s hprimes D q,d_coprime_residue_moduli_mul s q N hN hsN,
    residue_moduli_coprime s q,residue_moduli_dvd s q hq,residue_moduli_le s q hq⟩

end CubicTenVariables.PlanAlphaFactorEligibility
