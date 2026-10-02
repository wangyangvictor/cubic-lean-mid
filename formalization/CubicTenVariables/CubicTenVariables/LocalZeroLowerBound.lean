import CubicTenVariables.IntegralZeroPatch
import CubicTenVariables.LocalZeroResidues
import CubicTenVariables.NormalizedLocalCounts
import CubicTenVariables.PrimeLocalizationData

/-!
# Actual local zeros and an eventual positive normalized lower bound

An integral smooth zero supplies sufficiently many distinct residues of
actual integral zeros in any prescribed congruence coset. The same lower
bound holds for the ordinary modular zero count and on the constructed
unit orbit. No convergence of normalized counts or Euler-factor identity
is asserted. The local theorem requires neither cubic homogeneity nor a
unit derivative, and adds no premise to the existing prime-local data.
-/

noncomputable section
namespace CubicTenVariables.LocalZeroLowerBound

open MvPolynomial PadicUnitOrbit LocalZeroResidues NormalizedLocalCounts
open Filter
open scoped Topology

variable (p : ℕ) [Fact p.Prime] {m : ℕ}

theorem exists_actual_zero_lower_bound_of_contains_coset
    (F : MvPolynomial (Fin (m + 1)) ℤ) (i : Fin (m + 1))
    (ξ : Fin (m + 1) → ℤ_[p])
    (hzero : eval₂ (Int.castRingHom ℚ_[p]) (fun j => (ξ j : ℚ_[p])) F = 0)
    (hpartial : eval₂ (Int.castRingHom ℚ_[p]) (fun j => (ξ j : ℚ_[p])) (pderiv i F) ≠ 0)
    (M : ℕ) (B : Set (Fin (m + 1) → ℤ_[p])) (hB : coset p ξ M ⊆ B) :
    ∃ K : ℕ, max M 1 ≤ K ∧ ∀ s, K ≤ s →
      p ^ ((s - K) * m) ≤ Nat.card (actualZeroResidues p F B s) := by
  obtain ⟨K, hK, hpatch⟩ :=
    IntegralZeroPatch.exists_integral_zero_patch p F i ξ hzero hpartial M
  refine ⟨K, hK, ?_⟩
  intro s hs
  apply card_actualZeroResidues_ge_of_parameter_surjection p F B i ξ K ?_ s hs
  intro y hy
  obtain ⟨z, hz, hFz, hzy⟩ := hpatch y hy
  exact ⟨z, hB hz, hFz, hzy⟩

theorem exists_coset_actual_zero_lower_bound
    (F : MvPolynomial (Fin (m + 1)) ℤ) (i : Fin (m + 1))
    (ξ : Fin (m + 1) → ℤ_[p])
    (hzero : eval₂ (Int.castRingHom ℚ_[p]) (fun j => (ξ j : ℚ_[p])) F = 0)
    (hpartial : eval₂ (Int.castRingHom ℚ_[p]) (fun j => (ξ j : ℚ_[p])) (pderiv i F) ≠ 0)
    (M : ℕ) :
    ∃ K : ℕ, max M 1 ≤ K ∧ ∀ s, K ≤ s →
      p ^ ((s - K) * m) ≤ Nat.card (actualZeroResidues p F (coset p ξ M) s) :=
  exists_actual_zero_lower_bound_of_contains_coset p F i ξ hzero hpartial M _ Set.Subset.rfl

theorem exists_coset_modular_zero_filter_lower_bound
    (F : MvPolynomial (Fin (m + 1)) ℤ) (i : Fin (m + 1))
    (ξ : Fin (m + 1) → ℤ_[p])
    (hzero : eval₂ (Int.castRingHom ℚ_[p]) (fun j => (ξ j : ℚ_[p])) F = 0)
    (hpartial : eval₂ (Int.castRingHom ℚ_[p]) (fun j => (ξ j : ℚ_[p])) (pderiv i F) ≠ 0)
    (M : ℕ) :
    ∃ K : ℕ, max M 1 ≤ K ∧ ∀ s, ∀ hKs : K ≤ s, ∀ hMs : M ≤ s,
      p ^ ((s - K) * m) ≤ (modularZeroCosetFilter p F ξ M s hMs).card := by
  obtain ⟨K, hK, hcount⟩ := exists_coset_actual_zero_lower_bound p F i ξ hzero hpartial M
  refine ⟨K, hK, ?_⟩
  intro s hs hMs
  rw [card_modularZeroCosetFilter_eq]
  exact (hcount s hs).trans (card_actualZeroResidues_le_modularZeroResidues p F _ s)

end CubicTenVariables.LocalZeroLowerBound

namespace CubicTenVariables.PrimeLocalizationData

open MvPolynomial PadicUnitOrbit LocalZeroResidues NormalizedLocalCounts
open Filter
open scoped Topology

variable {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 10) ℤ}

/-- The actual chosen unit orbit contains many residues of exact integral
zeros, with one exponent K fixed before the modulus. -/
theorem exists_actual_zero_lower_bound (D : PrimeLocalizationData p F) :
    ∃ K : ℕ, max D.modulusExponent 1 ≤ K ∧ ∀ s, K ≤ s →
      p ^ ((s - K) * 9) ≤
        Nat.card (actualZeroResidues p F (unitOrbit p D.center D.modulusExponent) s) :=
  LocalZeroLowerBound.exists_actual_zero_lower_bound_of_contains_coset p F D.partialIndex
    D.center D.center_zero D.partial_ne_zero D.modulusExponent _
    (coset_subset_unitOrbit p D.center D.modulusExponent)

theorem exists_modular_zero_lower_bound (D : PrimeLocalizationData p F) :
    ∃ K : ℕ, max D.modulusExponent 1 ≤ K ∧ ∀ s, K ≤ s →
      p ^ ((s - K) * 9) ≤
        Nat.card (modularZeroResidues p F (unitOrbit p D.center D.modulusExponent) s) := by
  obtain ⟨K, hK, hc⟩ := D.exists_actual_zero_lower_bound
  exact ⟨K, hK, fun s hs => (hc s hs).trans
    (card_actualZeroResidues_le_modularZeroResidues p F _ s)⟩

/-- Positive eventual lower bound for the literal modular-zero counts,
normalized by p^(9s). This does not assert that they converge. -/
theorem exists_positive_normalized_zero_lower_bound (D : PrimeLocalizationData p F) :
    ∃ K : ℕ, max D.modulusExponent 1 ≤ K ∧
      0 < ((p : ℝ) ^ (K * 9))⁻¹ ∧
      ∀ᶠ s : ℕ in atTop, ((p : ℝ) ^ (K * 9))⁻¹ ≤
        normalizedCount p 9
          (fun t => Nat.card (modularZeroResidues p F
            (unitOrbit p D.center D.modulusExponent) t)) s := by
  obtain ⟨K, hK, hc⟩ := D.exists_modular_zero_lower_bound
  exact ⟨K, hK, positive_eventual_normalized_lower_bound p 9 K
    (Fact.out : p.Prime).pos _ hc⟩

theorem modular_zero_density_pos_of_tendsto (D : PrimeLocalizationData p F)
    (L : ℝ) (hL : Tendsto (normalizedCount p 9
      (fun t => Nat.card (modularZeroResidues p F
        (unitOrbit p D.center D.modulusExponent) t))) atTop (𝓝 L)) : 0 < L := by
  obtain ⟨K, _, hc⟩ := D.exists_modular_zero_lower_bound
  exact normalized_limit_pos p 9 K (Fact.out : p.Prime).pos _ hc L hL

end CubicTenVariables.PrimeLocalizationData
