import CubicTenVariables.OrdinaryLocalSeriesFactor
import CubicTenVariables.LocalZeroLowerBound

/-! Supplied local geometric data give strict positivity of the ordinary
Euler factor once the ordinary series is absolutely convergent. Restricted
modular roots are included in the unrestricted root count. No local-solubility
literature premise, homogeneity hypothesis or global product positivity is used.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OrdinaryLocalFactorPositivity
open MvPolynomial LocalZeroResidues PrimePowerRootSeriesIdentity
open OrdinaryLocalSeriesFactor NormalizedLocalCounts PadicUnitOrbit

/-- Forgetting the lift restriction embeds the selected modular zeros into
the literal unrestricted modular root set, at every exponent including zero. -/
theorem card_restricted_le_rootCount {n : ℕ} (p : ℕ) [Fact p.Prime]
    (F : MvPolynomial (Fin n) ℤ) (B : Set (Fin n → ℤ_[p])) (s : ℕ) :
    Nat.card (modularZeroResidues p F B s) ≤ rootCount F p s := by
  classical
  have h : Nat.card (modularZeroResidues p F B s) ≤
      Nat.card {x : Fin n → ZMod (p^s) //
        eval₂ (Int.castRingHom (ZMod (p^s))) x F = 0} :=
    Set.ncard_le_ncard (fun _ hx => hx.1)
  simpa only [rootCount,Nat.card_eq_fintype_card,Fintype.card_subtype] using h

/-- The ordinary local factor is strictly positive at the given prime.
The supplied data are at that prime; no good-characteristic restriction is
required, and the polynomial need not be homogeneous. -/
theorem localFactor_re_pos {p : ℕ} [Fact p.Prime]
    {F : MvPolynomial (Fin 10) ℤ} (D : PrimeLocalizationData p F)
    (hconv : SingularSeriesAbsolutelyConvergent F) :
    0 < (localFactor F p).re := by
  obtain ⟨K,_,hK⟩ := D.exists_modular_zero_lower_bound
  refine normalized_limit_pos p 9 K (Fact.out : p.Prime).pos
    (fun s => rootCount F p s) ?_ (localFactor F p).re ?_
  · intro s hs
    exact (hK s hs).trans
      (card_restricted_le_rootCount p F (unitOrbit p D.center D.modulusExponent) s)
  · simpa only [normalizedCount,rootDensity] using
      rootDensity_tendsto F (by decide) hconv p

/-- The same actual ordinary prime-power sum is a positive real number;
both strict positivity and the absence of an imaginary part are conclusions. -/
theorem exists_positive_localFactor {p : ℕ} [Fact p.Prime]
    {F : MvPolynomial (Fin 10) ℤ} (D : PrimeLocalizationData p F)
    (hconv : SingularSeriesAbsolutelyConvergent F) :
    ∃ L : ℝ, 0 < L ∧
      (∑' k : ℕ, singularSeriesTerm F (p^k)) = (L : ℂ) :=
  ⟨(localFactor F p).re,localFactor_re_pos D hconv,
    localFactor_eq_ofReal F (by decide) hconv p⟩

end CubicTenVariables.OrdinaryLocalFactorPositivity
