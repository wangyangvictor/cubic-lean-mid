import CubicTenVariables.PrimeLocalizationFactor
import CubicTenVariables.WeightedResidueMaximum
import CubicTenVariables.LocalizedFrequencyComparison
import Mathlib.Topology.Order.LiminfLimsup

/-! Uniform bounds for the literal restricted root count, and elementary
weighted bounds that retain the full least-common-multiple normalization. -/
noncomputable section
namespace CubicTenVariables
open MvPolynomial LocalizedRootSeriesIdentity PrimePowerFibers
open LocalZeroResidues PadicUnitOrbit NormalizedLocalCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PrimeLocalizationData
variable {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 10) ℤ}

theorem rootCountAt_eq_modularZeroResidues (D : PrimeLocalizationData p F)
    (a : ℕ) (hMa : D.modulusExponent ≤ a) :
    rootCountAt F p D.modulusExponent a a D.residueSet =
      Nat.card (modularZeroResidues p F (unitOrbit p D.center D.modulusExponent) a) := by
  rw [rootCountAt_eq_filter F p D.modulusExponent a a D.residueSet hMa le_rfl,
    D.modularZeroResidues_eq_restricted a hMa]
  simp only [reduction, ZMod.castHom_self, RingHom.id_apply, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Set.mem_setOf_eq]

/-- The supplied orbit has a uniform root-count bound. This is deduced
from the already proved stabilization of its actual density. -/
theorem exists_rootCountAt_bound (D : PrimeLocalizationData p F)
    (hF : F.IsHomogeneous 3) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℕ, D.modulusExponent ≤ a →
      (rootCountAt F p D.modulusExponent a a D.residueSet : ℝ) ≤ C * (p : ℝ)^(9*a) := by
  obtain ⟨L,_,_,hlim⟩ := D.exists_positive_normalized_root_limit hF
  obtain ⟨B,hB⟩ := hlim.bddAbove_range
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro a hMa
  have ha := hB (Set.mem_range_self a)
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [D.rootCountAt_eq_modularZeroResidues a hMa]
  have hb : normalizedCount p 9 (fun t => Nat.card (modularZeroResidues p F
      (unitOrbit p D.center D.modulusExponent) t)) a ≤ max 1 B :=
    ha.trans (le_max_right _ _)
  dsimp only [normalizedCount] at hb
  have := (div_le_iff₀ (pow_pos hp (a*9))).mp hb
  simpa only [Nat.mul_comm a 9] using this
end PrimeLocalizationData

namespace WeightedResidueMaximum
variable {n : ℕ}

/-- The total finite weighted mass is the sum of its actual residue-class masses. -/
theorem sum_classWeight (A : ℕ) [NeZero A] (V : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ) :
    (∑ k : Fin n → ZMod A, classWeight A V w k) = ∑ v ∈ V, w v := by
  simp only [classWeight,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp

/-- Works also for signed weights; nonnegativity is only needed when
multiplying this inequality by later bounds. -/
theorem total_mass_le (A : ℕ) [NeZero A] (V : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ) :
    (∑ v ∈ V, w v) ≤ (A : ℝ)^n * maximum A V w := by
  rw [←sum_classWeight A V w]
  calc
    _ ≤ ∑ _k : Fin n → ZMod A, maximum A V w :=
      Finset.sum_le_sum fun k _ => classWeight_le_maximum A V w k
    _ = _ := by simp
end WeightedResidueMaximum

namespace LocalizedFrequencyComparison
variable {n : ℕ}

/-- The elementary weighted estimate uses lcm(q,W), also when q is smaller
than the fixed localization modulus. -/
theorem weighted_trivial_bound (F : MvPolynomial (Fin n) ℤ)
    (q W A : ℕ) (hq : 0 < q) (hW : 0 < W) [NeZero A]
    (Ω : Set (Fin n → ZMod W)) (V : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ) (hw : ∀ v ∈ V, 0 ≤ w v) :
    (∑ v ∈ V, w v * ‖localizedCompleteCubicSum F q W Ω v‖) ≤
      ((q : ℝ)*(Nat.lcm q W : ℝ)^n*(A : ℝ)^n) *
        WeightedResidueMaximum.maximum A V w := by
  calc
    _ ≤ ∑ v ∈ V, w v * ((q : ℝ)*(Nat.lcm q W : ℝ)^n) :=
      Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left
        (trivial_bound F q W hq hW Ω v) (hw v hv)
    _ = ((q : ℝ)*(Nat.lcm q W : ℝ)^n) * ∑ v ∈ V, w v := by
      rw [Finset.mul_sum]; congr 1; ext v; ring
    _ ≤ ((q : ℝ)*(Nat.lcm q W : ℝ)^n) *
        ((A : ℝ)^n * WeightedResidueMaximum.maximum A V w) :=
      mul_le_mul_of_nonneg_left (WeightedResidueMaximum.total_mass_le A V w) (by positivity)
    _ = _ := by ring
end LocalizedFrequencyComparison
end CubicTenVariables
