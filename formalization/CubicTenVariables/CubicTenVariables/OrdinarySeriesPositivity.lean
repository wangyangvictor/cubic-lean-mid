import CubicTenVariables.OrdinarySeriesMultiplicativity
import CubicTenVariables.OrdinaryLocalSeriesFactor
import CubicTenVariables.Literature.Bernert
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Positivity of the actual ordinary singular series from absolute
prime-power summability and strictly positive local factors. This is an
Euler-product argument and assumes no cubic point-count theorem. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OrdinarySeriesPositivity
open scoped BigOperators Topology
open Filter OrdinaryLocalSeriesFactor

theorem of_localFactors {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (hconv : SingularSeriesAbsolutelyConvergent F)
    (hprime : Summable (fun pk : Nat.Primes × ℕ =>
      ‖singularSeriesTerm F (pk.1.val ^ (pk.2+1))‖))
    (hpos : ∀ p : Nat.Primes, 0 < (localFactor F p.val).re) :
    Literature.PositiveRealSingularSeries F := by
  classical
  let L : Nat.Primes → ℂ := fun p => localFactor F p.val
  have hreal (p : Nat.Primes) : L p = ((L p).re : ℂ) := by
    letI : Fact p.val.Prime := ⟨p.property⟩
    exact localFactor_eq_ofReal F hn hconv p.val
  have hsplit := (summable_prod_of_nonneg (fun pk : Nat.Primes × ℕ =>
    norm_nonneg (singularSeriesTerm F (pk.1.val ^ (pk.2+1))))).mp hprime
  have htail (p : Nat.Primes) : L p - 1 =
      ∑' k : ℕ, singularSeriesTerm F (p.val^(k+1)) := by
    have h := (summable_norm_prime_power F hconv p.val p.property).of_norm.tsum_eq_zero_add
    dsimp [L, localFactor]
    rw [h]
    simp only [pow_zero, singularSeriesTerm_one]
    ring
  have hsmall : Summable (fun p => ‖L p - 1‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by rw [htail]; exact norm_tsum_le_tsum_norm (hsplit.1 p)) hsplit.2
  have hprod : HasProd L (singularSeries F) :=
    EulerProduct.eulerProduct_hasProd (by simp)
      (fun {a b} h => OrdinarySeriesMultiplicativity.mul F a b h) hconv (by simp)
  have hne : singularSeries F ≠ 0 := by
    rw [← hprod.tprod_eq]
    have hcancel (z : ℂ) : 1 + (z - 1) = z := by ring
    have h := tprod_one_add_ne_zero_of_summable
      (f := fun p : Nat.Primes => L p - 1)
      (fun p => by
        simp only [hcancel]
        intro hp
        have := hpos p
        change 0 < (L p).re at this
        rw [hp] at this
        simp at this) hsmall
    simpa only [hcancel] using h
  have hfinite (s : Finset Nat.Primes) :
      (∏ p ∈ s, L p) = ((∏ p ∈ s, (L p).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun p _ => hreal p)
  have hre : Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, (L p).re)
      atTop (𝓝 (singularSeries F).re) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hprod
    simpa only [Function.comp_def, hfinite, Complex.ofReal_re] using h
  have hnonneg : 0 ≤ (singularSeries F).re :=
    ge_of_tendsto hre (Eventually.of_forall fun s =>
      Finset.prod_nonneg (fun p _ => (hpos p).le))
  have hrealSum : singularSeries F = ((singularSeries F).re : ℂ) := by
    apply tendsto_nhds_unique hprod
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
    simpa only [Function.comp_def, ← hfinite] using h
  refine ⟨(singularSeries F).re, lt_of_le_of_ne hnonneg ?_, hrealSum⟩
  intro hz
  apply hne
  rw [hrealSum, ← hz]
  simp

end CubicTenVariables.OrdinarySeriesPositivity
