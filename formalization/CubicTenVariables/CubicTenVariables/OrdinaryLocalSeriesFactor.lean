import CubicTenVariables.PrimePowerRootSeriesIdentity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Complex.Basic

/-!
# Ordinary local factors from literal root counts

Absolute convergence of the actual ordinary singular series implies that
each prime-power subseries converges to a nonnegative real number. The proof
uses the already proved finite root-count identity; neither multiplicativity
nor a local or global positivity theorem is assumed. The polynomial is unchanged.
-/

noncomputable section
namespace CubicTenVariables.OrdinaryLocalSeriesFactor

open MvPolynomial Filter
open scoped BigOperators Topology

variable {n : ℕ}

def localFactor (F : MvPolynomial (Fin n) ℤ) (p : ℕ) : ℂ :=
  ∑' e : ℕ, singularSeriesTerm F (p ^ e)

def rootDensity (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (s : ℕ) : ℝ :=
  (PrimePowerRootSeriesIdentity.rootCount F p s : ℝ) / (p : ℝ) ^ (s * (n - 1))

theorem summable_norm_prime_power (F : MvPolynomial (Fin n) ℤ)
    (hconv : SingularSeriesAbsolutelyConvergent F) (p : ℕ) (hp : p.Prime) :
    Summable (fun e : ℕ => ‖singularSeriesTerm F (p ^ e)‖) :=
  hconv.comp_injective (Nat.pow_right_injective hp.two_le)

theorem rootDensity_tendsto_complex (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (hconv : SingularSeriesAbsolutelyConvergent F) (p : ℕ) [Fact p.Prime] :
    Tendsto (fun s => (rootDensity F p s : ℂ)) atTop (𝓝 (localFactor F p)) := by
  have h := (summable_norm_prime_power F hconv p Fact.out).of_norm.hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  have hid (s : ℕ) : (rootDensity F p s : ℂ) =
      ∑ e ∈ Finset.range (s + 1), singularSeriesTerm F (p ^ e) := by
    simpa only [rootDensity, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_pow] using PrimePowerRootSeriesIdentity.root_density_eq_sum F hn p s
  simpa only [Function.comp_def, ← hid, localFactor] using h

theorem rootDensity_tendsto (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (hconv : SingularSeriesAbsolutelyConvergent F) (p : ℕ) [Fact p.Prime] :
    Tendsto (rootDensity F p) atTop (𝓝 (localFactor F p).re) := by
  simpa only [Function.comp_def, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto (localFactor F p)).comp
      (rootDensity_tendsto_complex F hn hconv p)

theorem localFactor_eq_ofReal (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (hconv : SingularSeriesAbsolutelyConvergent F) (p : ℕ) [Fact p.Prime] :
    localFactor F p = ((localFactor F p).re : ℂ) :=
  tendsto_nhds_unique (rootDensity_tendsto_complex F hn hconv p)
    (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (rootDensity_tendsto F hn hconv p))

theorem localFactor_re_nonneg (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (hconv : SingularSeriesAbsolutelyConvergent F) (p : ℕ) [Fact p.Prime] :
    0 ≤ (localFactor F p).re := by
  apply ge_of_tendsto (rootDensity_tendsto F hn hconv p)
  exact Filter.Eventually.of_forall fun s => by
    unfold rootDensity
    positivity

theorem exists_nonnegative_localFactor (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (hconv : SingularSeriesAbsolutelyConvergent F) (p : ℕ) [Fact p.Prime] :
    ∃ σ : ℝ, 0 ≤ σ ∧ (∑' e : ℕ, singularSeriesTerm F (p ^ e)) = (σ : ℂ) :=
  ⟨(localFactor F p).re, localFactor_re_nonneg F hn hconv p,
    localFactor_eq_ofReal F hn hconv p⟩

/-- Both the real local factor and convergence of the literal modular root
counts are conclusions of global absolute convergence. Strict positivity
is deliberately not asserted. -/
theorem exists_nonnegative_localFactor_and_density_limit
    (F : MvPolynomial (Fin n) ℤ) (hn : 1 ≤ n)
    (hconv : SingularSeriesAbsolutelyConvergent F) (p : ℕ) [Fact p.Prime] :
    ∃ σ : ℝ, 0 ≤ σ ∧ (∑' e : ℕ, singularSeriesTerm F (p ^ e)) = (σ : ℂ) ∧
      Tendsto (fun s : ℕ =>
        ((Finset.univ.filter fun z : Fin n → ZMod (p ^ s) =>
          eval₂ (Int.castRingHom (ZMod (p ^ s))) z F = 0).card : ℝ) /
            (p : ℝ) ^ (s * (n - 1))) atTop (𝓝 σ) := by
  classical
  refine ⟨(localFactor F p).re, localFactor_re_nonneg F hn hconv p,
    localFactor_eq_ofReal F hn hconv p, ?_⟩
  exact rootDensity_tendsto F hn hconv p

/-- The ordinary coefficient with moduli sharing a prime factor with W
removed. This mask does not change its value at one. -/
def coprimeTerm (F : MvPolynomial (Fin n) ℤ) (W q : ℕ) : ℂ :=
  if Nat.Coprime q W then singularSeriesTerm F q else 0

@[simp] theorem coprimeTerm_zero (F : MvPolynomial (Fin n) ℤ) (W : ℕ) :
    coprimeTerm F W 0 = 0 := by
  simp [coprimeTerm]

@[simp] theorem coprimeTerm_one (F : MvPolynomial (Fin n) ℤ) (W : ℕ) :
    coprimeTerm F W 1 = 1 := by
  simp [coprimeTerm]

theorem summable_norm_coprimeTerm (F : MvPolynomial (Fin n) ℤ)
    (hconv : SingularSeriesAbsolutelyConvergent F) (W : ℕ) :
    Summable (fun q => ‖coprimeTerm F W q‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hconv
  intro q
  unfold coprimeTerm
  split_ifs <;> simp

theorem coprimeTerm_prime_pow_of_not_dvd (F : MvPolynomial (Fin n) ℤ)
    (p W : ℕ) (hp : p.Prime) (hpW : ¬p ∣ W) (e : ℕ) :
    coprimeTerm F W (p ^ e) = singularSeriesTerm F (p ^ e) := by
  apply if_pos
  exact (hp.coprime_iff_not_dvd.mpr hpW).pow_left e

theorem tsum_coprimeTerm_prime_pow_of_not_dvd (F : MvPolynomial (Fin n) ℤ)
    (p W : ℕ) (hp : p.Prime) (hpW : ¬p ∣ W) :
    (∑' e : ℕ, coprimeTerm F W (p ^ e)) = localFactor F p := by
  exact tsum_congr (coprimeTerm_prime_pow_of_not_dvd F p W hp hpW)

end CubicTenVariables.OrdinaryLocalSeriesFactor
