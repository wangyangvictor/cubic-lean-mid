import CubicTenVariables.PrimePowerRootSeriesIdentity
import CubicTenVariables.PrimePowerSeriesConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform ten-variable root counts from an explicit all-modulus complete
sum estimate. The estimate is an input here, not a new literature premise.
The proof uses only the finite root-density identity and a geometric series;
it does not use Bernert or global singular-series convergence. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimePowerRootBoundOfPointwise
open MvPolynomial
open scoped BigOperators

/-- The normalized terms at powers of any prime have one uniform geometric
majorant, including level zero. Thus every finite prime-power partial sum
has the same bound, before the prime or truncation is chosen. -/
theorem norm_prime_power_partial_le (F : MvPolynomial (Fin 10) ℤ) {C : ℝ}
    (hbound : ∀ q : ℕ, 0 < q →
      ‖completeCubicSum F q 0‖ ≤ C * (q : ℝ) ^ ((28 : ℝ) / 3))
    (p : ℕ) (hp : p.Prime) (s : ℕ) :
    ‖∑ k ∈ Finset.range (s+1), singularSeriesTerm F (p^k)‖ ≤
      C * (1 - (2 : ℝ) ^ (-(2 : ℝ)/3))⁻¹ := by
  have hC1 : 1 ≤ C := by simpa using hbound 1 (by omega)
  have hC : 0 ≤ C := le_trans (by norm_num) hC1
  let θ : ℝ := (2 : ℝ) ^ (-(2 : ℝ)/3)
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg (by norm_num) _
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsummable : Summable (fun k : ℕ => θ ^ k) :=
    summable_geometric_of_lt_one hθ0 hθ1
  have hmajorant (k : ℕ) : ‖singularSeriesTerm F (p^k)‖ ≤ C * θ ^ k := by
    have h := PrimePowerSeriesConvergence.normalized_bound F (pow_pos hp.pos k)
      (hbound (p^k) (pow_pos hp.pos k))
    have hnorm : ‖singularSeriesTerm F (p^k)‖ ≤
        C * ((p : ℝ)^k)^(-(2 : ℝ)/3) := by
      convert h using 1 <;> norm_num
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : 0 ≤ (p : ℝ) := by positivity
    have hratio : (p : ℝ)^(-(2 : ℝ)/3) ≤ θ :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    rw [← Real.rpow_pow_comm hp0] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hp0 _) hratio k) hC)
  calc
    _ ≤ ∑ k ∈ Finset.range (s+1), ‖singularSeriesTerm F (p^k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (s+1), C * θ ^ k :=
      Finset.sum_le_sum (fun k _ => hmajorant k)
    _ = C * ∑ k ∈ Finset.range (s+1), θ ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∑' k : ℕ, θ ^ k := mul_le_mul_of_nonneg_left
      (hsummable.sum_le_tsum _ (fun k _ => pow_nonneg hθ0 k)) hC
    _ = _ := by rw [tsum_geometric_of_lt_one hθ0 hθ1]

/-- Exactly the manuscript's unrestricted ten-variable root estimate,
conditional only on the displayed complete-sum bound. No homogeneity or
anisotropy premise is needed by this finite-identity adapter itself. -/
theorem exists_uniform_root_bound (F : MvPolynomial (Fin 10) ℤ) {C : ℝ}
    (hbound : ∀ q : ℕ, 0 < q →
      ‖completeCubicSum F q 0‖ ≤ C * (q : ℝ) ^ ((28 : ℝ) / 3)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : ℕ,
        (Finset.univ.filter fun z : Fin 10 → ZMod (p^s) =>
          eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ A*p^(9*s) := by
  obtain ⟨A, hA⟩ := exists_nat_ge (C * (1 - (2 : ℝ)^(-(2 : ℝ)/3))⁻¹)
  have hA' : C * (1 - (2 : ℝ)^(-(2 : ℝ)/3))⁻¹ ≤ ((A+1 : ℕ) : ℝ) :=
    hA.trans (by exact_mod_cast Nat.le_succ A)
  refine ⟨A+1, by omega, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro s
  have hnorm := congrArg norm (PrimePowerRootSeriesIdentity.root_density_eq_sum
    F (by omega) p s)
  simp only [norm_div, norm_pow, Complex.norm_natCast, Nat.reduceSub] at hnorm
  have hratio : (PrimePowerRootSeriesIdentity.rootCount F p s : ℝ) /
      (p : ℝ)^(s*9) ≤ ((A+1 : ℕ) : ℝ) := by
    rw [hnorm]
    exact (norm_prime_power_partial_le F hbound p hp s).trans hA'
  have hpos : 0 < (p : ℝ)^(s*9) := pow_pos (by exact_mod_cast hp.pos) _
  have hcount := (div_le_iff₀ hpos).mp hratio
  simpa only [PrimePowerRootSeriesIdentity.rootCount, Nat.mul_comm s 9] using
    (show PrimePowerRootSeriesIdentity.rootCount F p s ≤ (A+1)*p^(s*9) by
      exact_mod_cast hcount)

end CubicTenVariables.PrimePowerRootBoundOfPointwise
