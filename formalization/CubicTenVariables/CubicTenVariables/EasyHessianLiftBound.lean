import CubicTenVariables.HessianRankLifts
import CubicTenVariables.PrimeRankGcdMass
import CubicTenVariables.PrimePowerRootFiberBound

/-!
# The ten-variable easy Hessian lifting bound

A literal partition by the prime residue sums the proved rank-specific gcd
mass against the proved composite root bound. No unproved literature
premise remains. One constant precedes
every prime, positive level and rank. Level one incurs no gamma loss.
-/

noncomputable section
namespace CubicTenVariables.EasyHessianLiftBound
open MvPolynomial HessianTheorem11 SmoothResidueIteration
  HessianRankLifts OnCubicRankCountsTen PrimeRankGcdMass PrimeFrogZeroMass
open scoped BigOperators

/-- Rank-conditioned prime-power root count with natural delta/gamma tables. -/
theorem exists_uniform_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime],
      ∀ (a : ℕ) (ha : 1 ≤ a) (r : ℕ), r ≤ 10 →
        ((rankRoots F p a ha r).card : ℝ) ≤
          C*(p : ℝ)^(((a-1 : ℕ) : ℝ)*(9+ε)+(deltaNat r : ℝ)+
            (if 2 ≤ a then (gammaNat r : ℝ) else 0)) := by
  classical
  obtain ⟨A,hA1,hfiber⟩ := PrimePowerRootFiberBound.exists_uniform_bound  F hF hA ε hε
  obtain ⟨B,hB1,hB⟩ := PrimeRankGcdMass.exists_uniform_bounds F hF hA
  have hB1R : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hAB : (1 : ℝ) ≤ A*B := by
    calc
      1 = 1*1 := by ring
      _ ≤ A*B := mul_le_mul hA1 hB1R (by norm_num) (by linarith)
  refine ⟨A*B, hAB, ?_⟩
  intro p hp a ha r hr
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hcounts := hB p r hr
  by_cases h2 : 2 ≤ a
  · have hsum : ((rankRoots F p a ha r).card : ℝ) ≤
        A*(p : ℝ)^(((a-1 : ℕ) : ℝ)*(9+ε)) *
          ((∑ y ∈ exactRankRoots F p r, rootWeight F p y : ℕ) : ℝ) := by
      rw [card_rankRoots_eq_sum]
      change ((∑ y ∈ exactRankRoots F p r, (zeroLifts p a ha F y).card : ℕ) : ℝ) ≤ _
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y hy
      exact hfiber p a ha h2 y (Finset.mem_filter.mp hy).2.1
    calc
      _ ≤ A*(p : ℝ)^(((a-1 : ℕ) : ℝ)*(9+ε)) *
          ((∑ y ∈ exactRankRoots F p r, rootWeight F p y : ℕ) : ℝ) := hsum
      _ ≤ A*(p : ℝ)^(((a-1 : ℕ) : ℝ)*(9+ε)) *
          ((B*p^(deltaNat r+gammaNat r) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcounts.2) (by positivity)
      _ = _ := by
        rw [if_pos h2]
        push_cast
        rw [show ((a-1 : ℕ) : ℝ)*(9+ε)+(deltaNat r : ℝ)+(gammaNat r : ℝ) =
          ((a-1 : ℕ) : ℝ)*(9+ε)+((deltaNat r+gammaNat r : ℕ) : ℝ) by push_cast; ring]
        rw [Real.rpow_add hpR, Real.rpow_natCast]
        ring
  · have ha1 : a = 1 := by omega
    subst a
    have hc : ((rankRoots F p 1 ha r).card : ℝ) ≤ ((B*p^(deltaNat r) : ℕ) : ℝ) := by
      exact_mod_cast (show (rankRoots F p 1 ha r).card ≤ B*p^(deltaNat r) by
        simpa only [card_rankRoots_one, exactRankRoots] using hcounts.1)
    calc
      _ ≤ ((B*p^(deltaNat r) : ℕ) : ℝ) := hc
      _ ≤ (A*B)*(p : ℝ)^(deltaNat r : ℝ) := by
        rw [Real.rpow_natCast]
        push_cast
        nlinarith [show (0 : ℝ) ≤ (B : ℝ)*(p : ℝ)^(deltaNat r) by positivity]
      _ = _ := by norm_num

/-- The manuscript's literal finite filter and exact real exponent, with
no unproved literature input. -/
theorem exists_literal_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (a : ℕ) (ha : 1 ≤ a) (r : ℕ), r ≤ 10 →
        ((Finset.univ.filter (fun z : Fin 10 → ZMod (p^a) =>
          eval₂ (Int.castRingHom (ZMod (p^a))) z F = 0 ∧
          (hessian (map (Int.castRingHom (ZMod p)) F)
            (fun i => toPrime p a ha (z i))).rank = r)).card : ℝ) ≤
          C*(p : ℝ)^(((a : ℝ)-1)*(9+ε)+(SmithProfileNumerics.delta r : ℝ)+
            (SmithProfileNumerics.gamma r : ℝ)*(if 2 ≤ a then 1 else 0)) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_bound  F hF hA ε hε
  refine ⟨C,hC,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro a ha r hr
  have hd : (deltaNat r : ℝ) = (SmithProfileNumerics.delta r : ℝ) := by
    exact_mod_cast deltaNat_eq_delta r hr
  have hg : (gammaNat r : ℝ) = (SmithProfileNumerics.gamma r : ℝ) := by
    exact_mod_cast gammaNat_eq_gamma r hr
  have hh := hbound p a ha r hr
  by_cases h2 : 2 ≤ a <;>
    simpa [rankRoots, Nat.cast_sub ha, hd, hg, h2] using hh

end CubicTenVariables.EasyHessianLiftBound
