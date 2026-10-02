import CubicTenVariables.SmithProfileDistribution
import CubicTenVariables.HessianProfileRoots
import CubicTenVariables.EasyHessianLiftBound
import CubicTenVariables.TranslatedHessianLeadingGeometry

/-!
# The minimum of the easy and transition Smith-profile bounds

The easy estimate is inherited from the proved literal root-lifting theorem. The transition estimate is
combined with it using the exact finite-profile costs, including the
level-one convention with no gamma loss.
-/

noncomputable section
namespace CubicTenVariables.SmithProfileMinimumBound

open MvPolynomial HessianTheorem11 HessianProfileRoots SmithProfileNumerics
  OnCubicRankCountsTen PrimeRankGcdMass TranslatedHessianLeadingGeometry
open scoped BigOperators

/-- The natural transition exponent agrees exactly with the manuscript's
rational delta and finite transition cost. -/
theorem transition_exponent_eq {a : ℕ} (c : Profile a) :
    ((deltaNat (entry c 0) +
      ∑ j ∈ Finset.range (a-1), tauNat (entry c j + entry c (j+1)) : ℕ) : ℝ) =
        (delta (entry c 0) : ℝ) + (transitionCost c : ℝ) := by
  have hc : entry c 0 ≤ 10 := by have := entry_lt_eleven c 0; omega
  have he : ((deltaNat (entry c 0) +
      ∑ j ∈ Finset.range (a-1), tauNat (entry c j + entry c (j+1)) : ℕ) : ℚ) =
        delta (entry c 0) + transitionCost c := by
    rw [Nat.cast_add, Nat.cast_sum, deltaNat_eq_delta _ hc]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => tauNat_eq_tau _)
  exact_mod_cast he

/-- The easy bound uses at most epsilon times the full profile length. -/
theorem easy_exponent_le {a : ℕ} (c : Profile a) (ha : 1 ≤ a)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ((a-1 : ℕ) : ℝ)*(9+ε) + (deltaNat (entry c 0) : ℝ) +
        (if 2 ≤ a then (gammaNat (entry c 0) : ℝ) else 0) ≤
      (delta (entry c 0) : ℝ) + (easyCost c : ℝ) + ε*(a : ℝ) := by
  have hc : entry c 0 ≤ 10 := by have := entry_lt_eleven c 0; omega
  have hd : (deltaNat (entry c 0) : ℝ) = (delta (entry c 0) : ℝ) := by
    exact_mod_cast deltaNat_eq_delta _ hc
  have hg : (gammaNat (entry c 0) : ℝ) = (gamma (entry c 0) : ℝ) := by
    exact_mod_cast gammaNat_eq_gamma _ hc
  rw [hd]
  by_cases h2 : 2 ≤ a
  · simp only [if_pos h2, hg, easyCost]
    push_cast
    rw [Nat.cast_sub ha]
    norm_num only [Nat.cast_one]
    nlinarith
  · have ha1 : a = 1 := by omega
    subst a
    simp [easyCost, hε]

/-- Finite-profile assembly with the transition theorem supplied explicitly.
The final theorem discharges this hypothesis with the proved distribution
bound; this helper does not treat it as a literature input. -/
theorem exists_uniform_bound_of_transition_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε)
    (htransition : ∃ P : ℕ, 2 ≤ P ∧ ∀ (p : ℕ) [Fact p.Prime], P ≤ p →
      ∀ a : ℕ, 1 ≤ a → ∀ c : ℕ → ℕ, c 0 ≤ 10 →
        ((roots F p a c).card : ℝ) ≤
          (p : ℝ)^((deltaNat (c 0) +
            ∑ j ∈ Finset.range (a-1), tauNat (c j + c (j+1)) : ℕ) + ε*(a : ℝ))) :
    ∃ (P : ℕ) (C : ℝ), 2 ≤ P ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime], P ≤ p → ∀ (a : ℕ) (_ha : 1 ≤ a) (c : Profile a),
        ((roots F p a (entry c)).card : ℝ) ≤
          C*(p : ℝ)^((delta (entry c 0) : ℝ) +
            (min (easyCost c) (transitionCost c) : ℝ) + ε*(a : ℝ)) := by
  obtain ⟨P, hP, htrans⟩ := htransition
  obtain ⟨C, hC, heasy⟩ := EasyHessianLiftBound.exists_uniform_bound  F hF hA ε hε
  refine ⟨P, C, hP, hC, ?_⟩
  intro p hp hpP a ha c
  have hc : entry c 0 ≤ 10 := by have := entry_lt_eleven c 0; omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  by_cases hcost : easyCost c ≤ transitionCost c
  · rw [min_eq_left (show (easyCost c : ℝ) ≤ (transitionCost c : ℝ) by exact_mod_cast hcost)]
    have hsubset : ((roots F p a (entry c)).card : ℝ) ≤
        ((HessianRankLifts.rankRoots F p a ha (entry c 0)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (roots_subset_rankRoots F p a ha (entry c))
    exact hsubset.trans ((heasy p a ha (entry c 0) hc).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1 (easy_exponent_le c ha ε hε.le)) hC0))
  · rw [min_eq_right (show (transitionCost c : ℝ) ≤ (easyCost c : ℝ) by
      exact_mod_cast (le_of_not_ge hcost))]
    have ht := htrans p hpP a ha (entry c) hc
    rw [transition_exponent_eq c] at ht
    exact ht.trans (le_mul_of_one_le_left (Real.rpow_nonneg (by positivity) _) hC)

/-- The complete ten-variable profile estimate with the manuscript's minimum
cost. No transition, Smith-form, finite-field, root-count or unproved
literature premise remains. -/
theorem exists_uniform_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : ℕ) (C : ℝ), 2 ≤ P ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime], P ≤ p → ∀ (a : ℕ) (_ha : 1 ≤ a) (c : Profile a),
        ((roots F p a (entry c)).card : ℝ) ≤
          C*(p : ℝ)^((delta (entry c 0) : ℝ) +
            (min (easyCost c) (transitionCost c) : ℝ) + ε*(a : ℝ)) :=
  exists_uniform_bound_of_transition_bound  F hF hA ε hε
    (SmithProfileDistribution.exists_large_prime_transition_bound F hF hA ε hε)

end CubicTenVariables.SmithProfileMinimumBound
