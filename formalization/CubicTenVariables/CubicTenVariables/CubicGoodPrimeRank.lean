import CubicTenVariables.HessianRankOneReduction

/-!
# One fixed integer for the rank-two lifting application

The existing proved integral certificate excludes all nonzero on-cubic
rank-at-most-one points modulo every prime outside its divisors. Multiplying
by six also excludes the two small primes. The conclusion below applies to
literal integer centers and the actual reduced Hessian, with no spreading-out
or finite-field geometry premise.
-/

noncomputable section
namespace CubicTenVariables.CubicGoodPrimeRank
open MvPolynomial HessianTheorem11

/-- One actual nonzero integer controls all primes and all integer centers. -/
theorem exists_rank_two_certificate {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ¬ (p : ℤ) ∣ D → p ≠ 2 ∧ p ≠ 3 ∧
        ∀ k : Fin n → ℤ, (p : ℤ) ∣ eval k F →
          (∃ i, ¬ (p : ℤ) ∣ k i) →
          2 ≤ (hessian (map (Int.castRingHom (ZMod p)) F)
            (fun i => (k i : ZMod p))).rank := by
  obtain ⟨D,hD,hgood⟩ := HessianRankOneReduction.exists_good_prime_certificate F hF hA
  refine ⟨6*D, mul_ne_zero (by norm_num) hD, ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro hpd
  have hpD : ¬ (p : ℤ) ∣ D := fun h => hpd (dvd_mul_of_dvd_right h 6)
  refine ⟨?_,?_,?_⟩
  · intro heq
    subst p
    exact hpd ⟨3*D, by ring⟩
  · intro heq
    subst p
    exact hpd ⟨2*D, by ring⟩
  · intro k hk hnonzero
    by_contra hr
    have hr' : (hessian (map (Int.castRingHom (ZMod p)) F)
        (fun i => (k i : ZMod p))).rank ≤ 1 := by omega
    have hx : eval (fun i => (k i : ZMod p))
        (map (Int.castRingHom (ZMod p)) F) = 0 := by
      rw [← eval₂_eq_eval_map]
      have he : ((eval k F : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hk
      have hm := map_eval (Int.castRingHom (ZMod p)) k F
      simpa only [Function.comp_def, Int.coe_castRingHom, eval₂_eq_eval_map, he] using hm.symm
    have hz := hgood p hp hpD (fun i => (k i : ZMod p)) hx hr'
    obtain ⟨i,hi⟩ := hnonzero
    exact hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (congrFun hz i))

end CubicTenVariables.CubicGoodPrimeRank
