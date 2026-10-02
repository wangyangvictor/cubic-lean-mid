import CubicTenVariables.CubicSingularQuotient
import CubicTenVariables.PolynomialSingularLifts
import CubicTenVariables.RankTwoPolynomialLifting
import CubicTenVariables.CubicGoodPrimeRank

/-!
# The singular nonzero residue-class bound for an actual integral cubic

The quotient polynomial, its reduced Hessian, and the free last-digit factor
are constructed before invoking the rank-two root bound. The final certificate
corollary chooses the exceptional integer from rational anisotropy and proves
the required Hessian rank internally.
-/

noncomputable section
namespace CubicTenVariables.CubicSingularResidueBound
open MvPolynomial HessianTheorem11 SmoothResidueIteration
open CubicSingularQuotient

/-- Actual roots above a critical center with reduced Hessian rank at least
two satisfy the manuscript's sharp singular-class exponent. -/
theorem card_singular_lifts_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (r : ℕ) (hr : 2 ≤ r)
    (k : Fin n → ℤ) (hg : ∀ i, (p : ℤ) ∣ eval k (pderiv i F))
    (hH : 2 ≤ (hessian (map (Int.castRingHom (ZMod p)) F)
      (fun i => (k i : ZMod p))).rank) :
    (Finset.univ.filter fun z : Fin n → ZMod (p^r) =>
      (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
        (r-1)*p^((r-1)*(n-1)+1) := by
  by_cases h0 : (p : ℤ)^2 ∣ eval k F
  · rw [PolynomialSingularLifts.card_singular_lifts_of_rescale F
      (quotientPolynomial F k (p : ℤ)) p r hr k
      (eval_translate_eq_sq_mul_quotient F hF k (p : ℤ) h0 hg)]
    have hbound := RankTwoPolynomialLifting.card_zeros_le_succ_mul_pow
      (quotientPolynomial F k (p : ℤ)) p hp
      (totalDegree_quotient_le_three F hF k (p : ℤ))
      (totalDegree_reduction_quotient_le_two F hF k p)
      (by rwa [hessian_reduction_quotient_origin F hF]) (r-2)
    have hn : 2 ≤ n := hH.trans (Matrix.rank_le_width _)
    calc
      _ ≤ p^n * ((r-2+1)*p^((r-2)*(n-1))) := Nat.mul_le_mul_left _ hbound
      _ = (r-1)*(p^n*p^((r-2)*(n-1))) := by
        rw [show r-2+1 = r-1 by omega]
        ring
      _ = (r-1)*p^((r-1)*(n-1)+1) := by
        rw [← pow_add]
        congr 2
        rw [show r-1 = (r-2)+1 by omega, Nat.add_mul, one_mul]
        omega
  · rw [PolynomialSingularLifts.card_singular_lifts_of_not_sq_dvd F p r hr k hg h0]
    exact Nat.zero_le _

/-- The exact singular-class exponent used in ten variables. -/
theorem card_ten_singular_lifts_le
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (r : ℕ) (hr : 2 ≤ r)
    (k : Fin 10 → ℤ) (hg : ∀ i, (p : ℤ) ∣ eval k (pderiv i F))
    (hH : 2 ≤ (hessian (map (Int.castRingHom (ZMod p)) F)
      (fun i => (k i : ZMod p))).rank) :
    (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
      (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
        (r-1)*p^(9*(r-1)+1) := by
  simpa only [Nat.reduceSub, Nat.mul_comm (r-1) 9] using
    card_singular_lifts_le F hF p hp r hr k hg hH

/-- The same actual count with the rank condition derived from a single
proved certificate, chosen before every prime, center, and lifting level. -/
theorem exists_good_prime_singular_bound {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ¬ (p : ℤ) ∣ D → ∀ (k : Fin n → ℤ),
        (p : ℤ) ∣ eval k F → (∃ i, ¬ (p : ℤ) ∣ k i) →
        (∀ i, (p : ℤ) ∣ eval k (pderiv i F)) →
        ∀ (r : ℕ) (hr : 2 ≤ r),
          (Finset.univ.filter fun z : Fin n → ZMod (p^r) =>
            (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
            eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
              (r-1)*p^((r-1)*(n-1)+1) := by
  obtain ⟨D,hD,hgood⟩ := CubicGoodPrimeRank.exists_rank_two_certificate F hF hA
  refine ⟨D,hD,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro hpd k hk hnonzero hg r hr
  obtain ⟨hp2,_,hH⟩ := hgood p hp hpd
  exact card_singular_lifts_le F hF p hp2 r hr k hg (hH k hk hnonzero)

end CubicTenVariables.CubicSingularResidueBound
