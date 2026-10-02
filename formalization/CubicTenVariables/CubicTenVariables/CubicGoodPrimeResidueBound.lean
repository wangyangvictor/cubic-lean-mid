import CubicTenVariables.CubicOriginLifts
import CubicTenVariables.CubicSingularResidueBound
import CubicTenVariables.GeneralSmoothResidueIteration

/-!
# The three good-prime residue classes in ten variables

The exceptional integer is proved from rational anisotropy and chosen before
any counting constant. The unrestricted root-count estimate is an EXPLICIT
remaining premise. It is not asserted here and is not a literature axiom.
Smooth and nonzero singular classes use the proved local results; the origin
class uses the exact homogeneous recurrence and that unrestricted estimate.
-/

noncomputable section
namespace CubicTenVariables.CubicGoodPrimeResidueBound
open MvPolynomial HessianTheorem11 SmoothResidueIteration

/-- The origin-class estimate from an explicit unrestricted estimate at
this prime. The constant is independent of the lifting level. This sharper
bound does not need the factor r-1 used in the final common formulation. -/
theorem card_ten_divisible_center_lifts_le
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (C : ℕ) (hC : 1 ≤ C)
    (hU : ∀ s : ℕ,
      (Finset.univ.filter fun z : Fin 10 → ZMod (p^s) =>
        eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ C*p^(9*s))
    (r : ℕ) (hr : 2 ≤ r) (k : Fin 10 → ℤ)
    (hk : ∀ i, (p : ℤ) ∣ k i) :
    (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
      (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
        C*p^(9*(r-1)+2) := by
  by_cases hr2 : r = 2
  · subst r
    have hz (i : Fin 10) : (k i : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hk i)
    have hc := CubicOriginLifts.card_origin_lifts_two F hF p
    simp only [hz]
    rw [hc]
    calc
      p^10 ≤ p^11 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
      _ ≤ C*p^11 := by simpa only [one_mul] using Nat.mul_le_mul_right (p^11) hC
  · have hr3 : 3 ≤ r := by omega
    rw [CubicOriginLifts.card_divisible_center_lifts F hF p r hr3 k hk]
    calc
      p^(2*10) * _ ≤ p^(2*10) * (C*p^(9*(r-3))) := Nat.mul_le_mul_left _ (hU (r-3))
      _ = C*(p^(2*10)*p^(9*(r-3))) := by ring
      _ = C*p^(9*(r-1)+2) := by
        rw [← pow_add]
        congr 2
        omega

/-- One fixed good-prime certificate controls all three literal residue
cases. The unrestricted estimate hU is an explicit open input, quantified
uniformly over primes and levels; no proof of that estimate is claimed.
The defect is 2 at the origin class, 1 at a nonzero critical class, and 0
at a smooth class. No coordinate change, slice count, or recurrence is
supplied as an additional premise. -/
theorem exists_good_prime_residue_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (C : ℕ), 1 ≤ C →
      (∀ (q : ℕ) (hq : q.Prime),
        letI : Fact q.Prime := ⟨hq⟩
        ∀ s : ℕ,
          (Finset.univ.filter fun z : Fin 10 → ZMod (q^s) =>
            eval₂ (Int.castRingHom (ZMod (q^s))) z F = 0).card ≤ C*q^(9*s)) →
      ∀ (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        ¬ (p : ℤ) ∣ D → ∀ (k : Fin 10 → ℤ), (p : ℤ) ∣ eval k F →
          ∀ (r : ℕ) (hr : 2 ≤ r),
            (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
              (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
              eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
                C*(r-1)*p^(9*(r-1) +
                  if (∀ i, (p : ℤ) ∣ k i) then 2
                  else if (∀ i, (p : ℤ) ∣ eval k (pderiv i F)) then 1 else 0) := by
  obtain ⟨D,hD,hgood⟩ := CubicGoodPrimeRank.exists_rank_two_certificate F hF hA
  refine ⟨D,hD,?_⟩
  intro C hC hU p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro hpd k hk r hr
  have hr1 : 1 ≤ r-1 := by omega
  by_cases hkzero : ∀ i, (p : ℤ) ∣ k i
  · simp only [if_pos hkzero]
    have hc := card_ten_divisible_center_lifts_le F hF p C hC (hU p hp) r hr k hkzero
    have hcoef : C ≤ C*(r-1) := by
      simpa only [mul_one] using Nat.mul_le_mul_left C hr1
    exact hc.trans (Nat.mul_le_mul_right _ hcoef)
  · simp only [if_neg hkzero]
    by_cases hg : ∀ i, (p : ℤ) ∣ eval k (pderiv i F)
    · simp only [if_pos hg]
      have hnonzero : ∃ i, ¬ (p : ℤ) ∣ k i := not_forall.mp hkzero
      obtain ⟨hp2,_,hH⟩ := hgood p hp hpd
      have hc := CubicSingularResidueBound.card_ten_singular_lifts_le
        F hF p hp2 r hr k hg (hH k hk hnonzero)
      calc
        _ ≤ (r-1)*p^(9*(r-1)+1) := hc
        _ ≤ C*((r-1)*p^(9*(r-1)+1)) := by
          simpa only [one_mul] using Nat.mul_le_mul_right ((r-1)*p^(9*(r-1)+1)) hC
        _ = C*(r-1)*p^(9*(r-1)+1) := by ring
    · simp only [if_neg hg, add_zero]
      have hgradient : ∃ i, ((eval k (pderiv i F) : ℤ) : ZMod p) ≠ 0 := by
        obtain ⟨i,hi⟩ := not_forall.mp hg
        exact ⟨i, fun hz => hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)⟩
      have hc := GeneralSmoothResidueIteration.card_smooth_integer_zero_lifts
        p F k hk hgradient r (by omega)
      have hc' :
          (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
            (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
            eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card = p^(9*(r-1)) := by
        simpa only [Nat.reduceSub, Nat.mul_comm (r-1) 9] using hc
      rw [hc']
      have hcoef : 1 ≤ C*(r-1) := by
        simpa only [one_mul] using Nat.mul_le_mul hC hr1
      simpa only [one_mul] using Nat.mul_le_mul_right (p^(9*(r-1))) hcoef

end CubicTenVariables.CubicGoodPrimeResidueBound
