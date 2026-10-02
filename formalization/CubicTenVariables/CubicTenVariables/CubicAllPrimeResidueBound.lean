import CubicTenVariables.CubicGoodPrimeResidueBound

/-!
# Absorbing the finite exceptional primes in the residue-class bound

The exceptional integer is chosen before the supplied unrestricted counting
constant. Its prime divisors are bounded by its absolute value, so their
extra factor p^9 is absorbed into one larger natural constant. The global
unrestricted root bound remains explicit in this assembly helper.
-/

noncomputable section
namespace CubicTenVariables.CubicAllPrimeResidueBound
open MvPolynomial HessianTheorem11 SmoothResidueIteration

/-- A literal prime-class root filter is a subset of the unrestricted root
filter at the same modulus. -/
theorem card_prime_class_le_full {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 1 ≤ r) (k : Fin n → ℤ) :
    (Finset.univ.filter fun z : Fin n → ZMod (p^r) =>
      (∀ i, toPrime p r hr (z i) = (k i : ZMod p)) ∧
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
    (Finset.univ.filter fun z : Fin n → ZMod (p^r) =>
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card := by
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact hz.2

/-- At the first prime-power level there is precisely one residue vector
in the supplied prime class, and it is a root by the displayed congruence.
No homogeneity, degree bound, or counting estimate is assumed. -/
theorem card_prime_class_roots_one {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (k : Fin n → ℤ) (hk : (p : ℤ) ∣ eval k F) :
    (Finset.univ.filter fun z : Fin n → ZMod (p^1) =>
      (∀ i, toPrime p 1 le_rfl (z i) = (k i : ZMod p)) ∧
      eval₂ (Int.castRingHom (ZMod (p^1))) z F = 0).card = 1 := by
  have hk' : eval₂ (Int.castRingHom (ZMod p)) (fun i => (k i : ZMod p)) F = 0 := by
    rw [← SmoothResidueLifting.cast_eval_int, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hk
  change (zeroLifts p 1 le_rfl F (fun i => (k i : ZMod p))).card = 1
  rw [zeroLifts_one p F (fun i => (k i : ZMod p)) hk', Finset.card_singleton]

/-- At a divisor of a fixed nonzero integer, the unrestricted estimate
absorbs into the defect-zero class bound with an explicit enlarged constant.
Only the unrestricted estimate at this exact prime and level is used. -/
theorem card_exceptional_prime_lifts_le (F : MvPolynomial (Fin 10) ℤ)
    (p : ℕ) [Fact p.Prime] (D : ℤ) (hD : D ≠ 0) (hpD : (p : ℤ) ∣ D)
    (C r : ℕ) (hr : 2 ≤ r) (k : Fin 10 → ℤ)
    (hU : (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤ C*p^(9*r)) :
    (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
      (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
        (C*(max 1 D.natAbs)^9)*(r-1)*p^(9*(r-1)) := by
  have hpabs : p ≤ D.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero hpD hD
  have hpmax : p ≤ max 1 D.natAbs := hpabs.trans (le_max_right _ _)
  have hp9 : p^9 ≤ (max 1 D.natAbs)^9 := Nat.pow_le_pow_left hpmax 9
  have hr1 : 1 ≤ r-1 := by omega
  calc
    _ ≤ (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
      eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card :=
        card_prime_class_le_full F p r (by omega) k
    _ ≤ C*p^(9*r) := hU
    _ = (C*p^9)*p^(9*(r-1)) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    _ ≤ (C*(max 1 D.natAbs)^9)*p^(9*(r-1)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C hp9)
    _ ≤ (C*(max 1 D.natAbs)^9)*(r-1)*p^(9*(r-1)) := by
      apply Nat.mul_le_mul_right
      simpa only [mul_one] using Nat.mul_le_mul_left (C*(max 1 D.natAbs)^9) hr1

/-- A single constant controls all primes, centers and levels r≥2.
The fixed exceptional integer precedes C and the explicit global unrestricted
input hU. Exceptional primes have defect zero; the good-prime defects are
2 at the origin, 1 at a nonzero critical point, and 0 at a smooth point.
This is a prime-power statement, not a CRT or square-full modulus estimate. -/
theorem exists_all_prime_residue_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (C : ℕ), 1 ≤ C →
      (∀ (q : ℕ) (hq : q.Prime),
        letI : Fact q.Prime := ⟨hq⟩
        ∀ s : ℕ,
          (Finset.univ.filter fun z : Fin 10 → ZMod (q^s) =>
            eval₂ (Int.castRingHom (ZMod (q^s))) z F = 0).card ≤ C*q^(9*s)) →
      ∃ B : ℕ, 1 ≤ B ∧ ∀ (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (k : Fin 10 → ℤ), (p : ℤ) ∣ eval k F →
          ∀ (r : ℕ) (hr : 2 ≤ r),
            (Finset.univ.filter fun z : Fin 10 → ZMod (p^r) =>
              (∀ i, toPrime p r (by omega) (z i) = (k i : ZMod p)) ∧
              eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card ≤
                B*(r-1)*p^(9*(r-1) +
                  if (p : ℤ) ∣ D then 0 else
                  if (∀ i, (p : ℤ) ∣ k i) then 2
                  else if (∀ i, (p : ℤ) ∣ eval k (pderiv i F)) then 1 else 0) := by
  obtain ⟨D,hD,hgood⟩ := CubicGoodPrimeResidueBound.exists_good_prime_residue_bound F hF hA
  refine ⟨D,hD,?_⟩
  intro C hC hU
  let B := C*(max 1 D.natAbs)^9
  have hpow : 1 ≤ (max 1 D.natAbs)^9 := by
    simpa only [one_pow] using Nat.pow_le_pow_left (le_max_left 1 D.natAbs) 9
  have hB : 1 ≤ B := by
    simpa only [one_mul] using Nat.mul_le_mul hC hpow
  have hCB : C ≤ B := by
    simpa only [mul_one] using Nat.mul_le_mul_left C hpow
  refine ⟨B,hB,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro k hk r hr
  by_cases hpD : (p : ℤ) ∣ D
  · simp only [if_pos hpD, add_zero]
    exact card_exceptional_prime_lifts_le F p D hD hpD C r hr k (hU p hp r)
  · simp only [if_neg hpD]
    have hc := hgood C hC hU p hp hpD k hk r hr
    exact hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (r-1) hCB))

end CubicTenVariables.CubicAllPrimeResidueBound
