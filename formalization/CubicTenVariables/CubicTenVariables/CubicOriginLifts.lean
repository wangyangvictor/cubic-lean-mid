import CubicTenVariables.PolynomialSingularLifts
import CubicTenVariables.CubicGradientScaling

/-! Exact root counts over the origin prime class of an integral homogeneous
cubic. These are identities between literal residue filters, including the
modulus-one factor at level three. No root estimate or local input is used. -/

noncomputable section
namespace CubicTenVariables.CubicOriginLifts
open MvPolynomial PrimePowerFibers SmoothResidueIteration SmoothResidueLifting
open BinarySingularLifts CubicGradientScaling

/-- Evaluation at the zero low digit extracts the literal integral cubic
factor p³ before any divisibility cancellation. -/
theorem eval_lowDigitLift_zero {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p k : ℕ) (x : Fin n → ZMod (p^k)) :
    eval₂ (Int.castRingHom (ZMod (p^(k+1)))) (lowDigitLift p k 0 x) F =
      ((((p^3 : ℕ) : ℤ) * eval (fun i => ((x i).val : ℤ)) F : ℤ) :
        ZMod (p^(k+1))) := by
  have he := homogeneous_eval₂_smul F hF (RingHom.id ℤ)
    (fun i => ((x i).val : ℤ)) (p : ℤ)
  have he' : eval (fun i => (p : ℤ) * (x i).val) F =
      ((p^3 : ℕ) : ℤ) * eval (fun i => ((x i).val : ℤ)) F := by
    simpa only [eval₂_id, Pi.smul_apply, smul_eq_mul, Nat.cast_pow] using he
  rw [← he', cast_eval_int]
  apply congrArg (fun v : Fin n → ZMod (p^(k+1)) => eval₂ (Int.castRingHom _) v F)
  funext i
  simp only [lowDigitLift, Pi.zero_apply, zero_add]

/-- At level k+3, the equation on the origin low-digit fiber is exactly the
unrestricted equation at level k after reducing its remaining digits. -/
theorem zero_lowDigitLift_iff {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p k : ℕ) [Fact p.Prime]
    (x : Fin n → ZMod (p^(k+2))) :
    eval₂ (Int.castRingHom (ZMod (p^(k+3)))) (lowDigitLift p (k+2) 0 x) F = 0 ↔
      eval₂ (Int.castRingHom (ZMod (p^k)))
        (fun i => reduction p (show k ≤ k+2 by omega) (x i)) F = 0 := by
  rw [eval_lowDigitLift_zero F hF, power_mul_cast_eq_zero_iff, cast_eval_int]
  have hv (i : Fin n) : (((x i).val : ℤ) : ZMod (p^k)) =
      reduction p (show k ≤ k+2 by omega) (x i) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      (map_natCast (reduction p (show k ≤ k+2 by omega)) (x i).val).symm
  simp only [hv]

/-- Exact origin-class recurrence for every r≥3. At r=3, the right-hand
root set is the actual one-element residue space modulo p⁰. -/
theorem card_origin_lifts {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 3 ≤ r) :
    (Finset.univ.filter fun x : Fin n → ZMod (p^r) =>
      (∀ i, toPrime p r (by omega) (x i) = 0) ∧
        eval₂ (Int.castRingHom (ZMod (p^r))) x F = 0).card =
      p^(2*n) * (Finset.univ.filter fun y : Fin n → ZMod (p^(r-3)) =>
        eval₂ (Int.castRingHom (ZMod (p^(r-3)))) y F = 0).card := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, r = k+3 := ⟨r-3, by omega⟩
  have hc := card_lowDigit_filter p (k+2) (0 : Fin n → ℤ)
    (fun x => eval₂ (Int.castRingHom (ZMod (p^(k+3)))) x F = 0)
  simp only [Pi.zero_apply, Int.cast_zero] at hc
  rw [hc]
  simp only [zero_lowDigitLift_iff F hF]
  simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_left] using
    PolynomialSingularLifts.card_reduction_preimage p (show k ≤ k+2 by omega)
      (fun y : Fin n → ZMod (p^k) => eval₂ (Int.castRingHom (ZMod (p^k))) y F = 0)

/-- Any positive-degree homogeneous cubic vanishes at the actual origin. -/
theorem eval₂_zero {n : ℕ} {R : Type*} [CommSemiring R]
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (f : ℤ →+* R) :
    eval₂ f (0 : Fin n → R) F = 0 := by
  have h := homogeneous_eval₂_smul F hF f (0 : Fin n → R) (0 : R)
  simpa using h

/-- At the prime level the origin class consists of its unique zero vector. -/
theorem card_origin_lifts_one {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun x : Fin n → ZMod (p^1) =>
      (∀ i, toPrime p 1 le_rfl (x i) = 0) ∧
        eval₂ (Int.castRingHom (ZMod (p^1))) x F = 0).card = 1 := by
  change (zeroLifts p 1 le_rfl F 0).card = 1
  rw [zeroLifts_one p F 0 (eval₂_zero F hF _), Finset.card_singleton]

/-- Every vector in the origin prime class is already a cubic zero modulo
p², so that class contains exactly pⁿ zeros. -/
theorem card_origin_lifts_two {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun x : Fin n → ZMod (p^2) =>
      (∀ i, toPrime p 2 (by omega) (x i) = 0) ∧
        eval₂ (Int.castRingHom (ZMod (p^2))) x F = 0).card = p^n := by
  classical
  have hc := card_lowDigit_filter p 1 (0 : Fin n → ℤ)
    (fun x => eval₂ (Int.castRingHom (ZMod (p^2))) x F = 0)
  simp only [Pi.zero_apply, Int.cast_zero] at hc
  rw [hc]
  have hz (x : Fin n → ZMod (p^1)) :
      eval₂ (Int.castRingHom (ZMod (p^2))) (lowDigitLift p 1 0 x) F = 0 := by
    rw [eval_lowDigitLift_zero F hF]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    have hd : ((p^2 : ℕ) : ℤ) ∣ ((p^3 : ℕ) : ℤ) := by
      exact_mod_cast pow_dvd_pow p (show 2 ≤ 3 by omega)
    exact hd.mul_right _
  simp only [hz, Finset.filter_true, Finset.card_univ, Fintype.card_fun,
    ZMod.card, pow_one, Fintype.card_fin]

/-- Level three has p^(2n) origin-class roots, since the remaining modulus
in the exact recurrence is one. -/
theorem card_origin_lifts_three {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun x : Fin n → ZMod (p^3) =>
      (∀ i, toPrime p 3 (by omega) (x i) = 0) ∧
        eval₂ (Int.castRingHom (ZMod (p^3))) x F = 0).card = p^(2*n) := by
  rw [card_origin_lifts F hF p 3 le_rfl]
  haveI : Subsingleton (ZMod (p^(3-3))) := by
    simpa only [Nat.sub_self, pow_zero] using (inferInstance : Subsingleton (ZMod 1))
  have hz (y : Fin n → ZMod (p^(3-3))) :
      eval₂ (Int.castRingHom (ZMod (p^(3-3)))) y F = 0 := Subsingleton.elim _ _
  simp only [hz, Finset.filter_true, Finset.card_univ, Fintype.card_fun,
    ZMod.card, Nat.sub_self, pow_zero, one_pow, mul_one]

/-- A center divisible by p specifies precisely the same actual prime class
as the origin; no choice of representative changes the recurrence. -/
theorem card_divisible_center_lifts {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 3 ≤ r)
    (a : Fin n → ℤ) (ha : ∀ i, (p : ℤ) ∣ a i) :
    (Finset.univ.filter fun x : Fin n → ZMod (p^r) =>
      (∀ i, toPrime p r (by omega) (x i) = (a i : ZMod p)) ∧
        eval₂ (Int.castRingHom (ZMod (p^r))) x F = 0).card =
      p^(2*n) * (Finset.univ.filter fun y : Fin n → ZMod (p^(r-3)) =>
        eval₂ (Int.castRingHom (ZMod (p^(r-3)))) y F = 0).card := by
  have haz (i : Fin n) : (a i : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (ha i)
  simpa only [haz] using card_origin_lifts F hF p r hr

end CubicTenVariables.CubicOriginLifts
