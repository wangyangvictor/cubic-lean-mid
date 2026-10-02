import CubicTenVariables.CRTCharacters

/-!
# Exact CRT for polynomial roots in a prescribed residue class

The polynomial and residue center are integral. All reductions are actual
ring homomorphisms between the indicated residue rings. The two root counts
multiply exactly, including modulus-one factors and empty variable types.
No degree, nonsingularity, or anisotropy hypothesis is required.
-/

noncomputable section

namespace CubicTenVariables.PolynomialResidueCRT

open MvPolynomial CRTCharacters

variable {n c₁ c₂ d₁ d₂ : ℕ}

private theorem map_eval₂_int {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : MvPolynomial (Fin n) ℤ) (z : Fin n → R) :
    f (eval₂ (Int.castRingHom R) z F) =
      eval₂ (Int.castRingHom S) (fun i => f (z i)) F := by
  have hc : f.comp (Int.castRingHom R) = Int.castRingHom S := by
    ext k
    simp
  simpa only [hc, Function.comp_def] using
    eval₂_comp_left f (Int.castRingHom R) z F

/-- The actual root condition is equivalent to both of its CRT projections. -/
theorem zero_crt_iff (F : MvPolynomial (Fin n) ℤ) (hc : c₁.Coprime c₂)
    (z : Fin n → ZMod (c₁ * c₂)) :
    eval₂ (Int.castRingHom (ZMod (c₁ * c₂))) z F = 0 ↔
      eval₂ (Int.castRingHom (ZMod c₁)) (fun i => leftProjection hc (z i)) F = 0 ∧
      eval₂ (Int.castRingHom (ZMod c₂)) (fun i => rightProjection hc (z i)) F = 0 := by
  constructor
  · intro hz
    constructor
    · simpa only [map_eval₂_int, map_zero] using congrArg (leftProjection hc) hz
    · simpa only [map_eval₂_int, map_zero] using congrArg (rightProjection hc) hz
  · rintro ⟨h₁, h₂⟩
    apply (ZMod.chineseRemainder hc).injective
    apply Prod.ext
    · change leftProjection hc _ = leftProjection hc 0
      simpa only [map_eval₂_int, map_zero] using h₁
    · change rightProjection hc _ = rightProjection hc 0
      simpa only [map_eval₂_int, map_zero] using h₂

/-- Reducing to a product residue class is equivalent to prescribing the
two projected residue classes separately. The smaller moduli are coprime
because each divides its corresponding larger modulus. -/
theorem residue_condition_crt_iff (k : Fin n → ℤ) (hc : c₁.Coprime c₂)
    (hd₁ : d₁ ∣ c₁) (hd₂ : d₂ ∣ c₂) (z : Fin n → ZMod (c₁ * c₂)) :
    (∀ i, ZMod.castHom (Nat.mul_dvd_mul hd₁ hd₂) (ZMod (d₁ * d₂)) (z i) =
      (k i : ZMod (d₁ * d₂))) ↔
      (∀ i, ZMod.castHom hd₁ (ZMod d₁) (leftProjection hc (z i)) =
        (k i : ZMod d₁)) ∧
      (∀ i, ZMod.castHom hd₂ (ZMod d₂) (rightProjection hc (z i)) =
        (k i : ZMod d₂)) := by
  let hd : d₁.Coprime d₂ := (hc.of_dvd_left hd₁).of_dvd_right hd₂
  have hleft : (leftProjection hd).comp
      (ZMod.castHom (Nat.mul_dvd_mul hd₁ hd₂) (ZMod (d₁ * d₂))) =
      (ZMod.castHom hd₁ (ZMod d₁)).comp (leftProjection hc) := Subsingleton.elim _ _
  have hright : (rightProjection hd).comp
      (ZMod.castHom (Nat.mul_dvd_mul hd₁ hd₂) (ZMod (d₁ * d₂))) =
      (ZMod.castHom hd₂ (ZMod d₂)).comp (rightProjection hc) := Subsingleton.elim _ _
  constructor
  · intro hz
    constructor
    · intro i
      have hi := congrArg (leftProjection hd) (hz i)
      rw [← RingHom.comp_apply, hleft, RingHom.comp_apply, map_intCast] at hi
      exact hi
    · intro i
      have hi := congrArg (rightProjection hd) (hz i)
      rw [← RingHom.comp_apply, hright, RingHom.comp_apply, map_intCast] at hi
      exact hi
  · rintro ⟨h₁, h₂⟩ i
    apply (ZMod.chineseRemainder hd).injective
    apply Prod.ext
    · change leftProjection hd _ = leftProjection hd _
      rw [← RingHom.comp_apply, hleft, RingHom.comp_apply, map_intCast]
      exact h₁ i
    · change rightProjection hd _ = rightProjection hd _
      rw [← RingHom.comp_apply, hright, RingHom.comp_apply, map_intCast]
      exact h₂ i

/-- Pointwise CRT equivalence for the literal root and residue predicates. -/
theorem zero_in_residue_class_crt_iff (F : MvPolynomial (Fin n) ℤ)
    (k : Fin n → ℤ) (hc : c₁.Coprime c₂) (hd₁ : d₁ ∣ c₁) (hd₂ : d₂ ∣ c₂)
    (z : Fin n → ZMod (c₁ * c₂)) :
    (eval₂ (Int.castRingHom (ZMod (c₁ * c₂))) z F = 0 ∧
      ∀ i, ZMod.castHom (Nat.mul_dvd_mul hd₁ hd₂) (ZMod (d₁ * d₂)) (z i) =
        (k i : ZMod (d₁ * d₂))) ↔
    (eval₂ (Int.castRingHom (ZMod c₁)) (vectorEquiv hc n z).1 F = 0 ∧
      ∀ i, ZMod.castHom hd₁ (ZMod d₁) ((vectorEquiv hc n z).1 i) = (k i : ZMod d₁)) ∧
    (eval₂ (Int.castRingHom (ZMod c₂)) (vectorEquiv hc n z).2 F = 0 ∧
      ∀ i, ZMod.castHom hd₂ (ZMod d₂) ((vectorEquiv hc n z).2 i) = (k i : ZMod d₂)) := by
  rw [zero_crt_iff F hc, residue_condition_crt_iff k hc hd₁ hd₂]
  tauto

/-- Exact multiplicativity of the number of actual polynomial roots in
a fixed integral residue class. Nonzero natural moduli are positive, and
divisibility then also forces the residue moduli to be positive. -/
theorem card_zeros_in_residue_class_mul [NeZero c₁] [NeZero c₂]
    (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ) (hc : c₁.Coprime c₂)
    (hd₁ : d₁ ∣ c₁) (hd₂ : d₂ ∣ c₂) :
    (Finset.univ.filter fun z : Fin n → ZMod (c₁ * c₂) =>
      eval₂ (Int.castRingHom (ZMod (c₁ * c₂))) z F = 0 ∧
      ∀ i, ZMod.castHom (Nat.mul_dvd_mul hd₁ hd₂) (ZMod (d₁ * d₂)) (z i) =
        (k i : ZMod (d₁ * d₂))).card =
    (Finset.univ.filter fun z : Fin n → ZMod c₁ =>
      eval₂ (Int.castRingHom (ZMod c₁)) z F = 0 ∧
      ∀ i, ZMod.castHom hd₁ (ZMod d₁) (z i) = (k i : ZMod d₁)).card *
    (Finset.univ.filter fun z : Fin n → ZMod c₂ =>
      eval₂ (Int.castRingHom (ZMod c₂)) z F = 0 ∧
      ∀ i, ZMod.castHom hd₂ (ZMod d₂) (z i) = (k i : ZMod d₂)).card := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_equiv (vectorEquiv hc n)
  intro z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  exact zero_in_residue_class_crt_iff F k hc hd₁ hd₂ z

end CubicTenVariables.PolynomialResidueCRT
