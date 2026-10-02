import CubicTenVariables.IntegralGradientFibers
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Cubic-gradient scaling and exact transport of local residue fibers

The first partials of a homogeneous cubic scale quadratically over arbitrary
commutative rings, including p-adic integers and prime-power residue rings.
Multiplication by a p-adic unit induces an actual bijection of full residue
tuples and transports the displayed fibers, including their genuine integral
lifts. The gradient multiplier absorbs the square of the reduced unit, and
the prescribed untouched coordinates are multiplied by its inverse.
-/

noncomputable section

namespace CubicTenVariables.CubicGradientScaling

open MvPolynomial LocalCongruenceFibers IntegralGradientPatch IntegralGradientFibers

/-- Homogeneous evaluation extracts a common scalar over commutative semirings. -/
theorem homogeneous_eval₂_smul
    {R S σ : Type*} [CommSemiring R] [CommSemiring S] {d : ℕ}
    (F : MvPolynomial σ R) (hF : F.IsHomogeneous d) (f : R →+* S)
    (v : σ → S) (a : S) :
    eval₂ f (a • v) F = a ^ d * eval₂ f v F := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add F G _ _ hF hG => simp [hF, hG, mul_add]
  | monomial e c he =>
    have hd : (∑ i ∈ e.support, e i) = d := by
      simpa [Finsupp.weight_apply] using he
    simp [eval₂_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hd, mul_left_comm]

/-- Literal first partials of a cubic scale by the square, without a field hypothesis. -/
theorem eval₂_partial_smul
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (F : MvPolynomial σ R) (hF : F.IsHomogeneous 3) (f : R →+* S)
    (i : σ) (v : σ → S) (a : S) :
    eval₂ f (a • v) (pderiv i F) = a ^ 2 * eval₂ f v (pderiv i F) :=
  homogeneous_eval₂_smul (pderiv i F) hF.pderiv f v a

variable (p : ℕ) [Fact p.Prime] {n r : ℕ}

theorem integralSelectedGradient_smul (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (rows : Fin r → Fin n)
    (v : Fin n → ℤ_[p]) (a : ℤ_[p]) :
    integralSelectedGradient p F rows (a • v) = a ^ 2 • integralSelectedGradient p F rows v := by
  funext i
  exact eval₂_partial_smul F hF (Int.castRingHom ℤ_[p]) (rows i) v a

omit [Fact p.Prime] in
theorem modularSelectedGradient_smul (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (rows : Fin r → Fin n) (s : ℕ)
    (v : Fin n → ZMod (p ^ s)) (a : ZMod (p ^ s)) :
    modularSelectedGradient p F rows s (a • v) =
      a ^ 2 • modularSelectedGradient p F rows s v := by
  funext i
  exact eval₂_partial_smul F hF (Int.castRingHom (ZMod (p ^ s))) (rows i) v a

/-- The actual reduction of a p-adic unit, retained as a unit of the residue ring. -/
def residueUnit (s : ℕ) (a : ℤ_[p]ˣ) : (ZMod (p ^ s))ˣ :=
  Units.map (PadicInt.toZModPow s).toMonoidHom a

@[simp] theorem coe_residueUnit (s : ℕ) (a : ℤ_[p]ˣ) :
    (residueUnit p s a : ZMod (p ^ s)) = PadicInt.toZModPow s (a : ℤ_[p]) := rfl

/-- Scalar multiplication by the reduced unit is an actual residue-vector bijection. -/
def residueScalarEquiv (s : ℕ) (a : ℤ_[p]ˣ) :
    (Fin n → ZMod (p ^ s)) ≃ (Fin n → ZMod (p ^ s)) where
  toFun v := (residueUnit p s a : ZMod (p ^ s)) • v
  invFun v := (↑((residueUnit p s a)⁻¹) : ZMod (p ^ s)) • v
  left_inv v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, Units.inv_mul, one_mul]
  right_inv v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]

@[simp] theorem residueScalarEquiv_apply (s : ℕ) (a : ℤ_[p]ˣ)
    (v : Fin n → ZMod (p ^ s)) :
    residueScalarEquiv p s a v = (residueUnit p s a : ZMod (p ^ s)) • v := rfl

/-- Reduction commutes with literal integral scalar multiplication. -/
theorem toZModPow_smul (s : ℕ) (a : ℤ_[p]ˣ) (z : Fin n → ℤ_[p]) (k : Fin n) :
    PadicInt.toZModPow s (((a : ℤ_[p]) • z) k) =
      ((residueUnit p s a : ZMod (p ^ s)) • (fun j => PadicInt.toZModPow s (z j))) k := by
  simp [Pi.smul_apply, smul_eq_mul]

/-- An integral lift in the scaled image is exactly a scaled genuine lift in U. -/
theorem exists_lift_unit_image_iff (s : ℕ) (a : ℤ_[p]ˣ)
    (U : Set (Fin n → ℤ_[p])) (v : Fin n → ZMod (p ^ s)) :
    (∃ z ∈ (fun z : Fin n → ℤ_[p] => (a : ℤ_[p]) • z) '' U,
      ∀ k, PadicInt.toZModPow s (z k) =
        ((residueUnit p s a : ZMod (p ^ s)) • v) k) ↔
    ∃ z ∈ U, ∀ k, PadicInt.toZModPow s (z k) = v k := by
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hv⟩
    refine ⟨z, hz, fun k => ?_⟩
    apply (residueUnit p s a).isUnit.mul_left_cancel
    simpa only [Pi.smul_apply, smul_eq_mul, map_mul, coe_residueUnit] using hv k
  · rintro ⟨z, hz, hv⟩
    refine ⟨(a : ℤ_[p]) • z, ⟨z, hz, rfl⟩, fun k => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, coe_residueUnit, hv]

/-- Exact membership transport. The multiplier absorbs the square of the
reduced scalar; untouched targets absorb its inverse. -/
theorem mem_unitModularFiber_unit_image_iff
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (rows cols : Fin r → Fin n) (s : ℕ) (U : Set (Fin n → ℤ_[p]))
    (a : ℤ_[p]ˣ) (u : (ZMod (p ^ s))ˣ)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s))
    (v : Fin n → ZMod (p ^ s)) :
    (residueUnit p s a : ZMod (p ^ s)) • v ∈
      unitModularFiber p F rows cols s ((fun z => (a : ℤ_[p]) • z) '' U) u b c ↔
    v ∈ unitModularFiber p F rows cols s U (u * residueUnit p s a ^ 2)
      (fun j => (↑((residueUnit p s a)⁻¹) : ZMod (p ^ s)) * b j) c := by
  simp only [unitModularFiber, Set.mem_setOf_eq]
  rw [exists_lift_unit_image_iff, modularSelectedGradient_smul p F hF]
  simp only [Pi.smul_apply, smul_eq_mul, Units.val_mul, Units.val_pow_eq_pow_val,
    mul_assoc, Units.eq_inv_mul_iff_mul_eq]

/-- Exact cardinality equality under unit scaling, for full residue tuples
with actual lifts in the respective integral sets. -/
theorem card_unitModularFiber_unit_image
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (rows cols : Fin r → Fin n) (s : ℕ) (U : Set (Fin n → ℤ_[p]))
    (a : ℤ_[p]ˣ) (u : (ZMod (p ^ s))ˣ)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    Nat.card (unitModularFiber p F rows cols s
      ((fun z => (a : ℤ_[p]) • z) '' U) u b c) =
    Nat.card (unitModularFiber p F rows cols s U (u * residueUnit p s a ^ 2)
      (fun j => (↑((residueUnit p s a)⁻¹) : ZMod (p ^ s)) * b j) c) := by
  symm
  exact Nat.card_congr ((residueScalarEquiv p s a).subtypeEquiv (fun v =>
    (mem_unitModularFiber_unit_image_iff p F hF rows cols s U a u b c v).symm))

/-- A uniform bound on U transfers to every unit-scaled image with the very
same constant, independently of the unit and all residue targets. -/
theorem unit_image_fiber_bound
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (rows cols : Fin r → Fin n) (U : Set (Fin n → ℤ_[p])) (N : ℕ)
    (hcount : ∀ (s : ℕ) (u : (ZMod (p ^ s))ˣ)
      (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)),
      Nat.card (unitModularFiber p F rows cols s U u b c) ≤ N)
    (a : ℤ_[p]ˣ) (s : ℕ) (u : (ZMod (p ^ s))ˣ)
    (b : Untouched cols → ZMod (p ^ s)) (c : Fin r → ZMod (p ^ s)) :
    Nat.card (unitModularFiber p F rows cols s
      ((fun z => (a : ℤ_[p]) • z) '' U) u b c) ≤ N := by
  rw [card_unitModularFiber_unit_image p F hF]
  exact hcount s _ _ c

end CubicTenVariables.CubicGradientScaling
