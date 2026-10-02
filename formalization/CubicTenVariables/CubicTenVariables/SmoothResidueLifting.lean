import CubicTenVariables.CubicTaylorExpansion
import CubicTenVariables.PrimePowerFibers
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Field.ZMod

/-!
# Exact one-step lifting at a smooth residue zero

Actual residue classes modulo p^(s+1), with their actual reduction modulo
p^s retained, are parametrized by the next p-adic digit vector. Cubic Taylor
expansion leaves one nonzero linear equation in those digits. This uses
only finite algebra, including in residue characteristics 2 and 3.
-/

noncomputable section
namespace CubicTenVariables.SmoothResidueLifting

open MvPolynomial HessianTheorem11 CubicTaylorExpansion PrimePowerFibers
open scoped BigOperators

variable {n : ℕ}

/-- Multiplication by p^s raises the zero-congruence modulus by exactly s. -/
theorem step_mul_cast_eq_zero_iff (p s : ℕ) [NeZero p] (z : ℤ) :
    ((((p ^ s : ℕ) : ℤ) * z : ℤ) : ZMod (p ^ (s + 1))) = 0 ↔ (z : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [pow_succ, Nat.cast_mul, mul_dvd_mul_iff_left]
  exact_mod_cast pow_ne_zero s (NeZero.ne p)

/-- The next-digit parametrization is shifted by the supplied integer center,
so negative or noncanonical representatives are allowed. -/
def digitLift (p s : ℕ) (y : Fin n → ℤ) (x : Fin n → ZMod p) :
    Fin n → ZMod (p ^ (s + 1)) :=
  fun i => ((y i + ((p ^ s : ℕ) : ℤ) * (x i).val : ℤ) : ZMod (p ^ (s + 1)))

theorem reduction_digitLift (p s : ℕ) (y : Fin n → ℤ) (x : Fin n → ZMod p)
    (i : Fin n) :
    reduction p (Nat.le_succ s) (digitLift p s y x i) = (y i : ZMod (p ^ s)) := by
  rw [digitLift, map_intCast]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, zero_mul, add_zero]

theorem digitLift_injective (p s : ℕ) [NeZero p] (y : Fin n → ℤ) :
    Function.Injective (digitLift p s y) := by
  intro x x' h
  funext i
  have hi := congrFun h i
  have hz : ((((p ^ s : ℕ) : ℤ) * ((x i).val - (x' i).val) : ℤ) :
      ZMod (p ^ (s + 1))) = 0 := by
    simp only [digitLift, Int.cast_add, Int.cast_mul, Int.cast_sub,
      Int.cast_natCast] at hi ⊢
    linear_combination hi
  have hsmall := (step_mul_cast_eq_zero_iff p s
    ((x i).val - (x' i).val)).mp hz
  simpa only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    sub_eq_zero] using hsmall

/-- A genuine equivalence with the entire literal reduction fiber. -/
def digitLiftEquiv (p s : ℕ) [Fact p.Prime] (y : Fin n → ℤ) :
    (Fin n → ZMod p) ≃ {z : Fin n → ZMod (p ^ (s + 1)) //
      ∀ i, reduction p (Nat.le_succ s) (z i) = (y i : ZMod (p ^ s))} := by
  classical
  let f : (Fin n → ZMod p) → {z : Fin n → ZMod (p ^ (s + 1)) //
      ∀ i, reduction p (Nat.le_succ s) (z i) = (y i : ZMod (p ^ s))} :=
    fun x => ⟨digitLift p s y x, reduction_digitLift p s y x⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨fun x x' h => digitLift_injective p s y (congrArg Subtype.val h), ?_⟩
  simp only [← Nat.card_eq_fintype_card]
  rw [card_vector_reduction_fiber]
  simp

@[simp] theorem digitLiftEquiv_apply (p s : ℕ) [Fact p.Prime]
    (y : Fin n → ℤ) (x : Fin n → ZMod p) :
    (digitLiftEquiv p s y x).val = digitLift p s y x := rfl

/-- A nonzero linear equation over the prime field has exactly p^(n-1) solutions. -/
theorem card_linear_fiber (p : ℕ) [Fact p.Prime] (g : Fin n → ZMod p)
    (hg : ∃ i, g i ≠ 0) (b : ZMod p) :
    Nat.card {x : Fin n → ZMod p // (∑ i, g i * x i) = b} = p ^ (n - 1) := by
  classical
  obtain ⟨i, hi⟩ := hg
  let f : (Fin n → ZMod p) →+ ZMod p :=
    { toFun := fun x => ∑ i, g i * x i
      map_zero' := by simp
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib] }
  have hf : Function.Surjective f := by
    intro c
    refine ⟨Pi.single i (c / g i), ?_⟩
    simp [f, Pi.single_apply, mul_ite]
    field_simp
  have h := card_fiber_mul_card_of_surjective f hf b
  have hn : 1 ≤ n := by have := i.isLt; omega
  apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
  calc
    Nat.card {x : Fin n → ZMod p // (∑ i, g i * x i) = b} * p =
        p ^ n := by simpa [f, Nat.card_fun, Nat.card_zmod] using h
    _ = p ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hn]

/-- The exact integer Taylor remainder is divisible by the square of the step. -/
theorem sq_dvd_eval_difference (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (y x : Fin n → ℤ) (m : ℤ) :
    m ^ 2 ∣ eval (y + m • x) F - (eval y F + m * directional F y x) := by
  refine ⟨quadraticAt F y x + m * eval x F, ?_⟩
  rw [eval_cubic_add_smul F hF]
  ring

theorem cast_eval_int (F : MvPolynomial (Fin n) ℤ) (q : ℕ) (x : Fin n → ℤ) :
    ((eval x F : ℤ) : ZMod q) = eval₂ (Int.castRingHom (ZMod q))
      (fun i => (x i : ZMod q)) F := by
  simpa only [Function.comp_def, Int.coe_castRingHom, eval₂_eq_eval_map] using
    map_eval (Int.castRingHom (ZMod q)) x F

/-- The zero equation above an integral base zero is precisely one linear
equation in the new digits. No division by 2 or 3 occurs. -/
theorem zero_digitLift_iff (p s : ℕ) [NeZero p] (hs : 1 ≤ s)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (y : Fin n → ℤ) (k : ℤ) (hk : eval y F = ((p ^ s : ℕ) : ℤ) * k)
    (x : Fin n → ZMod p) :
    eval₂ (Int.castRingHom (ZMod (p ^ (s + 1)))) (digitLift p s y x) F = 0 ↔
      (∑ i, ((eval y (pderiv i F) : ℤ) : ZMod p) * x i) = -(k : ZMod p) := by
  let xZ : Fin n → ℤ := fun i => (x i).val
  have hdiv : ((p ^ (s + 1) : ℕ) : ℤ) ∣ ((p ^ s : ℕ) : ℤ) ^ 2 := by
    exact_mod_cast (show p ^ (s + 1) ∣ (p ^ s) ^ 2 by
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega))
  have hrem := hdiv.trans (sq_dvd_eval_difference F hF y xZ ((p ^ s : ℕ) : ℤ))
  have hcast : ((eval (y + ((p ^ s : ℕ) : ℤ) • xZ) F : ℤ) :
        ZMod (p ^ (s + 1))) =
      ((((p ^ s : ℕ) : ℤ) * (k + directional F y xZ) : ℤ) : ZMod (p ^ (s + 1))) := by
    apply sub_eq_zero.mp
    rw [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    convert hrem using 1
    rw [hk]
    ring
  rw [show eval₂ (Int.castRingHom (ZMod (p ^ (s + 1)))) (digitLift p s y x) F =
      ((eval (y + ((p ^ s : ℕ) : ℤ) • xZ) F : ℤ) : ZMod (p ^ (s + 1))) by
        rw [cast_eval_int]; rfl, hcast, step_mul_cast_eq_zero_iff]
  simp only [directional, dotProduct, gradient, Int.cast_add, Int.cast_sum,
    Int.cast_mul, xZ, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
  exact add_eq_zero_iff_eq_neg'

/-- Exactly p^(n-1) actual zero residue classes modulo p^(s+1) lie above
a smooth zero represented by y modulo p^s. The reduction condition remains
in the displayed global finite filter, not just in a digit-vector count. -/
theorem card_smooth_zero_lifts_one_step (p s : ℕ) [Fact p.Prime] (hs : 1 ≤ s)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (y : Fin n → ℤ) (hy : ((p ^ s : ℕ) : ℤ) ∣ eval y F)
    (hgradient : ∃ i, ((eval y (pderiv i F) : ℤ) : ZMod p) ≠ 0) :
    (Finset.univ.filter fun z : Fin n → ZMod (p ^ (s + 1)) =>
      (∀ i, reduction p (Nat.le_succ s) (z i) = (y i : ZMod (p ^ s))) ∧
      eval₂ (Int.castRingHom (ZMod (p ^ (s + 1)))) z F = 0).card = p ^ (n - 1) := by
  classical
  obtain ⟨k, hk⟩ := hy
  let P : (Fin n → ZMod (p ^ (s + 1))) → Prop := fun z =>
    ∀ i, reduction p (Nat.le_succ s) (z i) = (y i : ZMod (p ^ s))
  let Q : (Fin n → ZMod (p ^ (s + 1))) → Prop := fun z =>
    eval₂ (Int.castRingHom (ZMod (p ^ (s + 1)))) z F = 0
  let e := (digitLiftEquiv p s y).subtypeEquiv
    (p := fun x => (∑ i, ((eval y (pderiv i F) : ℤ) : ZMod p) * x i) = -(k : ZMod p))
    (q := fun z => Q z.val)
    (fun x => (zero_digitLift_iff p s hs F hF y k hk x).symm)
  have hcard : Nat.card {z : Fin n → ZMod (p ^ (s + 1)) // P z ∧ Q z} =
      p ^ (n - 1) := by
    rw [← Nat.card_congr (e.trans (Equiv.subtypeSubtypeEquivSubtypeInter P Q))]
    exact card_linear_fiber p (fun i => ((eval y (pderiv i F) : ℤ) : ZMod p))
      hgradient (-(k : ZMod p))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, P, Q] using hcard

end CubicTenVariables.SmoothResidueLifting
