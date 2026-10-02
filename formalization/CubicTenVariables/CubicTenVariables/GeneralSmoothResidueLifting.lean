import CubicTenVariables.SmoothResidueLifting

/-! Exact smooth lifting for arbitrary integral multivariate polynomials.
The square-step Taylor remainder is proved by polynomial induction, without
homogeneity, a degree bound, or division by any residue characteristic. -/
noncomputable section
namespace CubicTenVariables.GeneralSmoothResidueLifting
open MvPolynomial HessianTheorem11 CubicTaylorExpansion PrimePowerFibers
open SmoothResidueLifting
open scoped BigOperators
variable {n : ℕ}

@[simp] theorem directional_C {R : Type*} [CommRing R]
    (a : R) (y x : Fin n → R) : directional (C a) y x = 0 := by
  simp [directional, gradient, dotProduct]

@[simp] theorem directional_X {R : Type*} [CommRing R]
    (i : Fin n) (y x : Fin n → R) : directional (X i) y x = x i := by
  classical
  simp [directional, gradient, dotProduct, Pi.single_apply]

/-- The actual evaluated directional derivative obeys the product rule. -/
theorem directional_mul {R : Type*} [CommRing R]
    (F G : MvPolynomial (Fin n) R) (y x : Fin n → R) :
    directional (F * G) y x =
      directional F y x * eval y G + eval y F * directional G y x := by
  classical
  calc
    _ = ∑ i, ((x i * eval y (pderiv i F)) * eval y G +
        eval y F * (x i * eval y (pderiv i G))) := by
      change (∑ i, x i * eval y (pderiv i (F * G))) = _
      apply Finset.sum_congr rfl
      intro i _
      simp only [pderiv_mul, map_add, map_mul]
      ring
    _ = _ := by
      simp only [directional, gradient, dotProduct, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum]

/-- Division-free first-order Taylor congruence in an arbitrary commutative
ring. In particular it works over Z for polynomials of every degree. -/
theorem sq_dvd_eval_difference {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin n) R) (y x : Fin n → R) (m : R) :
    m ^ 2 ∣ eval (y + m • x) F - (eval y F + m * directional F y x) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG =>
    convert dvd_add hF hG using 1
    simp only [map_add, directional_add]
    ring
  | mul_X F i hF =>
    obtain ⟨k, hk⟩ := hF
    refine ⟨k * (y i + m * x i) + directional F y x * x i, ?_⟩
    have he : eval (y + m • x) F = eval y F + m * directional F y x + m ^ 2 * k := by
      linear_combination hk
    rw [directional_mul, directional_X]
    simp only [map_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [he]
    ring

/-- The zero equation above an integral base zero is precisely one linear
equation in the new digits. No division by 2 or 3 occurs. -/
theorem zero_digitLift_iff (p s : ℕ) [NeZero p] (hs : 1 ≤ s)
    (F : MvPolynomial (Fin n) ℤ)
    (y : Fin n → ℤ) (k : ℤ) (hk : eval y F = ((p ^ s : ℕ) : ℤ) * k)
    (x : Fin n → ZMod p) :
    eval₂ (Int.castRingHom (ZMod (p ^ (s + 1)))) (digitLift p s y x) F = 0 ↔
      (∑ i, ((eval y (pderiv i F) : ℤ) : ZMod p) * x i) = -(k : ZMod p) := by
  let xZ : Fin n → ℤ := fun i => (x i).val
  have hdiv : ((p ^ (s + 1) : ℕ) : ℤ) ∣ ((p ^ s : ℕ) : ℤ) ^ 2 := by
    exact_mod_cast (show p ^ (s + 1) ∣ (p ^ s) ^ 2 by
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega))
  have hrem := hdiv.trans (sq_dvd_eval_difference F y xZ ((p ^ s : ℕ) : ℤ))
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
    (F : MvPolynomial (Fin n) ℤ)
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
    (fun x => (zero_digitLift_iff p s hs F y k hk x).symm)
  have hcard : Nat.card {z : Fin n → ZMod (p ^ (s + 1)) // P z ∧ Q z} =
      p ^ (n - 1) := by
    rw [← Nat.card_congr (e.trans (Equiv.subtypeSubtypeEquivSubtypeInter P Q))]
    exact card_linear_fiber p (fun i => ((eval y (pderiv i F) : ℤ) : ZMod p))
      hgradient (-(k : ZMod p))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, P, Q] using hcard


end CubicTenVariables.GeneralSmoothResidueLifting
