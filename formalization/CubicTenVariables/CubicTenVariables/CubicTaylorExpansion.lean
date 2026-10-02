import HessianTheorem11.Polarization
import Mathlib.Data.Finsupp.Order

/-!
# Division-free Taylor expansion of homogeneous cubics

All identities here hold over arbitrary commutative rings. In particular,
they may be reduced modulo powers of 2 or 3. The quadratic term is the
actual integral expression `y · ∇F(z)`; it never uses an inverse of 2.
-/

noncomputable section
namespace CubicTenVariables.CubicTaylorExpansion

open MvPolynomial HessianTheorem11
open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The actual first directional derivative, evaluated at `x`. -/
def directional (F : MvPolynomial (Fin n) R) (x v : Fin n → R) : R :=
  dotProduct v (gradient F x)

/-- The integral quadratic term in cubic Taylor expansion at `y`. -/
def quadraticAt (F : MvPolynomial (Fin n) R) (y z : Fin n → R) : R :=
  directional F z y

@[simp] theorem directional_zero (x v : Fin n → R) : directional 0 x v = 0 := by
  simp [directional, gradient, dotProduct]

@[simp] theorem directional_add (F G : MvPolynomial (Fin n) R) (x v : Fin n → R) :
    directional (F + G) x v = directional F x v + directional G x v := by
  simp [directional, gradient, dotProduct, mul_add, Finset.sum_add_distrib]

private theorem exists_single_add_of_degree_succ (d : Fin n →₀ ℕ) (k : ℕ)
    (hd : d.degree = k + 1) :
    ∃ i e, d = Finsupp.single i 1 + e ∧ e.degree = k := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra! hz
    have : d = 0 := Finsupp.ext hz
    simp [this] at hd
  have hle : Finsupp.single i 1 ≤ d :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  obtain ⟨e, he⟩ := exists_add_of_le hle
  refine ⟨i, e, he, ?_⟩
  rw [he, map_add, Finsupp.degree_single] at hd
  omega

private theorem degree_two_decomposition (d : Fin n →₀ ℕ) (hd : d.degree = 2) :
    ∃ i j, d = Finsupp.single i 1 + Finsupp.single j 1 := by
  obtain ⟨i, e, rfl, he⟩ := exists_single_add_of_degree_succ d 1 hd
  obtain ⟨j, rfl⟩ := Finsupp.range_single_one.symm.subset he
  exact ⟨i, j, rfl⟩

private theorem degree_three_decomposition (d : Fin n →₀ ℕ) (hd : d.degree = 3) :
    ∃ i j k, d = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 := by
  obtain ⟨i, e, rfl, he⟩ := exists_single_add_of_degree_succ d 2 hd
  obtain ⟨j, k, rfl⟩ := degree_two_decomposition e he
  exact ⟨i, j, k, (add_assoc _ _ _).symm⟩

private theorem directional_two_X (c : R) (i j : Fin n) (x v : Fin n → R) :
    directional (C c * X i * X j) x v = c * (v i * x j + x i * v j) := by
  classical
  simp [directional, gradient, dotProduct, Derivation.leibniz, Pi.single_apply,
    mul_add, Finset.sum_add_distrib, mul_ite]
  simp only [apply_ite, map_zero, map_mul, eval_C, eval_X]
  simp only [mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

private theorem directional_three_X (c : R) (i j k : Fin n) (x v : Fin n → R) :
    directional (C c * X i * X j * X k) x v =
      c * (v i * x j * x k + x i * v j * x k + x i * x j * v k) := by
  classical
  simp [directional, gradient, dotProduct, Derivation.leibniz, Pi.single_apply,
    mul_add, Finset.sum_add_distrib, mul_ite]
  simp only [apply_ite, map_zero, map_mul, eval_C, eval_X]
  simp only [mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- A homogeneous quadratic has its division-free, first-order cross term. -/
theorem eval_quadratic_add (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 2)
    (x y : Fin n → R) :
    eval (x + y) F = eval x F + eval y F + directional F x y := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add F G _ _ hF hG => simp only [map_add, directional_add, hF, hG]; ring
  | monomial d c hd =>
    have hd' : d.degree = 2 := by
      simpa [Finsupp.degree_eq_weight_one] using hd
    obtain ⟨i, j, rfl⟩ := degree_two_decomposition d hd'
    have hmon : monomial (Finsupp.single i 1 + Finsupp.single j 1) c =
        C c * X i * X j := by
      simp only [X, C_apply, monomial_mul, zero_add, mul_one]
    rw [hmon, directional_two_X]
    simp only [map_mul, eval_C, eval_X, Pi.add_apply]
    ring

/-- Cubic Taylor expansion, with coefficients valid in every residue characteristic. -/
theorem eval_cubic_add_smul (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (y z : Fin n → R) (a : R) :
    eval (y + a • z) F = eval y F + a * directional F y z +
      a ^ 2 * quadraticAt F y z + a ^ 3 * eval z F := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simp [quadraticAt]
  | add F G _ _ hF hG =>
    simp only [map_add, directional_add, quadraticAt, hF, hG] at *
    ring
  | monomial d c hd =>
    have hd' : d.degree = 3 := by
      simpa [Finsupp.degree_eq_weight_one] using hd
    obtain ⟨i, j, k, rfl⟩ := degree_three_decomposition d hd'
    have hmon : monomial (Finsupp.single i 1 + Finsupp.single j 1 +
        Finsupp.single k 1) c = C c * X i * X j * X k := by
      simp only [X, C_apply, monomial_mul, zero_add, mul_one]
    rw [hmon]
    simp only [quadraticAt, directional_three_X, map_mul, eval_C, eval_X,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Actual gradients of a cubic expand quadratically, without factorial denominators. -/
theorem gradient_add (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (x y : Fin n → R) :
    gradient F (x + y) = gradient F x + gradient F y + (hessian F x).mulVec y := by
  ext i
  have he := eval_quadratic_add (pderiv i F) hF.pderiv x y
  simpa [directional, gradient, hessian, hessianPolynomial, Matrix.mulVec,
    dotProduct, mul_comm] using he

/-- The polar form of the integral quadratic term is exactly the cubic Hessian. -/
theorem quadraticAt_add (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (y z h : Fin n → R) :
    quadraticAt F y (z + h) = quadraticAt F y z + quadraticAt F y h +
      dotProduct z ((hessian F y).mulVec h) := by
  unfold quadraticAt directional
  rw [gradient_add F hF, dotProduct_add, dotProduct_add]
  congr 1
  change polarization F y h z = polarization F z h y
  rw [polarization_swap_first, polarization_swap_last hF, polarization_swap_first]

/-- Twice the integral quadratic term equals the familiar Hessian expression.
This equality does not permit division by two in an arbitrary ring. -/
theorem two_mul_quadraticAt (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (y z : Fin n → R) :
    2 * quadraticAt F y z = dotProduct z ((hessian F y).mulVec z) := by
  have he : polarization F y z z = 2 * quadraticAt F y z := by
    rw [polarization, hessian_mulVec_self hF]
    simp [quadraticAt, directional, dotProduct, Finset.mul_sum,
      mul_left_comm]
  rw [← he]
  change polarization F y z z = polarization F z z y
  rw [polarization_rotate hF, polarization_swap_last hF]

/-- Taylor expansion after an actual coefficient homomorphism, including
integer coefficients evaluated in any prime-power residue ring. -/
theorem eval₂_cubic_add_smul {S : Type*} [CommRing S]
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3) (f : R →+* S)
    (y z : Fin n → S) (a : S) :
    eval₂ f (y + a • z) F = eval₂ f y F +
      a * dotProduct z (fun i => eval₂ f y (pderiv i F)) +
      a ^ 2 * dotProduct y (fun i => eval₂ f z (pderiv i F)) +
      a ^ 3 * eval₂ f z F := by
  have he := eval_cubic_add_smul (MvPolynomial.map f F) (hF.map f) y z a
  simpa only [quadraticAt, directional, dotProduct, gradient, pderiv_map,
    ← eval₂_eq_eval_map] using he

/-- A square-zero step removes the actual quadratic and cubic remainders. -/
theorem eval_cubic_add_smul_of_sq_eq_zero
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (y z : Fin n → R) (a : R) (ha : a ^ 2 = 0) :
    eval (y + a • z) F = eval y F + a * directional F y z := by
  have ha3 : a ^ 3 = 0 := by
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, ha, zero_mul]
  simpa only [ha, ha3, zero_mul, add_zero] using eval_cubic_add_smul F hF y z a

/-- The exact phase algebra behind the first lift. Both the scalar and
vector move by the same square-zero step; no character or sum is assumed. -/
theorem first_lift_phase_of_sq_eq_zero
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (y h v : Fin n → R) (a e m : R) (hm : m ^ 2 = 0) :
    (a + m * e) * eval (y + m • h) F + dotProduct v (y + m • h) =
      a * eval y F + dotProduct v y +
        m * (e * eval y F + dotProduct (a • gradient F y + v) h) := by
  rw [eval_cubic_add_smul_of_sq_eq_zero F hF y h m hm]
  simp only [dotProduct_add, dotProduct_smul, add_dotProduct, smul_dotProduct,
    smul_eq_mul]
  rw [show dotProduct (gradient F y) h = directional F y h by
    exact dotProduct_comm _ _]
  linear_combination e * directional F y h * hm

/-- The square-zero step in modulus `A²T` is the literal integer `AT`.
No primality, unit, or coprimality premise is needed for this algebra. -/
theorem first_lift_phase_zmod (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ)
    (y h v : Fin n → ZMod (A ^ 2 * T)) (a e : ZMod (A ^ 2 * T)) :
    (a + ((A * T : ℕ) : ZMod (A ^ 2 * T)) * e) *
        eval₂ (Int.castRingHom (ZMod (A ^ 2 * T))) (y + (A * T : ℕ) • h) F +
        dotProduct v (y + (A * T : ℕ) • h) =
      a * eval₂ (Int.castRingHom (ZMod (A ^ 2 * T))) y F + dotProduct v y +
        ((A * T : ℕ) : ZMod (A ^ 2 * T)) *
          (e * eval₂ (Int.castRingHom (ZMod (A ^ 2 * T))) y F +
            dotProduct (a • (fun i =>
              eval₂ (Int.castRingHom (ZMod (A ^ 2 * T))) y (pderiv i F)) + v) h) := by
  let f := Int.castRingHom (ZMod (A ^ 2 * T))
  have hm : ((A * T : ℕ) : ZMod (A ^ 2 * T)) ^ 2 = 0 := by
    calc
      _ = ((A ^ 2 * T : ℕ) : ZMod (A ^ 2 * T)) * (T : ZMod (A ^ 2 * T)) := by
        push_cast
        ring
      _ = 0 := by simp
  have he := first_lift_phase_of_sq_eq_zero (MvPolynomial.map f F) (hF.map f)
    y h v a e ((A * T : ℕ) : ZMod (A ^ 2 * T)) hm
  simpa only [dotProduct, gradient, Pi.add_apply, Pi.smul_apply, pderiv_map,
    ← eval₂_eq_eval_map, f, Nat.cast_smul_eq_nsmul]
    using he

end CubicTenVariables.CubicTaylorExpansion
