import CubicTenVariables.CubicQuadraticGauss
import CubicTenVariables.ResidueShiftKernel
import CubicTenVariables.HessianResidueKernel

/-! Second moments of actual cubic-gradient quadratic sums in residue
fibers. Orthogonality is applied after summing the fibers, so the surviving
kernel is at the quotient modulus, without a loss at common prime factors. -/

noncomputable section
namespace CubicTenVariables.ResidueFiberQuadraticMoment
open MvPolynomial HessianTheorem11 CubicTaylorExpansion QuadraticGaussBound
open scoped BigOperators

/-- The literal sum on one fiber of a finite map. -/
def fiberSum {α β : Type*} [Fintype α] [DecidableEq β]
    (π : α → β) (f : α → ℂ) (b : β) : ℂ :=
  ∑ x, if π x = b then f x else 0

private theorem sum_fiber_mul_conj {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (π : α → β) (f : α → ℂ) :
    (∑ b, fiberSum π f b * starRingEnd ℂ (fiberSum π f b)) =
      ∑ y, fiberSum π f (π y) * starRingEnd ℂ (f y) := by
  unfold fiberSum
  simp_rw [map_sum, apply_ite, map_zero, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- Exact differencing on all fibers of an additive map, with the actual
zero-reduction shifts retained. No surjectivity hypothesis is needed. -/
theorem fiber_moment_identity {c n : ℕ} [NeZero c]
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (π : (Fin n → ZMod c) →+ A)
    (Q : (Fin n → ZMod c) → ZMod c)
    (B : Matrix (Fin n) (Fin n) (ZMod c))
    (hQ : ∀ x z, Q (x+z) = Q x+Q z+dotProduct x (B.mulVec z)) :
    (∑ b, fiberSum π (fun x => ZMod.stdAddChar (Q x)) b *
      starRingEnd ℂ (fiberSum π (fun x => ZMod.stdAddChar (Q x)) b)) =
      (c:ℂ)^n * ∑ z ∈ Finset.univ.filter (fun z => π z = 0 ∧ B.mulVec z = 0),
        ZMod.stdAddChar (Q z) := by
  classical
  have hshift (y : Fin n → ZMod c) :
      fiberSum π (fun x => ZMod.stdAddChar (Q x)) (π y) =
      ∑ z, if π z = 0 then ZMod.stdAddChar (Q (y+z)) else 0 := by
    unfold fiberSum
    rw [← Equiv.sum_comp (Equiv.addLeft y) (fun x =>
      if π x = π y then ZMod.stdAddChar (Q x) else 0)]
    simp
  rw [sum_fiber_mul_conj]
  simp_rw [hshift, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z, if π z = 0 then
        ZMod.stdAddChar (Q z) * ∑ y : Fin n → ZMod c,
          ZMod.stdAddChar (dotProduct y (B.mulVec z)) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : π z = 0
      · simp only [hz, if_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [hQ, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
        calc
          _ = (ZMod.stdAddChar (Q y) * starRingEnd ℂ (ZMod.stdAddChar (Q y))) *
              (ZMod.stdAddChar (Q z) * ZMod.stdAddChar (dotProduct y (B.mulVec z))) := by ring
          _ = _ := by rw [stdAddChar_mul_conj, one_mul]
      · simp [hz]
    _ = _ := by
      simp_rw [sum_linear_phase]
      simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hπ : π z = 0 <;> by_cases hB : B.mulVec z = 0 <;>
        simp [hπ, hB, mul_comm]

/-- A second-moment bound retaining the simultaneous additive and matrix
kernel. This finite theorem is valid over even and composite moduli. -/
theorem sum_norm_sq_le_restricted_kernel {c n : ℕ} [NeZero c]
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (π : (Fin n → ZMod c) →+ A)
    (Q : (Fin n → ZMod c) → ZMod c)
    (B : Matrix (Fin n) (Fin n) (ZMod c))
    (hQ : ∀ x z, Q (x+z) = Q x+Q z+dotProduct x (B.mulVec z)) :
    (∑ b, ‖fiberSum π (fun x => ZMod.stdAddChar (Q x)) b‖^2) ≤
      (c:ℝ)^n * Nat.card {z : Fin n → ZMod c // π z = 0 ∧ B.mulVec z = 0} := by
  classical
  let T := fiberSum π (fun x => ZMod.stdAddChar (Q x))
  have hreal : (∑ b, T b * starRingEnd ℂ (T b)) =
      ((∑ b, ‖T b‖^2 : ℝ) : ℂ) := by
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_sum, Complex.ofReal_pow]
  have hnonneg : 0 ≤ ∑ b, ‖T b‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he := congrArg norm (fiber_moment_identity π Q B hQ)
  change ‖∑ b, T b * starRingEnd ℂ (T b)‖ = _ at he
  rw [hreal] at he
  have he' : (∑ b, ‖T b‖^2) = (c:ℝ)^n *
      ‖∑ z ∈ Finset.univ.filter (fun z => π z = 0 ∧ B.mulVec z = 0),
        ZMod.stdAddChar (Q z)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hnonneg,
      norm_mul, norm_pow, Complex.norm_natCast] at he
    exact he
  change (∑ b, ‖T b‖^2) ≤ _
  rw [he']
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ z ∈ Finset.univ.filter (fun z => π z = 0 ∧ B.mulVec z = 0),
        ‖ZMod.stdAddChar (Q z)‖ := norm_sum_le _ _
    _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Coordinatewise actual reduction, as an additive homomorphism. -/
def reductionVector {n : ℕ} (c d : ℕ) (hdc : d ∣ c) :
    (Fin n → ZMod c) →+ (Fin n → ZMod d) where
  toFun x := fun i => ZMod.castHom hdc (ZMod d) (x i)
  map_zero' := by funext i; exact map_zero _
  map_add' x y := by funext i; exact map_add _ _ _

/-- The actual cubic-gradient second moment over all residue fibers.
The RHS is the literal Hessian kernel at the quotient modulus. -/
theorem sum_norm_sq_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c)
    (a : (ZMod c)ˣ) (h : Fin n → ℤ) :
    (∑ b : Fin n → ZMod d,
      ‖∑ x : Fin n → ZMod c,
        if (fun i => ZMod.castHom hdc (ZMod d) (x i)) = b then
          ZMod.stdAddChar ((a : ZMod c) *
            ∑ i, (h i : ZMod c) * eval₂ (Int.castRingHom (ZMod c)) x (pderiv i F))
        else 0‖^2) ≤
      (c:ℝ)^n * Nat.card {t : Fin n → ZMod (c/d) //
        ((hessian F h).map (Int.castRingHom (ZMod (c/d)))).mulVec t = 0} := by
  classical
  let G := map (Int.castRingHom (ZMod c)) F
  let y : Fin n → ZMod c := fun i => (h i : ZMod c)
  let Q := fun x : Fin n → ZMod c => (a : ZMod c) * quadraticAt G y x
  let B := (hessian F h).map (Int.castRingHom (ZMod c))
  have hB : B = hessian G y := HessianResidueKernel.hessian_intCast F c h
  have hQ : ∀ x z, Q (x+z) = Q x+Q z+dotProduct x (((a:ZMod c) • B).mulVec z) := by
    intro x z
    dsimp only [Q]
    rw [quadraticAt_add G (hF.map _) y x z, Matrix.smul_mulVec, dotProduct_smul, hB]
    simp only [smul_eq_mul]
    ring
  have hbound := sum_norm_sq_le_restricted_kernel (reductionVector c d hdc) Q
    ((a:ZMod c) • B) hQ
  have hcard : Nat.card {z : Fin n → ZMod c //
      reductionVector c d hdc z = 0 ∧ ((a:ZMod c) • B).mulVec z = 0} =
      Nat.card {t : Fin n → ZMod (c/d) //
        ((hessian F h).map (Int.castRingHom (ZMod (c/d)))).mulVec t = 0} := by
    calc
      _ = Nat.card {z : Fin n → ZMod c //
          (∀ i, ZMod.castHom hdc (ZMod d) (z i) = 0) ∧ B.mulVec z = 0} := by
        apply Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
        simp only [reductionVector, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          funext_iff, Pi.zero_apply, Matrix.smul_mulVec, a.isUnit.smul_eq_zero]
      _ = _ := ResidueShiftKernel.card_restricted_kernel_div c d hdc (hessian F h)
  rw [hcard] at hbound
  simpa only [fiberSum, reductionVector, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Q, G, y, quadraticAt, directional, gradient, dotProduct, pderiv_map, eval_map] using hbound

end CubicTenVariables.ResidueFiberQuadraticMoment
