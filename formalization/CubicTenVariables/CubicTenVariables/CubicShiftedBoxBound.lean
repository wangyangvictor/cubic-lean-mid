import CubicTenVariables.CubicDifferenceCorrelation
import CubicTenVariables.FiniteShiftDifferencing
import CubicTenVariables.GoodHessianKernelAverage
import CubicTenVariables.HessianKernelCRT

/-! Finite differencing of the actual ten-variable complete cubic sum over
a one-sided integer shift box. Its differences lie in the full symmetric
integer box, including zero. The proved Hessian-kernel average supplies the
only estimate, with one constant before both modulus and radius. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicShiftedBoxBound
open MvPolynomial HessianTheorem11
open scoped BigOperators

/-- The actual one-sided shift box, including both endpoints. -/
def shiftBox (B : ℕ) : Finset (Fin 10 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc 0 (B : ℤ)

@[simp] theorem mem_shiftBox {B : ℕ} {x : Fin 10 → ℤ} :
    x ∈ shiftBox B ↔ ∀ i, 0 ≤ x i ∧ x i ≤ (B : ℤ) := by
  simp only [shiftBox, Fintype.mem_piFinset, Finset.mem_Icc]

@[simp] theorem card_shiftBox (B : ℕ) : (shiftBox B).card = (B + 1)^10 := by
  have hcard : (Finset.Icc (0 : ℤ) (B : ℤ)).card = B + 1 := by
    rw [Int.card_Icc]
    have he : (B : ℤ) + 1 - 0 = ((B + 1 : ℕ) : ℤ) := by omega
    rw [he, Int.toNat_natCast]
  simp [shiftBox, Fintype.card_piFinset, hcard]

theorem shiftBox_nonempty (B : ℕ) : (shiftBox B).Nonempty := by
  refine ⟨0, mem_shiftBox.mpr ?_⟩
  intro i
  simp

theorem sub_mem_integerBox {B : ℕ} {x y : Fin 10 → ℤ}
    (hx : x ∈ shiftBox B) (hy : y ∈ shiftBox B) : x - y ∈ integerBox 10 B := by
  rw [mem_integerBox]
  intro i
  obtain ⟨hx0, hxB⟩ := mem_shiftBox.mp hx i
  obtain ⟨hy0, hyB⟩ := mem_shiftBox.mp hy i
  change |x i - y i| ≤ (B : ℤ)
  rw [abs_le]
  constructor <;> omega

/-- Coordinatewise reduction of the integer shift, without injectivity. -/
def castVector (q : ℕ) : (Fin 10 → ℤ) →+ (Fin 10 → ZMod q) where
  toFun h := fun i => (h i : ZMod q)
  map_zero' := by ext i; simp
  map_add' := by intro x y; ext i; simp

private theorem stdAddChar_mul_conj_eq_sub {q : ℕ} [NeZero q] (u v : ZMod q) :
    ZMod.stdAddChar u * starRingEnd ℂ (ZMod.stdAddChar v) =
      ZMod.stdAddChar (u - v) := by
  calc
    _ = (ZMod.stdAddChar (u-v) * ZMod.stdAddChar v) *
        starRingEnd ℂ (ZMod.stdAddChar v) := by
      rw [← AddChar.map_add_eq_mul, sub_add_cancel]
    _ = _ := by
      rw [mul_assoc, QuadraticGaussBound.stdAddChar_mul_conj, mul_one]

/-- The actual shifted correlation is bounded by the square root of the
actual integral Hessian kernel after reduction modulo `q`. -/
theorem norm_correlation_le {q : ℕ} [NeZero q]
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (a : (ZMod q)ˣ) (h : Fin 10 → ℤ) :
    ‖∑ x : Fin 10 → ZMod q,
      ZMod.stdAddChar ((a : ZMod q) * eval₂ (Int.castRingHom (ZMod q))
        (x + castVector q h) F) *
      starRingEnd ℂ (ZMod.stdAddChar ((a : ZMod q) *
        eval₂ (Int.castRingHom (ZMod q)) x F))‖ ≤
      (q : ℝ)^5 * Real.sqrt (GoodHessianKernelAverage.kernelCard F q h : ℝ) := by
  let ρ := Int.castRingHom (ZMod q)
  have hsum : (∑ x : Fin 10 → ZMod q,
      ZMod.stdAddChar ((a : ZMod q) * eval₂ ρ (x + castVector q h) F) *
      starRingEnd ℂ (ZMod.stdAddChar ((a : ZMod q) * eval₂ ρ x F))) =
      ∑ x : Fin 10 → ZMod q,
        ZMod.stdAddChar ((a : ZMod q) *
          (eval (x + castVector q h) (map ρ F) - eval x (map ρ F))) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [stdAddChar_mul_conj_eq_sub, mul_sub]
    simp only [← eval₂_eq_eval_map]
  change ‖∑ x : Fin 10 → ZMod q,
      ZMod.stdAddChar ((a : ZMod q) * eval₂ ρ (x + castVector q h) F) *
      starRingEnd ℂ (ZMod.stdAddChar ((a : ZMod q) * eval₂ ρ x F))‖ ≤ _
  rw [hsum]
  have hsq := CubicDifferenceCorrelation.norm_sum_sq_le (map ρ F) (hF.map ρ)
    a (castVector q h)
  have hmatrix : hessian (map ρ F) (castVector q h) = (hessian F h).map ρ :=
    (HessianKernelCRT.hessian_map_eval ρ F h).symm
  rw [hmatrix] at hsq
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (q : ℝ)^10 * (GoodHessianKernelAverage.kernelCard F q h : ℝ) := hsq
    _ = ((q : ℝ)^5 * Real.sqrt (GoodHessianKernelAverage.kernelCard F q h : ℝ))^2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring

/-- One constant works before all positive moduli, all positive integer
shift radii and all unit cubic coefficients. This is the actual complete
sum, with the shift-box cardinality left multiplied on the left. -/
theorem exists_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (B : ℕ), 1 ≤ B →
      ∀ a : (ZMod q)ˣ,
      ((B : ℝ)+1)^10 *
        ‖∑ x : Fin 10 → ZMod q,
          ZMod.stdAddChar ((a : ZMod q) * eval₂ (Int.castRingHom (ZMod q)) x F)‖^2 ≤
        A * (q : ℝ)^15 * ((q : ℝ)+(B : ℝ)^3)^5 := by
  classical
  obtain ⟨A, hA, hbound⟩ := GoodHessianKernelAverage.exists_integer_box_bound F hF hzero
  refine ⟨A, hA, ?_⟩
  intro q _ B hB a
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let f : (Fin 10 → ZMod q) → ℂ := fun x =>
    ZMod.stdAddChar ((a : ZMod q) * eval₂ (Int.castRingHom (ZMod q)) x F)
  let M : (Fin 10 → ℤ) → ℝ := fun h =>
    (q : ℝ)^5 * Real.sqrt (GoodHessianKernelAverage.kernelCard F q h : ℝ)
  have h := FiniteShiftDifferencing.norm_sum_sq_le_of_difference_majorant
    f (castVector q) (shiftBox B) (integerBox 10 B) (shiftBox_nonempty B) M
    (fun h _ => by dsimp [M]; positivity)
    (fun x hx y hy => sub_mem_integerBox hx hy)
    (fun h _ => norm_correlation_le F hF a h)
  have h' : ((B : ℝ)+1)^10 * ‖∑ x, f x‖^2 ≤
      (q : ℝ)^10 * ∑ h ∈ integerBox 10 B, M h := by
    simpa [card_shiftBox, ZMod.card] using h
  calc
    _ ≤ (q : ℝ)^10 * ∑ h ∈ integerBox 10 B, M h := h'
    _ = (q : ℝ)^15 *
        ∑ h ∈ integerBox 10 B, Real.sqrt (GoodHessianKernelAverage.kernelCard F q h : ℝ) := by
      simp only [M, ← Finset.mul_sum]
      ring
    _ ≤ (q : ℝ)^15 * (A * ((q : ℝ)+(B : ℝ)^3)^5) :=
      mul_le_mul_of_nonneg_left (hbound q B hq hB) (by positivity)
    _ = _ := by ring

end CubicTenVariables.CubicShiftedBoxBound
