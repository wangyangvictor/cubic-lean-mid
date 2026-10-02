import CubicTenVariables.QuadraticTerminalBound

/-!
# The pointwise squarefull starT estimate in ten variables

Scalar regrouping retains both the cubic-zero and stationary-gradient
congruences. The kernel is the actual reduced Hessian kernel. All positive
moduli with d dividing c are allowed, including even moduli and one.
-/

noncomputable section
namespace CubicTenVariables.SquarefullStarT
open MvPolynomial HessianTheorem11 FirstLiftSum SecondLiftSum
open MixedRadixLifting QuadraticTerminalBound
open scoped BigOperators

/-- Adding a multiple of the residue modulus to the scalar preserves
both support conditions. No degree assumption is needed. -/
theorem supportCondition_scalar_add_mul_iff {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (c : ℕ) (a e : ℤ) (x v : Fin n → ℤ) :
    supportCondition F c (a+(c:ℤ)*e) x v ↔ supportCondition F c a x v := by
  unfold supportCondition
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  have he : (c : ℤ) ∣ (c : ℤ)*e*eval x (pderiv i F) := by
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have heq : (a+(c:ℤ)*e)*eval x (pderiv i F)+v i =
      (c:ℤ)*e*eval x (pderiv i F)+(a*eval x (pderiv i F)+v i) := by ring
  rw [heq]
  exact dvd_add_right he

/-- The scalar modulo c*d has exactly d representatives over each scalar
modulo c; the unit and support conditions depend only on the latter. -/
theorem weighted_scalar_regrouping {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (c d : ℕ) (hdc : d ∣ c)
    (v : Fin n → ℤ) (W : (Fin n → Fin c) → ℝ) :
    (∑ a : Fin (c*d), if Nat.Coprime a.val (c*d) then
      ∑ x : Fin n → Fin c,
        if supportCondition F c (a.val:ℤ) (integerVector x) v then W x else 0
      else 0) =
    (d : ℝ) * ∑ a : Fin c, if Nat.Coprime a.val c then
      ∑ x : Fin n → Fin c,
        if supportCondition F c (a.val:ℤ) (integerVector x) v then W x else 0
      else 0 := by
  classical
  rw [Nat.mul_comm c d, sum_mixedRadix d c]
  simp_rw [coprime_mixedRadix_iff d c hdc, mixedRadixEquiv_intCast,
    supportCondition_scalar_add_mul_iff]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- Remove the dimension-ten power from the square root exactly. -/
theorem residueKernelRoot_ten (F : MvPolynomial (Fin 10) ℤ)
    (c d : ℕ) [NeZero d] (x : Fin 10 → Fin c) :
    residueKernelRoot F c d x = (d : ℝ)^5 *
      Real.sqrt (Nat.card {h : Fin 10 → ZMod d //
        (hessian (map (Int.castRingHom (ZMod d)) F)
          (fun i => ((x i).val : ZMod d))).mulVec h = 0}) := by
  unfold residueKernelRoot
  rw [Real.sqrt_mul (by positivity)]
  have he : (d : ℝ)^10 = ((d : ℝ)^5)^2 := by ring
  rw [he, Real.sqrt_sq (by positivity)]

/-- The literal pointwise starT bound required by the ten-variable proof.
It uses no anisotropy, literature, squarefreeness, or odd-prime premise. -/
theorem norm_completeCubicSum_starT_ten_le
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c) (v : Fin 10 → ℤ) :
    ‖completeCubicSum F (c^2*d) v‖ ≤
      (c : ℝ)^11 * (d : ℝ)^6 *
        ∑ a : Fin c, if Nat.Coprime a.val c then
          ∑ x : Fin 10 → Fin c,
            if supportCondition F c (a.val:ℤ) (integerVector x) v then
              Real.sqrt (Nat.card {h : Fin 10 → ZMod d //
                (hessian (map (Int.castRingHom (ZMod d)) F)
                  (fun i => ((x i).val : ZMod d))).mulVec h = 0})
            else 0
          else 0 := by
  classical
  have hfirst := SecondLiftSum.norm_completeCubicSum_le F hF c d v
  have hkernel :
      (∑ a : Fin (c*d), if Nat.Coprime a.val (c*d) then
        ∑ x : Fin 10 → Fin c,
          if supportCondition F c (a.val:ℤ) (integerVector x) v then
            residueTerminalMax F c d x else 0
        else 0) ≤
      ∑ a : Fin (c*d), if Nat.Coprime a.val (c*d) then
        ∑ x : Fin 10 → Fin c,
          if supportCondition F c (a.val:ℤ) (integerVector x) v then
            residueKernelRoot F c d x else 0
        else 0 := by
    apply Finset.sum_le_sum
    intro a _
    split_ifs with ha
    · apply Finset.sum_le_sum
      intro x _
      split_ifs with hx
      · exact residueTerminalMax_le_kernelRoot F hF c d hdc x
      · rfl
    · rfl
  have h := hfirst.trans (mul_le_mul_of_nonneg_left hkernel (by positivity))
  rw [weighted_scalar_regrouping F c d hdc v] at h
  simp_rw [residueKernelRoot_ten] at h
  have hextract :
      (∑ a : Fin c, if Nat.Coprime a.val c then
        ∑ x : Fin 10 → Fin c,
          if supportCondition F c (a.val:ℤ) (integerVector x) v then
            (d : ℝ)^5 * Real.sqrt (Nat.card {h : Fin 10 → ZMod d //
              (hessian (map (Int.castRingHom (ZMod d)) F)
                (fun i => ((x i).val : ZMod d))).mulVec h = 0}) else 0
        else 0) =
      (d : ℝ)^5 * ∑ a : Fin c, if Nat.Coprime a.val c then
        ∑ x : Fin 10 → Fin c,
          if supportCondition F c (a.val:ℤ) (integerVector x) v then
            Real.sqrt (Nat.card {h : Fin 10 → ZMod d //
              (hessian (map (Int.castRingHom (ZMod d)) F)
                (fun i => ((x i).val : ZMod d))).mulVec h = 0}) else 0
        else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : Nat.Coprime a.val c
    · simp only [if_pos ha]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    · simp [ha]
  rw [hextract] at h
  convert h using 1
  ring

end CubicTenVariables.SquarefullStarT
