import CubicTenVariables.TerminalHighSplit
import CubicTenVariables.QuadraticSumSupport
import CubicTenVariables.AdmissiblePrimePowerCount
import CubicTenVariables.PrimePowerFibers
import CubicTenVariables.HessianResidueKernel

/-!
# Higher terminal norm bounds from actual support and diagonalization

The finite split is restricted to the literal admissible low digits using
quadratic support containment. The Gauss bound controls each remaining
inner sum. Admissible counting and the scaled-kernel formula use the same
actual integral Hessian diagonalization. The maximizing unit is reduced
by the genuine prime-power ring homomorphism.
-/

noncomputable section
namespace CubicTenVariables.TerminalHighBound
open MvPolynomial HessianTheorem11 CubicTaylorExpansion TerminalCubicSum TerminalHighSplit
open scoped BigOperators Matrix

/-- The actual prime-power reduction preserves the multiplier as a unit. -/
def reducedUnit (p : ℕ) {a t : ℕ} (hat : a ≤ t) (u : (ZMod (p^t))ˣ) :
    (ZMod (p^a))ˣ := Units.map (PrimePowerFibers.reduction p hat).toMonoidHom u

/-- Its value is precisely the canonical integer representative used in
the existing split. No map between unrelated residue rings is used. -/
theorem reducedUnit_val (p : ℕ) [NeZero p] {a t : ℕ}
    (hat : a ≤ t) (u : (ZMod (p^t))ˣ) :
    (reducedUnit p hat u : ZMod (p^a)) = ((u : ZMod (p^t)).val : ZMod (p^a)) := by
  change PrimePowerFibers.reduction p hat (u : ZMod (p^t)) = _
  have he := congrArg (PrimePowerFibers.reduction p hat)
    (ZMod.natCast_zmod_val (u : ZMod (p^t)))
  simpa only [map_natCast] using he.symm

/-- A supported finite sum of norms is bounded by its actual support
cardinality times a common bound. -/
theorem sum_norm_le_card_mul {ι : Type*} [Fintype ι]
    (f : ι → ℂ) (P : ι → Prop) (R : ℝ)
    (hzero : ∀ v, ¬P v → f v = 0) (hbound : ∀ v, P v → ‖f v‖ ≤ R) :
    (∑ v, ‖f v‖) ≤ (Nat.card {v // P v} : ℝ) * R := by
  classical
  calc
    _ ≤ ∑ v, if P v then R else 0 := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : P v
      · simpa only [if_pos hv] using hbound v hv
      · simp only [if_neg hv, hzero v hv, norm_zero, le_refl]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The inner phase has the actual scaled-Hessian Gauss bound. This
individual estimate is valid also at even positive moduli. -/
theorem norm_quadraticInnerSum_le_sqrt (M : ℕ) [NeZero M] {n : ℕ}
    (F : MvPolynomial (Fin n) (ZMod M)) (hF : F.IsHomogeneous 3)
    (L : ZMod M) (u : (ZMod M)ˣ) (ell y v : Fin n → ZMod M) :
    ‖quadraticInnerSum M F L u ell y v‖ ≤ Real.sqrt
      ((M : ℝ)^n * Nat.card {x : Fin n → ZMod M // (L • hessian F y).mulVec x = 0}) := by
  have hQ : ∀ x h, L * quadraticAt F y (x+h) =
      L * quadraticAt F y x + L * quadraticAt F y h +
        dotProduct x ((L • hessian F y).mulVec h) := by
    intro x h
    rw [quadraticAt_add F hF, Matrix.smul_mulVec, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have hg := QuadraticGaussBound.norm_mixed_sum_sq_le M n
    (fun x => L * quadraticAt F y x) (L • hessian F y) hQ u
    (ell + (u : ZMod M) • (hessian F y).mulVec v)
  apply Real.le_sqrt_of_sq_le
  simpa only [quadraticInnerSum, quadraticInnerPhase, mul_assoc, add_comm] using hg

/-- The literal outer sum is supported on the actual admissible canonical
low digits. Its bound uses their subtype cardinality, not all low digits. -/
theorem sum_norm_quadraticInnerSum_le_admissible_card
    (M L : ℕ) [NeZero M] [NeZero L] {n : ℕ}
    (F : MvPolynomial (Fin n) (ZMod M)) (hF : F.IsHomogeneous 3)
    (ell y : Fin n → ZMod M) (u : (ZMod M)ˣ) (h2 : IsUnit (2 : ZMod M)) :
    (∑ v : Fin n → Fin L, ‖quadraticInnerSum M F (L : ZMod M) u ell y
      (fun i => ((v i).val : ZMod M))‖) ≤
      (Nat.card {v : Fin n → Fin L // ∃ x : Fin n → ZMod M,
        ((L : ZMod M) • hessian F y).mulVec x =
          ell + (u : ZMod M) • (hessian F y).mulVec (fun i => ((v i).val : ZMod M))} : ℝ) *
        Real.sqrt ((M : ℝ)^n * Nat.card {x : Fin n → ZMod M //
          ((L : ZMod M) • hessian F y).mulVec x = 0}) := by
  apply sum_norm_le_card_mul
  · intro v hv
    exact QuadraticSumSupport.cubic_quadratic_sum_eq_zero_of_not_mem_image M n F hF y
      (ell + (u : ZMod M) • (hessian F y).mulVec (fun i => ((v i).val : ZMod M)))
      (L : ZMod M) u h2 hv
  · intro v _
    exact norm_quadraticInnerSum_le_sqrt M F hF (L : ZMod M) u ell y _

/-- Pointwise higher-terminal profile bound. Both the admissible count
and scaled-kernel exponent use the same actual integral diagonalization. -/
theorem norm_terminalSum_primePower_le_profile {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (y : Fin n → ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (a t : ℕ) (hat : a ≤ t) (A : ℤ) (hA : ((p^a : ℕ) : ℤ) ∣ A)
    (u : (ZMod (p^t))ˣ) (ell : Fin n → ZMod (p^t)) :
    ‖terminalSum (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
      (A : ZMod (p^t)) ell u (fun i => (y i : ZMod (p^t)))‖ ≤
      (p : ℝ) ^ (∑ i, ((t-a) - min (t-a)
        (a - PrimePowerKernelProfile.truncatedValuation p a (d i)))) *
      Real.sqrt ((p : ℝ) ^ (n*a + ∑ i,
        min ((t-a) + PrimePowerKernelProfile.truncatedValuation p a (d i)) a)) := by
  classical
  let b := t-a
  let uA := reducedUnit p hat u
  let ellA : Fin n → ZMod (p^a) := fun i => ((ell i).val : ZMod (p^a))
  let H := hessian (map (Int.castRingHom (ZMod (p^a))) F) (fun i => (y i : ZMod (p^a)))
  let E := ∑ i, (b - min b (a - PrimePowerKernelProfile.truncatedValuation p a (d i)))
  let J := ∑ i, min (b + PrimePowerKernelProfile.truncatedValuation p a (d i)) a
  let K := Nat.card {v : Fin n → Fin (p^b) // ∃ x : Fin n → ZMod (p^a),
    (((p^b : ℕ) : ZMod (p^a)) • H).mulVec x =
      ellA + (uA : ZMod (p^a)) • H.mulVec (fun i => ((v i).val : ZMod (p^a)))}
  have hsplit := norm_terminalSum_primePower_highSplit_le F hF p a t hat A
    ((u : ZMod (p^t)).val : ℤ) hA (fun i => ((ell i).val : ℤ)) y
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hsplit
  rw [← reducedUnit_val p hat u] at hsplit
  have hsum := sum_norm_quadraticInnerSum_le_admissible_card (p^a) (p^b)
    (map (Int.castRingHom (ZMod (p^a))) F) (hF.map _) ellA
    (fun i => (y i : ZMod (p^a))) uA (QuadraticSumSupport.isUnit_two_primePower p a hp hp2)
  have hbound : ‖terminalSum (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
      (A : ZMod (p^t)) ell u (fun i => (y i : ZMod (p^t)))‖ ≤
      (K : ℝ) * Real.sqrt ((p^a : ℕ)^n *
        (Nat.card {x : Fin n → ZMod (p^a) //
          (((p^b : ℕ) : ZMod (p^a)) • H).mulVec x = 0} : ℝ)) := hsplit.trans hsum
  have hK : K = 0 ∨ K = p^E := by
    have hh := AdmissiblePrimePowerCount.admissible_fin_primePower_count_of_diagonalization
      (hessian F y) U V d hD p hp a b ellA uA
    dsimp only at hh
    simpa only [K, E, H, HessianResidueKernel.hessian_intCast,
      Finset.prod_pow_eq_pow_sum, Nat.cast_pow] using hh
  have hKle : (K : ℝ) ≤ (p : ℝ)^E := by
    rcases hK with hK | hK
    · rw [hK, Nat.cast_zero]
      positivity
    · rw [hK, Nat.cast_pow]
  have hkernel : Nat.card {x : Fin n → ZMod (p^a) //
      (((p^b : ℕ) : ZMod (p^a)) • H).mulVec x = 0} = p^J := by
    simpa only [H, J, Nat.cast_pow] using
      HessianResidueKernel.card_scaled_hessian_primePower_kernel F y U V d hD p hp a b
  have hroot : Real.sqrt ((p^a : ℕ)^n *
      (Nat.card {x : Fin n → ZMod (p^a) //
        (((p^b : ℕ) : ZMod (p^a)) • H).mulVec x = 0} : ℝ)) =
      Real.sqrt ((p : ℝ)^(n*a+J)) := by
    rw [hkernel, Nat.cast_pow, Nat.cast_pow, ← pow_mul, ← pow_add, Nat.mul_comm a n]
  change _ ≤ (p : ℝ)^E * Real.sqrt ((p : ℝ)^(n*a+J))
  rw [hroot] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hKle (Real.sqrt_nonneg _))

/-- The same bound for the actual attained maximum over all units and all
linear frequencies, with one integral Hessian and one fixed diagonal. -/
theorem terminalMax_primePower_le_profile {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (y : Fin n → ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (a t : ℕ) (hat : a ≤ t) (A : ℤ) (hA : ((p^a : ℕ) : ℤ) ∣ A) :
    terminalMax (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
      (A : ZMod (p^t)) (fun i => (y i : ZMod (p^t))) ≤
      (p : ℝ) ^ (∑ i, ((t-a) - min (t-a)
        (a - PrimePowerKernelProfile.truncatedValuation p a (d i)))) *
      Real.sqrt ((p : ℝ) ^ (n*a + ∑ i,
        min ((t-a) + PrimePowerKernelProfile.truncatedValuation p a (d i)) a)) := by
  obtain ⟨u, ell, he⟩ := terminalMax_attained (p^t)
    (map (Int.castRingHom (ZMod (p^t))) F) (A : ZMod (p^t)) (fun i => (y i : ZMod (p^t)))
  rw [he]
  exact norm_terminalSum_primePower_le_profile F hF y U V d hD p hp hp2 a t hat A hA u ell

end CubicTenVariables.TerminalHighBound
