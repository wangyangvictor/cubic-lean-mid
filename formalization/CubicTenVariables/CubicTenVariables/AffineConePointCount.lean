import CubicTenVariables.HyperplaneFrames
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact affine counts under a linear cone decomposition. These are finite
bijections, not point-count estimates or literature assumptions. -/
noncomputable section
namespace CubicTenVariables.AffineConePointCount
open MvPolynomial HessianTheorem11 PolynomialRestriction

variable {K : Type*} [Field K] {n r m : ℕ}

/-- A coordinate decomposition in which the equation depends only on the
second factor gives an actual bijection of its zero set with vertex times base. -/
def zeroEquiv (F : MvPolynomial (Fin n) K) (Q : MvPolynomial (Fin m) K)
    (E : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin m → K)))
    (h : ∀ x, eval x F = eval (E x).2 Q) :
    {x : Fin n → K // eval x F=0} ≃
      ((Fin r → K) × {y : Fin m → K // eval y Q=0}) where
  toFun x := ((E x).1, ⟨(E x).2, (h x).symm.trans x.property⟩)
  invFun y := ⟨E.symm (y.1,y.2), by simpa only [h, E.apply_symm_apply] using y.2.property⟩
  left_inv x := by apply Subtype.ext; exact E.symm_apply_apply x
  right_inv y := by cases y; simp

/-- Exact affine cone formula, including zero vertex rank and zero-dimensional
coordinate spaces. -/
theorem zero_card [Finite K]
    (F : MvPolynomial (Fin n) K) (Q : MvPolynomial (Fin m) K)
    (E : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin m → K)))
    (h : ∀ x, eval x F = eval (E x).2 Q) :
    Nat.card {x : Fin n → K // eval x F=0} =
      Nat.card K ^ r * Nat.card {y : Fin m → K // eval y Q=0} := by
  rw [Nat.card_congr (zeroEquiv F Q E h), Nat.card_prod]
  simp [Nat.card_fun]

/-- The literal zeros in a hyperplane are exactly the zeros of its actual
restricted polynomial in any injective frame of the full hyperplane. -/
def hyperplaneZeroEquiv (F : MvPolynomial (Fin (m+1)) K)
    (v : Fin (m+1) → K) (B : Matrix (Fin (m+1)) (Fin m) K)
    (hB : Function.Injective B.mulVec)
    (hRange : LinearMap.range B.mulVecLin = TerminalSectionIncidence.hyperplane v) :
    {y : Fin m → K // eval y (restrict B F)=0} ≃
      {x : Fin (m+1) → K // eval x F=0 ∧ dotProduct v x=0} := by
  classical
  refine Equiv.ofBijective (fun y => ⟨B.mulVec y, ?_⟩) ?_
  · refine ⟨by simpa only [eval_restrict] using y.property, ?_⟩
    have hy : B.mulVec y ∈ LinearMap.range B.mulVecLin := ⟨y,rfl⟩
    rw [hRange] at hy
    exact hy
  · constructor
    · intro x y hxy
      exact Subtype.ext (hB (congrArg Subtype.val hxy))
    · rintro ⟨x,hx,hv⟩
      have hmem : x ∈ LinearMap.range B.mulVecLin := by
        rw [hRange]
        exact hv
      obtain ⟨y,hy⟩ := hmem
      refine ⟨⟨y,?_⟩,?_⟩
      · rw [eval_restrict,show B.mulVec y=x from hy]
        exact hx
      · apply Subtype.ext
        exact hy

theorem hyperplane_zero_card (F : MvPolynomial (Fin (m+1)) K)
    (v : Fin (m+1) → K) (B : Matrix (Fin (m+1)) (Fin m) K)
    (hB : Function.Injective B.mulVec)
    (hRange : LinearMap.range B.mulVecLin = TerminalSectionIncidence.hyperplane v) :
    Nat.card {y : Fin m → K // eval y (restrict B F)=0} =
      Nat.card {x : Fin (m+1) → K // eval x F=0 ∧ dotProduct v x=0} :=
  Nat.card_congr (hyperplaneZeroEquiv F v B hB hRange)

end CubicTenVariables.AffineConePointCount
