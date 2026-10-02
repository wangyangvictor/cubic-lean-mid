import CubicTenVariables.ProjectiveLinearSectionCoordinates
import CubicTenVariables.ReducedVertexBaseChange
import CubicTenVariables.Literature.SmoothCubicWeil

/-! # The literal Jacobian criterion for a coordinate linear section

The first row of the augmented matrix is the gradient of the polynomial;
the remaining rows are the equations defining the linear section. Full
rank at every nonzero common zero over the algebraic closure implies the
existing literal geometric smoothness predicate for the restricted
polynomial. The proof uses the chain rule and finite-dimensional rank
arithmetic, including injectivity of the coordinate frame after scalar
extension. No smoothness or geometric realization is postulated.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.ProjectiveLinearSectionJacobian

open MvPolynomial HessianTheorem11.PolynomialRestriction
open ProjectiveLinearSectionCoordinates Literature

variable {K : Type*} [Field K] {m n k : ℕ}

/-- The actual Jacobian matrix of `F` and the displayed linear equations. -/
def augmentedSectionJacobian (F : MvPolynomial (Fin n) K)
    (γ : Matrix (Fin k) (Fin n) K) (x : Fin n → K) :
    Matrix (Fin (k + 1)) (Fin n) K :=
  Fin.cons (fun i => eval x (pderiv i F)) γ

/-- The chosen coordinate frame lies in the simultaneous equation kernel. -/
theorem equations_mul_sectionCoordinateMatrix (γ : Matrix (Fin k) (Fin n) K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    (γ : Matrix (Fin k) (Fin n) K) * sectionCoordinateMatrix γ e = 0 := by
  ext i j
  have h := (mem_equationKernel_iff γ _).mp
    (e (fun j' => if j' = j then 1 else 0)).property i
  simpa [Matrix.mul_apply, sectionCoordinateMatrix, LinearMap.toMatrix'_apply,
    dotProduct] using h

theorem section_dimension_add_rank (γ : Matrix (Fin k) (Fin n) K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    m + (γ : Matrix (Fin k) (Fin n) K).rank = n := by
  have he : Module.finrank K (LinearMap.ker (Matrix.mulVecLin γ)) = m := by
    simpa using e.finrank_eq.symm
  have h := (Matrix.mulVecLin γ).finrank_range_add_finrank_ker
  change (γ : Matrix (Fin k) (Fin n) K).rank +
    Module.finrank K (LinearMap.ker (Matrix.mulVecLin γ)) =
    Module.finrank K (Fin n → K) at h
  simpa [he, Nat.add_comm] using h

/-- An injective rectangular coordinate frame has full column rank. -/
theorem frame_rank (B : Matrix (Fin n) (Fin m) K)
    (hB : Function.Injective B.mulVec) : B.rank = m := by
  have hker : LinearMap.ker B.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr hB
  have h := B.mulVecLin.finrank_range_add_finrank_ker
  rw [hker] at h
  simpa [Matrix.rank] using h

/-- Vanishing of all restricted derivatives makes the augmented Jacobian
annihilate the coordinate frame. -/
theorem augmentedSectionJacobian_mul_eq_zero
    (F : MvPolynomial (Fin n) K) (γ : Matrix (Fin k) (Fin n) K)
    (B : Matrix (Fin n) (Fin m) K)
    (hγB : (γ : Matrix (Fin k) (Fin n) K) * B = 0)
    (y : Fin m → K)
    (hy : ∀ j, eval y (pderiv j (restrict B F)) = 0) :
    augmentedSectionJacobian F γ (B.mulVec y) * B = 0 := by
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · have h := congrArg (eval y) (pderiv_restrict B F j)
    simp only [map_sum, map_mul, eval_restrict, eval_C] at h
    simpa [augmentedSectionJacobian, Matrix.mul_apply] using h.symm.trans (hy j)
  · simpa [augmentedSectionJacobian, Matrix.mul_apply] using congrFun (congrFun hγB a) j

/-- The frame remains injective and satisfies all row equations after
any field extension. -/
theorem sectionCoordinateMatrix_baseChange
    {L : Type*} [Field L] [Algebra K L]
    (γ : Matrix (Fin k) (Fin n) K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    Function.Injective ((sectionCoordinateMatrix γ e).map (algebraMap K L)).mulVec ∧
      (Matrix.map (γ : Matrix (Fin k) (Fin n) K) (algebraMap K L)) *
        (sectionCoordinateMatrix γ e).map (algebraMap K L) = 0 := by
  refine ⟨ReducedVertexBaseChange.map_frame_injective _
    (sectionCoordinateMatrix_injective γ e), ?_⟩
  have h := congrArg (fun A : Matrix (Fin k) (Fin m) K => A.map (algebraMap K L))
    (equations_mul_sectionCoordinateMatrix γ e)
  simp only [Matrix.map_mul] at h
  exact h.trans (by ext i j; exact map_zero (algebraMap K L))

/-- Full augmented Jacobian rank at every nonzero geometric common zero
implies the literal smoothness predicate for the actual coordinate
restriction. All zeros and derivatives are over `AlgebraicClosure K`. -/
theorem projectivelySmooth_sectionPolynomial_of_augmented_rank
    (F : MvPolynomial (Fin n) K) (γ : Matrix (Fin k) (Fin n) K)
    (hrank : (γ : Matrix (Fin k) (Fin n) K).rank = k)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ))
    (hJac : ∀ x : Fin n → AlgebraicClosure K, x ≠ 0 →
      eval x (map (algebraMap K (AlgebraicClosure K)) F) = 0 →
      Matrix.mulVec ((γ : Matrix (Fin k) (Fin n) K).map
        (algebraMap K (AlgebraicClosure K))) x = 0 →
      (augmentedSectionJacobian (map (algebraMap K (AlgebraicClosure K)) F)
        ((γ : Matrix (Fin k) (Fin n) K).map (algebraMap K (AlgebraicClosure K))) x).rank =
        k + 1) :
    ProjectivelySmooth (sectionPolynomial F γ e) := by
  intro y hy
  let α := algebraMap K (AlgebraicClosure K)
  let B := (sectionCoordinateMatrix γ e).map α
  let γL := (γ : Matrix (Fin k) (Fin n) K).map α
  have hmap : map α (sectionPolynomial F γ e) = restrict B (map α F) :=
    map_restrict α (sectionCoordinateMatrix γ e) F
  change eval y (map α (sectionPolynomial F γ e)) = 0 ∧
    (∀ j, eval y (pderiv j (map α (sectionPolynomial F γ e))) = 0) at hy
  rw [hmap] at hy
  obtain ⟨hB, hγB⟩ := sectionCoordinateMatrix_baseChange
    (L := AlgebraicClosure K) γ e
  change Function.Injective B.mulVec at hB
  change γL * B = 0 at hγB
  by_contra hyne
  have hxne : B.mulVec y ≠ 0 := by
    intro hx
    apply hyne
    exact hB (by simpa using hx)
  have hxF : eval (B.mulVec y) (map α F) = 0 := by
    simpa only [eval_restrict] using hy.1
  have hxγ : γL.mulVec (B.mulVec y) = 0 := by
    rw [Matrix.mulVec_mulVec, hγB, Matrix.zero_mulVec]
  have hfull := hJac (B.mulVec y) hxne hxF hxγ
  have hzero := augmentedSectionJacobian_mul_eq_zero (map α F) γL B hγB y hy.2
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  have hBrank := frame_rank B hB
  have hdim := section_dimension_add_rank γ e
  rw [hrank] at hdim
  change (augmentedSectionJacobian (map α F) γL (B.mulVec y)).rank = k + 1 at hfull
  rw [hfull, hBrank, Fintype.card_fin] at hsum
  omega

end CubicTenVariables.ProjectiveLinearSectionJacobian
