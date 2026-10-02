import HessianTheorem11.UnconditionalAlgebraicExistence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Literal invertible and determinant-one matrix realizability descends
from any extension of an algebraically closed field, preserving arbitrary
polynomial matrix equations and finitely many inequations. -/
noncomputable section
namespace HessianTheorem11.UnconditionalAlgebraicExistence
open MvPolynomial Matrix
variable {K E : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixPoint (A : Matrix ι ι E) : (ι × ι) → E := fun ij => A ij.1 ij.2

def matrixDetPolynomial : MvPolynomial (ι × ι) K :=
  Matrix.det (fun i j : ι => (X (i,j) : MvPolynomial (ι × ι) K))

@[simp] theorem aeval_matrixDetPolynomial (A : Matrix ι ι E) :
    aeval (matrixPoint A) (matrixDetPolynomial (K := K)) = A.det := by
  change (aeval (matrixPoint A) : MvPolynomial (ι × ι) K →ₐ[K] E).toRingHom
    (Matrix.det (fun i j : ι => (X (i,j) : MvPolynomial (ι × ι) K))) = A.det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [matrixPoint]

@[simp] theorem eval_matrixDetPolynomial (A : Matrix ι ι K) :
    eval (matrixPoint A) (matrixDetPolynomial (K := K)) = A.det := by
  exact aeval_matrixDetPolynomial A

theorem exists_specialLinear_matrix
    (Q : Set (MvPolynomial (ι × ι) K)) (S : Finset (MvPolynomial (ι × ι) K))
    (A : Matrix ι ι E) (hA : A.det = 1)
    (hQ : ∀ p ∈ Q, aeval (matrixPoint A) p = 0)
    (hS : ∀ p ∈ S, aeval (matrixPoint A) p ≠ 0) :
    ∃ B : Matrix ι ι K, B.det = 1 ∧
      (∀ p ∈ Q, eval (matrixPoint B) p = 0) ∧
      (∀ p ∈ S, eval (matrixPoint B) p ≠ 0) := by
  classical
  let q : MvPolynomial (ι × ι) K := matrixDetPolynomial - 1
  have hq : aeval (matrixPoint A) q = 0 := by simp [q,hA]
  obtain ⟨y,hy,hSy⟩ := exists_equations_inequations (insert q Q) S (matrixPoint A)
    (fun p hp => by rcases hp with rfl | hp; exact hq; exact hQ p hp) hS
  let B : Matrix ι ι K := fun i j => y (i,j)
  have hBy : matrixPoint B = y := by ext ⟨i,j⟩; rfl
  refine ⟨B,?_,?_,?_⟩
  · have he := hy q (Set.mem_insert q Q)
    rw [← hBy] at he
    simpa [q,sub_eq_zero] using he
  · intro p hp
    rw [hBy]
    exact hy p (Set.mem_insert_of_mem q hp)
  · simpa only [hBy] using hSy

theorem exists_invertible_matrix
    (Q : Set (MvPolynomial (ι × ι) K)) (S : Finset (MvPolynomial (ι × ι) K))
    (A : Matrix ι ι E) (hA : A.det ≠ 0)
    (hQ : ∀ p ∈ Q, aeval (matrixPoint A) p = 0)
    (hS : ∀ p ∈ S, aeval (matrixPoint A) p ≠ 0) :
    ∃ B : Matrix ι ι K, IsUnit B ∧
      (∀ p ∈ Q, eval (matrixPoint B) p = 0) ∧
      (∀ p ∈ S, eval (matrixPoint B) p ≠ 0) := by
  classical
  let q : MvPolynomial (ι × ι) K := matrixDetPolynomial
  have hq : aeval (matrixPoint A) q ≠ 0 := by simpa only [q,aeval_matrixDetPolynomial] using hA
  obtain ⟨y,hy,hSy⟩ := exists_equations_inequations Q (insert q S) (matrixPoint A) hQ
    (fun p hp => by rcases Finset.mem_insert.mp hp with rfl | hp; exact hq; exact hS p hp)
  let B : Matrix ι ι K := fun i j => y (i,j)
  have hBy : matrixPoint B = y := by ext ⟨i,j⟩; rfl
  refine ⟨B,?_,?_,?_⟩
  · apply (Matrix.isUnit_iff_isUnit_det B).mpr
    apply isUnit_iff_ne_zero.mpr
    have he := hSy q (Finset.mem_insert_self q S)
    rw [← hBy] at he
    simpa only [q,eval_matrixDetPolynomial] using he
  · simpa only [hBy] using hy
  · intro p hp
    rw [hBy]
    exact hSy p (Finset.mem_insert_of_mem hp)

end HessianTheorem11.UnconditionalAlgebraicExistence
