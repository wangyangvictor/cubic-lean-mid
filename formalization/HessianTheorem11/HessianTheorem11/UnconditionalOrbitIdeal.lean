import HessianTheorem11.ReducedRelativeGeometry
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Actual finite-dimensional spaces of bounded-degree equations of a
linearly invariant affine set. Their evaluation functionals and pullback
actions are polynomial algebra, with no orbit or instability input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction Module
variable {K : Type*} [Field K] {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem totalDegree_restrict_le (B : Matrix σ τ K) (P : MvPolynomial σ K) :
    (restrict B P).totalDegree ≤ P.totalDegree := by
  classical
  have he : restrict B P = ∑ e ∈ P.support, restrict B (monomial e (coeff e P)) := by
    simpa only [restrict,map_sum] using congrArg (restrict B) P.as_sum
  rw [he]
  apply totalDegree_finsetSum_le
  intro e he
  have hh := (homogeneous_restrict B (monomial e (coeff e P))
    (isHomogeneous_monomial (coeff e P) rfl)).totalDegree_le
  exact hh.trans (by simpa only [Finsupp.degree] using le_totalDegree he)

def boundedIdeal (S : Set (σ → K)) (N : ℕ) : Submodule K (MvPolynomial σ K) :=
  (vanishingIdeal K S).restrictScalars K ⊓ restrictTotalDegree σ K N

theorem mem_boundedIdeal (S : Set (σ → K)) (N : ℕ) (P : MvPolynomial σ K) :
    P ∈ boundedIdeal S N ↔ (∀ x ∈ S, eval x P = 0) ∧ P.totalDegree ≤ N := by
  simp only [boundedIdeal,Submodule.mem_inf,Submodule.restrictScalars_mem,
    mem_restrictTotalDegree]
  rfl

instance boundedIdeal_finite (S : Set (σ → K)) (N : ℕ) :
    FiniteDimensional K (boundedIdeal S N) := by
  apply FiniteDimensional.of_injective
    (Submodule.inclusion (show boundedIdeal S N ≤ restrictTotalDegree σ K N from inf_le_right))
  exact Submodule.inclusion_injective _

theorem restrict_mem_boundedIdeal (B : Matrix σ σ K) (S : Set (σ → K)) (N : ℕ)
    (hS : ∀ x ∈ S, B.mulVec x ∈ S) {P : MvPolynomial σ K}
    (hP : P ∈ boundedIdeal S N) : restrict B P ∈ boundedIdeal S N := by
  rw [mem_boundedIdeal] at hP ⊢
  refine ⟨?_,(totalDegree_restrict_le B P).trans hP.2⟩
  intro x hx
  rw [eval_restrict]
  exact hP.1 _ (hS x hx)

def boundedPullback (B : Matrix σ σ K) (S : Set (σ → K)) (N : ℕ)
    (hS : ∀ x ∈ S, B.mulVec x ∈ S) : boundedIdeal S N →ₗ[K] boundedIdeal S N where
  toFun P := ⟨restrict B P, restrict_mem_boundedIdeal B S N hS P.property⟩
  map_add' P Q := Subtype.ext ((aeval (linearForms B)).map_add P.val Q.val)
  map_smul' c P := Subtype.ext ((aeval (linearForms B)).toLinearMap.map_smul c P.val)

def boundedEvaluation (S : Set (σ → K)) (N : ℕ) (x : σ → K) :
    Dual K (boundedIdeal S N) := (aeval x).toLinearMap.comp (boundedIdeal S N).subtype

@[simp] theorem boundedEvaluation_apply (S : Set (σ → K)) (N : ℕ)
    (x : σ → K) (P : boundedIdeal S N) : boundedEvaluation S N x P = eval x P.val := rfl

theorem boundedEvaluation_pullback (B : Matrix σ σ K) (S : Set (σ → K)) (N : ℕ)
    (hS : ∀ x ∈ S, B.mulVec x ∈ S) (x : σ → K) (P : boundedIdeal S N) :
    boundedEvaluation S N x (boundedPullback B S N hS P) =
      boundedEvaluation S N (B.mulVec x) P := eval_restrict B P.val x

theorem exists_nonzero_boundedEvaluation (S : Set (σ → K)) (x : σ → K)
    (hx : ∃ P : MvPolynomial σ K, (∀ y ∈ S, eval y P = 0) ∧ eval x P ≠ 0) :
    ∃ N : ℕ, boundedEvaluation S N x ≠ 0 := by
  obtain ⟨P,hP,hPx⟩ := hx
  refine ⟨P.totalDegree,?_⟩
  let p : boundedIdeal S P.totalDegree :=
    ⟨P,(mem_boundedIdeal S P.totalDegree P).mpr ⟨hP,le_rfl⟩⟩
  intro hz
  have he := congrArg (fun f : Dual K (boundedIdeal S P.totalDegree) => f p) hz
  exact hPx he

end HessianTheorem11.UnconditionalOrbitIdeal
