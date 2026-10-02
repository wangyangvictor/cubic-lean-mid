import HessianTheorem11.KernelGradientSpan
import HessianTheorem11.LinearEmbeddingGeometry
import HessianTheorem11.LocalCubicNormalForm

/-! The actual gradient of a cubic on a two-dimensional linear slice
lies in the span of three explicit vectors. This is the algebraic part of
the small-image normal-quadrics argument. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem gradient_two_vector_expansion
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (u v : Fin n → K) (a b : K) :
    gradient F (a • u + b • v) =
      a^2 • gradient F u + (a*b) • (hessian F u).mulVec v + b^2 • gradient F v := by
  ext i
  have h := congrFun (hessian_mulVec_self hF (a • u + b • v)) i
  have hu := congrFun (hessian_mulVec_self hF u) i
  have hv := congrFun (hessian_mulVec_self hF v) i
  have hs := congrFun (hessian_polarization hF u v) i
  simp only [hessian_add hF, hessian_smul hF, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, nsmul_eq_mul] at h hu hv hs ⊢
  linear_combination (a^2/2 : K) * hu + (b^2/2 : K) * hv - (1/2 : K) * h -
    (a*b/2 : K) * hs

def gradientPlaneEnvelope (F : MvPolynomial (Fin n) K) (u v : Fin n → K) :
    Submodule K (Fin n → K) :=
  Submodule.span K (Set.range ![gradient F u, (hessian F u).mulVec v, gradient F v])

theorem gradientPlaneEnvelope_finrank_le_three
    (F : MvPolynomial (Fin n) K) (u v : Fin n → K) :
    finrank K (gradientPlaneEnvelope F u v) ≤ 3 := by
  exact (finrank_range_le_card ![gradient F u, (hessian F u).mulVec v, gradient F v]).trans
    (by simp)

theorem gradient_two_vector_mem_envelope
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (u v : Fin n → K) (a b : K) :
    gradient F (a • u + b • v) ∈ gradientPlaneEnvelope F u v := by
  rw [gradient_two_vector_expansion F hF]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨(0 : Fin 3), rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨(1 : Fin 3), rfl⟩
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(2 : Fin 3), rfl⟩

/-- The same slice expansion for an arbitrary homogeneous quadratic,
using its actual constant Hessian coefficients. -/
theorem quadratic_eval_two_vector_expansion
    (Q : MvPolynomial (Fin n) K) (hQ : Q.IsHomogeneous 2)
    (u v : Fin n → K) (a b : K) :
    eval (a • u + b • v) Q = a^2 * eval u Q +
      (a*b) * (eval (u+v) Q - eval u Q - eval v Q) + b^2 * eval v Q := by
  have h := LocalCubicNormalForm.quadratic_eval_identity Q hQ (a • u + b • v)
  have hs := LocalCubicNormalForm.quadratic_eval_identity Q hQ (u+v)
  have hu := LocalCubicNormalForm.quadratic_eval_identity Q hQ u
  have hv := LocalCubicNormalForm.quadratic_eval_identity Q hQ v
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_smul, smul_dotProduct, smul_eq_mul] at h hs
  linear_combination ((a^2-a*b)/2 : K) * hu + ((b^2-a*b)/2 : K) * hv +
    (a*b/2 : K) * hs - (1/2 : K) * h

def quadraticTuplePlaneEnvelope {m : ℕ} (Q : Fin m → MvPolynomial (Fin n) K)
    (u v : Fin n → K) : Submodule K (Fin m → K) :=
  Submodule.span K (Set.range ![fun j => eval u (Q j),
    fun j => eval (u+v) (Q j) - eval u (Q j) - eval v (Q j), fun j => eval v (Q j)])

theorem quadraticTuplePlaneEnvelope_finrank_le_three {m : ℕ}
    (Q : Fin m → MvPolynomial (Fin n) K) (u v : Fin n → K) :
    finrank K (quadraticTuplePlaneEnvelope Q u v) ≤ 3 := by
  exact (finrank_range_le_card ![fun j => eval u (Q j),
    fun j => eval (u+v) (Q j) - eval u (Q j) - eval v (Q j), fun j => eval v (Q j)]).trans
    (by simp)

theorem quadraticTuple_two_vector_mem_envelope {m : ℕ}
    (Q : Fin m → MvPolynomial (Fin n) K) (hQ : ∀ j, (Q j).IsHomogeneous 2)
    (u v : Fin n → K) (a b : K) :
    (fun j => eval (a • u + b • v) (Q j)) ∈ quadraticTuplePlaneEnvelope Q u v := by
  have he : (fun j => eval (a • u + b • v) (Q j)) =
      a^2 • (fun j => eval u (Q j)) +
      (a*b) • (fun j => eval (u+v) (Q j) - eval u (Q j) - eval v (Q j)) +
      b^2 • (fun j => eval v (Q j)) := by
    ext j
    exact quadratic_eval_two_vector_expansion (Q j) (hQ j) u v a b
  rw [he]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨(0 : Fin 3), rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨(1 : Fin 3), rfl⟩
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(2 : Fin 3), rfl⟩

end HessianTheorem11
