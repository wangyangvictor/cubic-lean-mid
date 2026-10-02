import CubicTenVariables.CubicSmoothSectionReduction
import CubicTenVariables.ProjectiveLinearSectionJacobian

/-! The remaining smooth-section guarantee expressed entirely by the
given polynomial, its partial derivatives, and ranks of literal matrices.
Kernel coordinates and their geometric smoothness are proved consequences.
The existence of a bounded-degree certificate is still an explicit antecedent. -/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.CubicJacobianSectionReduction
open MvPolynomial Literature ProjectiveLinearSectionCoordinates
open ProjectiveLinearSectionVariance ProjectiveLinearSectionJacobian
open CubicSmoothSectionReduction

variable {K : Type} [Field K] [Fintype K]

/-- Rank five equations and rank six augmented Jacobian at every nonzero
geometric common zero. No scheme, sheaf, or cohomology object is supplied. -/
def GoodJacobianTuple (F : MvPolynomial (Fin 10) K) (γ : Fin 5 → Fin 10 → K) : Prop :=
  Matrix.rank γ = 5 ∧
    ∀ x : Fin 10 → AlgebraicClosure K, x ≠ 0 →
      eval x (map (algebraMap K (AlgebraicClosure K)) F) = 0 →
      Matrix.mulVec (Matrix.map γ (algebraMap K (AlgebraicClosure K))) x = 0 →
      Matrix.rank (augmentedSectionJacobian (map (algebraMap K (AlgebraicClosure K)) F)
        (Matrix.map γ (algebraMap K (AlgebraicClosure K))) x) = 6

theorem smooth_threefold_coordinates (F : MvPolynomial (Fin 10) K)
    (γ : Fin 5 → Fin 10 → K) (hgood : GoodJacobianTuple F γ) :
    ∃ e : (Fin 5 → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ),
      sectionPolynomial F γ e ≠ 0 ∧ ProjectivelySmooth (sectionPolynomial F γ e) := by
  have hdim : Module.finrank K (LinearMap.ker (Matrix.mulVecLin γ)) = 5 := by
    have h := (Matrix.mulVecLin γ).finrank_range_add_finrank_ker
    change Matrix.rank γ +
      Module.finrank K (LinearMap.ker (Matrix.mulVecLin γ)) =
      Module.finrank K (Fin 10 → K) at h
    rw [hgood.1] at h
    simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_self, mul_one] at h
    omega
  let e : (Fin 5 → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hdim])
  have hsmooth := projectivelySmooth_sectionPolynomial_of_augmented_rank F γ hgood.1 e hgood.2
  refine ⟨e, ?_, hsmooth⟩
  intro hzero
  have hz := hsmooth (Pi.single (0 : Fin 5) (1 : AlgebraicClosure K)) (by
    simp [geometricSingularCone, hzero])
  have h := congrFun hz (0 : Fin 5)
  simpa using h

/-- The complete counting reduction with a literal Jacobian certificate.
Only the certificate's existence and the numerical smooth-cubic Weil bound
remain external to this theorem. -/
theorem affine_bound_of_jacobian_certificate (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hcertificate : 1440 < Nat.card K →
      ∃ P : MvPolynomial (Fin 50) (AlgebraicClosure K),
        P ≠ 0 ∧ P.totalDegree ≤ 720 ∧
        ∀ γ : Fin 5 → Fin 10 → K,
          eval (algebraMap K (AlgebraicClosure K) ∘ normalTupleCoordinates γ) P ≠ 0 →
          GoodJacobianTuple F γ) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ 9| ≤
      330000 * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2) := by
  apply affine_bound_of_geometric_certificate weil F hFne hF
  intro hq
  obtain ⟨P, hP, hdegree, hgood⟩ := hcertificate hq
  refine ⟨P, hP, hdegree, ?_⟩
  intro γ hγ
  exact smooth_threefold_coordinates F γ (hgood γ hγ)

end CubicTenVariables.CubicJacobianSectionReduction
