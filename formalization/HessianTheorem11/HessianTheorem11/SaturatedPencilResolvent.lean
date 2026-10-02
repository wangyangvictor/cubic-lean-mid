import HessianTheorem11.SaturatedResolvent
import HessianTheorem11.ResolventCoefficients
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! Full scalar-rank-to-formal-resolvent implication for §34.1. -/
noncomputable section
namespace HessianTheorem11.SaturatedResolvent
open Matrix PencilSchurVanishing
variable {K α β γ : Type*} [Field K] [Infinite K]
  [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β]

/-- A rank bound on the entire scalar pencil, together with the full-column
normal Jacobian, forces the two exact formal identities. -/
theorem resolvent_of_pencil_rank
    (B₀ : Matrix α α K) (hB₀ : B₀.det ≠ 0)
    (G₁ : Matrix (α ⊕ (β ⊕ β)) (α ⊕ (β ⊕ β)) K)
    (P : Matrix γ β K) (L : Matrix β γ K) (hLP : L * P = 1)
    (hrank : ∀ t : K,
      (Matrix.fromBlocks (0 : Matrix γ γ K) (t • cross (α := α) P)
        (t • (cross P).transpose) (initial B₀ + t • G₁)).rank ≤
          Fintype.card (α ⊕ (β ⊕ β))) :
    G₁.submatrix (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inl i)) = 0 ∧
    (G₁.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl).map PowerSeries.C *
      (seriesPencil B₀ (G₁.submatrix Sum.inl Sum.inl))⁻¹ *
      (G₁.submatrix Sum.inl (fun i => Sum.inr (Sum.inl i))).map PowerSeries.C = 0 := by
  let G := seriesPencil (initial B₀) G₁
  have hGJ : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G
    (seriesPencil_isUnit_det _ _ (initial_isUnit_det B₀ hB₀))
  have hs := pencil_schur_eq_zero (0 : Matrix γ γ K) 0 0 (cross P)
    0 (cross P).transpose (initial B₀) G₁ (fun t => by simpa using hrank t) G⁻¹ hGJ
  exact resolvent_of_inverse_final_zero B₀ hB₀ G₁ G⁻¹ hGJ
    (cross_schur_cancel P L hLP G⁻¹ hs)

/-- Symmetry identifies the two rectangular blocks and gives the source's
precise expression E (B₀+tQ)⁻¹ Eᵀ. -/
theorem symmetric_resolvent_of_pencil_rank
    (B₀ : Matrix α α K) (hB₀ : B₀.det ≠ 0)
    (G₁ : Matrix (α ⊕ (β ⊕ β)) (α ⊕ (β ⊕ β)) K) (hG₁ : G₁.IsSymm)
    (P : Matrix γ β K) (L : Matrix β γ K) (hLP : L * P = 1)
    (hrank : ∀ t : K,
      (Matrix.fromBlocks (0 : Matrix γ γ K) (t • cross (α := α) P)
        (t • (cross P).transpose) (initial B₀ + t • G₁)).rank ≤
          Fintype.card (α ⊕ (β ⊕ β))) :
    G₁.submatrix (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inl i)) = 0 ∧
    (G₁.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl).map PowerSeries.C *
      (seriesPencil B₀ (G₁.submatrix Sum.inl Sum.inl))⁻¹ *
      ((G₁.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl).map PowerSeries.C).transpose = 0 := by
  have h := resolvent_of_pencil_rank B₀ hB₀ G₁ P L hLP hrank
  have he : G₁.submatrix Sum.inl (fun i => Sum.inr (Sum.inl i)) =
      (G₁.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl).transpose := by
    ext i j
    exact (hG₁.apply _ _).symm
  simpa only [he, Matrix.transpose_map] using h

/-- The formal identity yields polynomial identities of every degree in the
first variation, ready for extension from a dense open set. -/
theorem resolvent_coefficients_of_pencil_rank
    (B₀ : Matrix α α K) (hB₀ : B₀.det ≠ 0)
    (G₁ : Matrix (α ⊕ (β ⊕ β)) (α ⊕ (β ⊕ β)) K)
    (P : Matrix γ β K) (L : Matrix β γ K) (hLP : L * P = 1)
    (hrank : ∀ t : K,
      (Matrix.fromBlocks (0 : Matrix γ γ K) (t • cross (α := α) P)
        (t • (cross P).transpose) (initial B₀ + t • G₁)).rank ≤
          Fintype.card (α ⊕ (β ⊕ β))) (j : ℕ) :
    G₁.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl *
      (-(B₀⁻¹ * G₁.submatrix Sum.inl Sum.inl))^j * B₀⁻¹ *
      G₁.submatrix Sum.inl (fun i => Sum.inr (Sum.inl i)) = 0 := by
  have h := resolvent_of_pencil_rank B₀ hB₀ G₁ P L hLP hrank
  exact ResolventCoefficients.vanishing_resolvent_coefficients B₀
    (G₁.submatrix Sum.inl Sum.inl) B₀⁻¹
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB₀)) _ _ _
    (Matrix.mul_nonsing_inv _ (seriesPencil_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hB₀)))
    h.2 j

end HessianTheorem11.SaturatedResolvent
