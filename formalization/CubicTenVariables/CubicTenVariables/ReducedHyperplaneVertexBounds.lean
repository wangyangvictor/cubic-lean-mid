import CubicTenVariables.ReducedHessianRankDimensions
import CubicTenVariables.ReducedCubicVertex
import CubicTenVariables.LinearProjectiveDimension

/-! Uniform positive-characteristic bounds on the actual maximal vertices
of all ten-variable hyperplane sections. No literature premise is used. -/

noncomputable section
namespace CubicTenVariables.ReducedHyperplaneVertexBounds
open MvPolynomial HessianTheorem11 Module Matrix PolynomialRestriction
open ReducedCubicVertex ReducedGaussSection
variable {K : Type*} [Field K] [Infinite K]

/-- A geometric rank-locus dimension bound controls every section vertex,
with the frame allowed to vary arbitrarily over the given field. -/
theorem section_vertex_finrank_le {m r : ℕ}
    (F : MvPolynomial (Fin (m+1)) K) (hF : F.IsHomogeneous 3)
    (B : Matrix (Fin (m+1)) (Fin m) K) (hB : Function.Injective B.mulVec)
    (hdim : coordinateDimension {x | (hessian F x).rank ≤ 2} ≤ (r : Dimension)) :
    finrank K (affineVertex (restrict B F) (homogeneous_restrict B F hF)) ≤ r := by
  apply LinearSubspaceDimension.finrank_le_of_injective_image_subset
    _ B.mulVecLin hB _ r _ hdim
  rintro _ ⟨x,hx,rfl⟩
  exact ambient_rank_le_two_of_section_vertex F hF B hB x hx

theorem section_vertex_projectiveDimension_le {m s : ℕ}
    (F : MvPolynomial (Fin (m+1)) K) (hF : F.IsHomogeneous 3)
    (B : Matrix (Fin (m+1)) (Fin m) K) (hB : Function.Injective B.mulVec)
    (hdim : coordinateDimension {x | (hessian F x).rank ≤ 2} ≤
      ((s+1 : ℕ) : Dimension)) :
    ReducedGaussSection.projectiveDimension
      (affineVertex (restrict B F) (homogeneous_restrict B F hF) : Set (Fin m → K)) ≤
        (s : Dimension) :=
  LinearProjectiveDimension.projectiveDimension_le _ s
    (section_vertex_finrank_le F hF B hB hdim)

/-- The exceptional integer also removes 2 and 3. The vertex is identified
with literal translation invariance, and its projective bound uses actual
normalized-chart coordinate-ring dimensions. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬p∣D →
      3<p ∧ ∀ (K : Type) [Field K] [Infinite K] [CharP K p],
        coordinateDimension {x : Fin 10 → K |
          (hessian (map (Int.castRingHom K) F) x).rank ≤ 2} ≤ (4 : Dimension) ∧
        coordinateDimension {x : Fin 10 → K | eval₂ (Int.castRingHom K) x F=0 ∧
          gradient (map (Int.castRingHom K) F) x=0} ≤ (5 : Dimension) ∧
        ∀ (B : Matrix (Fin 10) (Fin 9) K), Function.Injective B.mulVec →
          let f := restrict B (map (Int.castRingHom K) F)
          let hf := homogeneous_restrict B _ (hF.map (Int.castRingHom K))
          finrank K (affineVertex f hf) ≤ 4 ∧
          ReducedGaussSection.projectiveDimension
            (affineVertex f hf : Set (Fin 9 → K)) ≤ (3 : Dimension) ∧
          ∀ x : Fin 9 → K, x∈affineVertex f hf ↔ TranslationDirection f x := by
  obtain ⟨D,hD,hgood⟩ := ReducedHessianRankDimensions.exists_rank_two_and_singular_bound F hF hA
  refine ⟨6*D,Nat.mul_pos (by decide) hD,?_⟩
  intro p hp hpD
  have hp6 : ¬p∣6 := fun h => hpD (dvd_mul_of_dvd_left h D)
  have hp3 : 3<p := by
    by_contra! h
    have : p=2 ∨ p=3 := by have := hp.two_le; omega
    rcases this with rfl | rfl <;> norm_num at hp6
  refine ⟨hp3,?_⟩
  intro K _ _ _
  obtain ⟨hr,hs⟩ := hgood p hp (fun h => hpD (dvd_mul_of_dvd_right h 6)) K
  refine ⟨hr,hs,?_⟩
  intro B hB
  dsimp only
  refine ⟨section_vertex_finrank_le _ (hF.map _) B hB hr,?_,?_⟩
  · apply section_vertex_projectiveDimension_le _ (hF.map _) B hB
    exact hr
  · intro x
    exact mem_affineVertex_iff_translation_charP _ _ p hp3 x

end CubicTenVariables.ReducedHyperplaneVertexBounds
