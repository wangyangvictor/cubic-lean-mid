import CubicTenVariables.UniformHyperplaneGeometry
import CubicTenVariables.ReducedVertexBaseChange
import CubicTenVariables.Literature.FiniteFieldPointCounts

/-! The geometric reduction endpoints in the finite-field interfaces used by
the point-count literature. Every frame is defined over the original field;
its scalar extension is proved injective, and vertex dimension descends. -/
noncomputable section
namespace CubicTenVariables.ReducedFiniteFieldGeometry
open MvPolynomial HessianTheorem11 Module PolynomialRestriction Literature

/-- Reducing an integral equation then extending its field is exactly the
original coefficient map into the extension. -/
theorem map_reduction {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    {K L : Type*} [Field K] [Field L] [Algebra K L] :
    map (algebraMap K L) (map (Int.castRingHom K) F) = map (Int.castRingHom L) F := by
  have hc : (algebraMap K L).comp (Int.castRingHom K) = Int.castRingHom L :=
    RingHom.ext_int _ _
  rw [map_map,hc]

theorem vertex_finrank_congr {K : Type*} [Field K] {n : ℕ}
    (f g : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (he : f=g) : finrank K (ReducedCubicVertex.affineVertex f hf) =
      finrank K (ReducedCubicVertex.affineVertex g hg) := by
  subst g
  rfl

/-- One integer controls the ambient cubic and every hyperplane section,
including the vertex dimension over the original finite field. -/
theorem exists_uniform_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1≤D ∧ ∀ p : ℕ, p.Prime → ¬p∣D →
      3<p ∧ ∀ (K : Type) [Field K] [CharP K p],
        GeometricallyIntegralForm (map (Int.castRingHom K) F) ∧
        ReducedGaussSection.coordinateDimension
          (geometricSingularCone (map (Int.castRingHom K) F)) ≤ (5 : WithBot ℕ∞) ∧
        ∀ (B : Matrix (Fin 10) (Fin 9) K), Function.Injective B.mulVec →
          GeometricallyIntegralForm (restrict B (map (Int.castRingHom K) F)) ∧
          finrank K (ReducedCubicVertex.affineVertex
            (restrict B (map (Int.castRingHom K) F))
            (homogeneous_restrict B _ (hF.map _))) ≤4 := by
  obtain ⟨DG,hDG,hG⟩ := UniformHyperplaneGeometry.exists_uniform_bound spread F hF hA
  obtain ⟨DV,hDV,hV⟩ := ReducedHyperplaneVertexBounds.exists_uniform_bound F hF hA
  refine ⟨DG*DV,Nat.mul_pos hDG hDV,?_⟩
  intro p hp hpD
  have hpG : ¬p∣DG := fun h => hpD (dvd_mul_of_dvd_left h DV)
  have hpV : ¬p∣DV := fun h => hpD (dvd_mul_of_dvd_right h DG)
  obtain ⟨hp3,hgeo⟩ := hG p hp hpG
  refine ⟨hp3,?_⟩
  intro K _ _
  let L := AlgebraicClosure K
  let f := map (Int.castRingHom K) F
  have hf : f.IsHomogeneous 3 := hF.map _
  obtain ⟨hdom,hsections⟩ := hgeo L
  have hsec (B : Matrix (Fin 10) (Fin 9) K) (hB : Function.Injective B.mulVec) :
      GeometricallyIntegralForm (restrict B f) ∧
      finrank K (ReducedCubicVertex.affineVertex (restrict B f)
        (homogeneous_restrict B f hf)) ≤4 := by
    have hBi := ReducedVertexBaseChange.map_frame_injective (L := L) B hB
    have hs := hsections (B.map (algebraMap K L)) hBi
    have he : map (algebraMap K L) (restrict B f) =
        restrict (B.map (algebraMap K L)) (map (Int.castRingHom L) F) := by
      rw [map_restrict,map_reduction]
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro hz
      have hz' := congrArg (map (algebraMap K L)) hz
      rw [he,map_zero] at hz'
      exact hs.1 hz'
    · change IsDomain (MvPolynomial (Fin 9) L ⧸
        Ideal.span {map (algebraMap K L) (restrict B f)})
      rw [he]
      exact hs.2.2.2.1
    · have hdim := ReducedVertexBaseChange.affineVertex_finrank_le_baseChange
        (L := L) (restrict B f) (homogeneous_restrict B f hf)
      have hgeom : finrank L (ReducedCubicVertex.affineVertex
          (map (algebraMap K L) (restrict B f))
          ((homogeneous_restrict B f hf).map _)) ≤4 := by
        rw [vertex_finrank_congr _ _ _ (homogeneous_restrict _ _ (hF.map _)) he]
        exact hs.2.2.2.2.1
      exact hdim.trans hgeom
  have hfne : f≠0 := by
    obtain ⟨B,hB,_⟩ := HyperplaneFrames.exists_frame
      (Pi.single (0 : Fin 10) (1 : K)) (by
        intro hz
        have he := congrFun hz 0
        simp at he)
    intro hz
    exact (hsec B hB).1.1 (by rw [hz]; simp [restrict])
  refine ⟨⟨hfne,?_⟩,?_,hsec⟩
  · change IsDomain (MvPolynomial (Fin 10) L ⧸
      Ideal.span {map (algebraMap K L) f})
    dsimp only [f]
    rw [map_reduction]
    exact hdom
  · have hd := ((hV p hp hpV).2 L).2.1
    have he : geometricSingularCone f =
        {x : Fin 10 → L | eval₂ (Int.castRingHom L) x F=0 ∧
          gradient (map (Int.castRingHom L) F) x=0} := by
      ext x
      simp only [geometricSingularCone,f,map_reduction,Set.mem_setOf_eq,HessianTheorem11.gradient,
        _root_.funext_iff,Pi.zero_apply,eval_map]
      rfl
    rw [he]
    exact hd

end CubicTenVariables.ReducedFiniteFieldGeometry
