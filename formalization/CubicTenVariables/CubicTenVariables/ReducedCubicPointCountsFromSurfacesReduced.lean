import CubicTenVariables.ReducedFiniteFieldGeometry
import CubicTenVariables.CubicConePointCountFromSurfacesReduced

/-! Actual ten-variable hyperplane counts with only the isolated-conjugate
cubic-surface remainder. -/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.ReducedCubicPointCountsFromSurfacesReduced

open MvPolynomial HessianTheorem11 PolynomialRestriction Literature

theorem exists_hyperplane_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p]
        (v : Fin 10 → K), v ≠ 0 →
        |(Nat.card {x : Fin 10 → K // eval₂ (Int.castRingHom K) x F = 0 ∧
          dotProduct v x = 0} : ℝ) - (Fintype.card K : ℝ)^8| ≤
          C * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ)^6 := by
  obtain ⟨D,hD,hgeo⟩ :=
    ReducedFiniteFieldGeometry.exists_uniform_bound spread F hF hA
  obtain ⟨N,hN,C,hC,hcount⟩ :=
    CubicConePointCountFromSurfacesReduced.exists_nine_variable_bound isolated weil
  refine ⟨D*N, Nat.mul_pos hD hN, C, hC, ?_⟩
  intro p hp hpDN K _ _ _ v hv
  have hpD : ¬ p ∣ D := fun h => hpDN (dvd_mul_of_dvd_left h N)
  have hpN : ¬ p ∣ N := fun h => hpDN (dvd_mul_of_dvd_right h D)
  have hNK : (N : K) ≠ 0 := (CharP.cast_eq_zero_iff K p N).not.mpr hpN
  obtain ⟨_hp3,hgeom⟩ := hgeo p hp hpD
  obtain ⟨B,hB,hRange⟩ := HyperplaneFrames.exists_frame v hv
  obtain ⟨hI,hV⟩ := (hgeom K).2.2 B hB
  have hc := hcount K hNK (restrict B (map (Int.castRingHom K) F))
    (homogeneous_restrict B _ (hF.map _)) hI (hV.trans (by decide : 4 ≤ 5))
  have he := AffineConePointCount.hyperplane_zero_card
    (map (Int.castRingHom K) F) v B hB hRange
  simp only [eval_map] at he
  change |(Nat.card {x : Fin 9 → K //
    eval x (restrict B (map (Int.castRingHom K) F)) = 0} : ℝ) - _| ≤ _ at hc
  rw [he] at hc
  exact hc

end CubicTenVariables.ReducedCubicPointCountsFromSurfacesReduced
