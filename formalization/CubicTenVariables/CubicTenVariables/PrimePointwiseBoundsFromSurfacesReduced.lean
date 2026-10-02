import CubicTenVariables.CubicGenericSmoothness
import CubicTenVariables.ReducedCubicPointCountsFromSurfacesReduced
import CubicTenVariables.PrimePointCountTransfer

/-! Prime complete-sum bounds with only the isolated-conjugate cubic-surface
point-count remainder and the smooth cubic Weil input. -/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.PrimePointwiseBoundsFromSurfacesReduced

open MvPolynomial HessianTheorem11

theorem exists_uniform_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (weil : Literature.SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ∀ v : Fin 10 → ℤ,
      ((fun i ↦ (v i : ZMod p)) = 0 →
        ‖completeCubicSum F p v‖ ≤ C * (p : ℝ) ^ ((17 : ℝ) / 2)) ∧
      ((fun i ↦ (v i : ZMod p)) ≠ 0 →
        ‖completeCubicSum F p v‖ ≤ C * (p : ℝ) ^ 8) := by
  obtain ⟨DA,hDA,ha⟩ := CubicGenericSmoothness.exists_prime_bound weil F hF hA
  obtain ⟨DB,hDB,B,hB,hb⟩ :=
    ReducedCubicPointCountsFromSurfacesReduced.exists_hyperplane_bound
      spread isolated weil F hF hA
  apply PrimePointCountTransfer.exists_uniform_bound F hF (DA * DB)
    (Nat.mul_pos hDA hDB) 15 B (by norm_num) (zero_le_one.trans hB)
  intro p hp hpD
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨ha p hp (fun h ↦ hpD (dvd_mul_of_dvd_left h DB)), ?_⟩
  intro v hv
  simpa only [ZMod.card] using
    hb p hp (fun h ↦ hpD (dvd_mul_of_dvd_right h DA)) (ZMod p) v hv

end CubicTenVariables.PrimePointwiseBoundsFromSurfacesReduced
