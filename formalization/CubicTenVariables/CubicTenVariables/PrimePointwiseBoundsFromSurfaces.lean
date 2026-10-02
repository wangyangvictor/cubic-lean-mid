import CubicTenVariables.CubicGenericSmoothness
import CubicTenVariables.ReducedCubicPointCountsFromSurfaces
import CubicTenVariables.PrimePointCountTransfer

/-! Prime complete-sum bounds from surface amplification and smooth cubic
Weil. The ambient estimate uses the internal generic smooth-section proof;
the hyperplane estimate uses the surface induction and actual cone geometry.
The fixed exceptional primes are absorbed by the elementary trivial bound.
No Browning or Hooley--Katz point-count proposition is assumed.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimePointwiseBoundsFromSurfaces
open MvPolynomial HessianTheorem11

/-- One constant precedes every prime and integral frequency, including
the exceptional primes and the zero-reduction frequency alternative. -/
theorem exists_uniform_bound
    (spread : CubicPrincipalOpenUniform.Uniform)
    (ampl : Literature.CubicSurfacePointCountAmplification)
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
    ReducedCubicPointCountsFromSurfaces.exists_hyperplane_bound spread ampl weil F hF hA
  apply PrimePointCountTransfer.exists_uniform_bound F hF (DA * DB)
    (Nat.mul_pos hDA hDB) 15 B (by norm_num) (zero_le_one.trans hB)
  intro p hp hpD
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨ha p hp (fun h ↦ hpD (dvd_mul_of_dvd_left h DB)), ?_⟩
  intro v hv
  simpa only [ZMod.card] using
    hb p hp (fun h ↦ hpD (dvd_mul_of_dvd_right h DA)) (ZMod p) v hv

end CubicTenVariables.PrimePointwiseBoundsFromSurfaces
