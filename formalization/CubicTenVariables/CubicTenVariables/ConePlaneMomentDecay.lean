import CubicTenVariables.DegreeSpanEightPlane
import CubicTenVariables.DegreeSpanReduction
import CubicTenVariables.RationalKernelMomentDecay
import CubicTenVariables.SmoothInfinityGeometricIntegralityProved
import CubicTenVariables.CubicGenericIntegralityUniform

/-! Moment decay for the actual reductions of an integral polynomial model
contained in an eight-dimensional rational plane. Plane containment is supplied
by literal ideal-membership certificates; all integrality and spreading inputs
are proved internally. Only the stated plane-curve Weil premise is used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.ConePlaneMomentDecay
open MvPolynomial Matrix HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven Filter
open scoped BigOperators Classical Topology

theorem exists_decay
    (weil : Literature.AffinePlaneCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {t : ℕ} (G : Fin t → MvPolynomial (Fin 10) ℤ)
    (B : Matrix (Fin 2) (Fin 10) ℤ)
    (hB : Module.finrank ℚ (LinearMap.ker
      (B.map (Int.castRingHom ℚ)).mulVecLin) = 8)
    (hrows : ∀ j, map (Int.castRingHom ℚ) (DegreeSpanEightPlane.rowPolynomial B j) ∈
      Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i)))) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      ∀ (K : ℕ → Type) [∀ a, Field (K a)] [∀ a, Fintype (K a)]
        [∀ a, CharP (K a) p]
        (ψ : ∀ a, AddChar (K a) ℂ) (U : ∀ a, Finset (Fin 10 → K a)),
        (∀ a, 1 ≤ a → Fintype.card (K a) = p^a) →
        (∀ a, 1 ≤ a → ψ a ≠ 1) →
        (∀ a, 1 ≤ a → ∀ v ∈ U a, ∀ i,
          eval v (map (Int.castRingHom (K a)) (G i)) = 0) →
        Tendsto (fun a =>
          (∑ v ∈ U a, ‖normalizedFourierSum (ψ a) (map (Int.castRingHom (K a)) F) v‖^2) /
            (p : ℝ)^(a*18)) atTop (𝓝 0) := by
  obtain ⟨D,hD,hcontain⟩ := DegreeSpanReduction.exists_uniform_family_reduction G
    (DegreeSpanEightPlane.rowPolynomial B) hrows
  obtain ⟨N,hN,hlimit⟩ := RationalKernelMomentDecay.exists_decay_ten
    SmoothInfinityGeometricIntegralityProved.proved CubicGenericIntegralityUniform.proved weil F hF hAn B hB
  refine ⟨N*D,one_le_mul_of_one_le_of_one_le hN hD,?_⟩
  intro p hp hpND K _ _ _ ψ U hcard hψ hU
  have hpN : ¬ p ∣ N := fun h => hpND (dvd_mul_of_dvd_left h D)
  have hpD : ¬ p ∣ D := fun h => hpND (dvd_mul_of_dvd_right h N)
  apply hlimit p hp hpN K ψ U hcard hψ
  intro a ha v hv
  ext j
  have h := hcontain p hpD (K a) v (hU a ha v hv) j
  simpa only [DegreeSpanEightPlane.map_rowPolynomial, DegreeSpanEightPlane.eval_rowPolynomial,
    Pi.zero_apply] using h

end CubicTenVariables.ConePlaneMomentDecay
