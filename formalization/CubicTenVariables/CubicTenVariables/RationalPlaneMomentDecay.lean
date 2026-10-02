import CubicTenVariables.RationalPlaneMomentSubsets
import CubicTenVariables.MomentTraceNumerics

/-! Actual cubic moments on arbitrary subsets of a rational plane tend
to zero after q^18 normalization along finite extensions. The geometric inputs
have internal proofs; the affine curve Weil bound remains assumed. In particular,
no lisse-sheaf or pointwise-trace conclusion is asserted. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CubicTenVariables.RationalPlaneMomentDecay
open MvPolynomial Matrix HessianTheorem11 ProjectiveFourierIdentity RationalPlaneReduction
open Filter
open scoped BigOperators Classical Topology

theorem exists_decay_ten
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (L : Submodule ℚ (Fin 10 → ℚ)) (hL : Module.finrank ℚ L = 8) :
    ∃ (e : Fin 2 ↪ Fin 10) (A : Matrix (Fin 10) (Fin 10) ℤ),
      A.det ≠ 0 ∧ plane e A ℚ = L ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ (K : ℕ → Type) [∀ a, Field (K a)] [∀ a, Fintype (K a)]
          [∀ a, CharP (K a) p]
          (ψ : ∀ a, AddChar (K a) ℂ) (U : ∀ a, Finset (Fin 10 → K a)),
          (∀ a, 1 ≤ a → Fintype.card (K a) = p^a) →
          (∀ a, 1 ≤ a → ψ a ≠ 1) →
          (∀ a, 1 ≤ a → ∀ v ∈ U a, v ∈ plane e A (K a)) →
          Tendsto (fun a =>
            (∑ v ∈ U a, ‖normalizedFourierSum (ψ a) (map (Int.castRingHom (K a)) F) v‖^2) /
              (p : ℝ)^(a*18)) atTop (𝓝 0) := by
  obtain ⟨e,A,hA,heq,N,hN,C,hC,hbound⟩ :=
    RationalLinearSecondMoment.exists_bound_ten smooth spread weil F hF hAn L hL
  refine ⟨e,A,hA,heq,N,hN,?_⟩
  intro p hp hpN K _ _ _ ψ U hcard hψ hU
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply MomentTraceNumerics.normalized_moment_tendsto (p : ℝ) C hp2 17
    (fun a => ∑ v ∈ U a,
      ‖normalizedFourierSum (ψ a) (map (Int.castRingHom (K a)) F) v‖^2)
  · exact Eventually.of_forall fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with a ha
    have hb := (hbound p hp hpN (K a) (ψ a) (hψ a ha)).2
    have hs := RationalPlaneMomentSubsets.subset_moment_le
      (map (Int.castRingHom (K a)) F) (ψ a) (plane e A (K a)) (U a) (hU a ha)
    have hc : (Fintype.card (K a) : ℝ) = (p : ℝ)^a := by
      rw [hcard a ha, Nat.cast_pow]
    exact hs.trans (by simpa only [hc, pow_mul] using hb)

end CubicTenVariables.RationalPlaneMomentDecay
