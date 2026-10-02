import CubicTenVariables.RationalLinearSecondMoment

/-! The proved rational-plane moment controls every finite subset of the
same reduced plane. Its q^18-normalized mass is at most C/q, with C fixed
before the prime and every finite extension. No trace dichotomy is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.RationalPlaneMomentSubsets
open MvPolynomial Matrix HessianTheorem11 ProjectiveFourierIdentity RationalPlaneReduction
open scoped BigOperators Classical

theorem subset_moment_le {n : ℕ} {K : Type*} [Field K] [Fintype K]
    (F : MvPolynomial (Fin n) K) (ψ : AddChar K ℂ)
    (L : Submodule K (Fin n → K)) (U : Finset (Fin n → K))
    (hU : ∀ v ∈ U, v ∈ L) :
    ∑ v ∈ U, ‖normalizedFourierSum ψ F v‖^2 ≤
      ∑ v : L, ‖normalizedFourierSum ψ F v.val‖^2 := by
  have hsub : U ⊆ Finset.univ.filter (fun v => v ∈ L) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,hU v hv⟩
  calc
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => v ∈ L),
        ‖normalizedFourierSum ψ F v‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = _ := Finset.sum_subtype _ (by simp) _

theorem exists_normalized_bound_ten
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (L : Submodule ℚ (Fin 10 → ℚ)) (hL : Module.finrank ℚ L = 8) :
    ∃ (e : Fin 2 ↪ Fin 10) (A : Matrix (Fin 10) (Fin 10) ℤ),
      A.det ≠ 0 ∧ plane e A ℚ = L ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ (K : Type) [Field K] [Fintype K] [CharP K p] (ψ : AddChar K ℂ), ψ ≠ 1 →
          Module.finrank K (plane e A K) = 8 ∧
          ∀ U : Finset (Fin 10 → K), (∀ v ∈ U, v ∈ plane e A K) →
            (∑ v ∈ U, ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v‖^2) /
              (Fintype.card K : ℝ)^18 ≤ C / (Fintype.card K : ℝ) := by
  obtain ⟨e,A,hA,heq,N,hN,C,hC,hbound⟩ :=
    RationalLinearSecondMoment.exists_bound_ten smooth spread weil F hF hAn L hL
  refine ⟨e,A,hA,heq,N,hN,C,hC,?_⟩
  intro p hp hpN K _ _ _ ψ hψ
  obtain ⟨hdim,hm⟩ := hbound p hp hpN K ψ hψ
  refine ⟨hdim,?_⟩
  intro U hU
  have hmoment := (subset_moment_le (map (Int.castRingHom K) F) ψ (plane e A K) U hU).trans hm
  have hq : 0 < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ (C * (Fintype.card K : ℝ)^17) / (Fintype.card K : ℝ)^18 :=
      div_le_div_of_nonneg_right hmoment (le_of_lt (pow_pos hq 18))
    _ = _ := by
      rw [show (18 : ℕ) = 17+1 by decide, pow_succ]
      field_simp

end CubicTenVariables.RationalPlaneMomentSubsets
