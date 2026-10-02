import CubicTenVariables.UniformCoordinateSecondMoment
import CubicTenVariables.RationalPlaneReduction

/-! The uniform second moment over every rational codimension-two plane.
An actual integral equation model of that plane is constructed. Its good
reductions have the correct dimension, and the same N,C work for every
finite extension and every nontrivial additive character. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.RationalLinearSecondMoment
open MvPolynomial Matrix HessianTheorem11 PolynomialRestriction ProjectiveFourierIdentity
open RationalCodimensionTwoCoordinates RationalPlaneReduction IntegralFourierCoordinates
open scoped BigOperators Classical

theorem exists_uniform_bound (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil) {n : ℕ} (hn : 4 ≤ n)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (L : Submodule ℚ (Fin n → ℚ)) (hL : Module.finrank ℚ L = n-2) :
    ∃ (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ),
      A.det ≠ 0 ∧ plane e A ℚ = L ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ∀ (K : Type) [Field K] [Fintype K] [CharP K p] (ψ : AddChar K ℂ), ψ ≠ 1 →
          Module.finrank K (plane e A K) = n-2 ∧
          ∑ v : plane e A K, ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v.val‖^2 ≤
            C*(Fintype.card K : ℝ)^(2*n-3) := by
  obtain ⟨e,A,hA,hplane⟩ := exists_integral_coordinates L (by omega) hL
  obtain ⟨N,hN,C,hC,hbound⟩ := UniformCoordinateSecondMoment.exists_bound smooth spread weil hn
    (restrict A F) (homogeneous_restrict A F hF) (anisotropic_restrict_integral F hAn A hA) e
  have hdet : 1 ≤ A.det.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hA)
  refine ⟨e,A,hA,rational_eq L e A hA hplane,N*A.det.natAbs,
    one_le_mul_of_one_le_of_one_le hN hdet,C,hC,?_⟩
  intro p hp hNp K _ _ _ ψ hψ
  have hpN : ¬ p ∣ N := fun h => hNp (dvd_mul_of_dvd_left h A.det.natAbs)
  have hpA : ¬ p ∣ A.det.natAbs := fun h => hNp (dvd_mul_of_dvd_right h N)
  have hunit := residue_isUnit A p hpA K
  refine ⟨finrank_plane e A K hunit,?_⟩
  rw [second_moment_eq e A K hunit F ψ]
  exact hbound p hp hpN K ψ hψ

/-- Manuscript Lemma n10:second-moment in ten variables. The model is
given by the two literal integral linear equations in `plane`; it equals
the originally supplied rational L and has dimension eight in every
permitted finite field. The final exponent is seventeen. -/
theorem exists_bound_ten (smooth : Literature.SmoothInfinityGeometricIntegrality)
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
          ∑ v : plane e A K, ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v.val‖^2 ≤
            C*(Fintype.card K : ℝ)^17 := by
  simpa only [Nat.reduceSub, Nat.reduceMul] using
    exists_uniform_bound smooth spread weil (by norm_num : 4 ≤ 10) F hF hAn L hL

end CubicTenVariables.RationalLinearSecondMoment
