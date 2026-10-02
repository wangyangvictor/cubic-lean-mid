import CubicTenVariables.FixedEquationDimensionReduction
import CubicTenVariables.TranslatedHessianLeadingGeometry

/-! Uniform geometric dimension reduction for the actual ambient Hessian
rank loci and singular locus. The one exceptional integer is selected before
the prime and before every field of that characteristic. The proof uses the
original integral equations; no finite-field point-count or spreading premise
is assumed. -/

noncomputable section
namespace CubicTenVariables.ReducedHessianRankDimensions
open MvPolynomial HessianTheorem11 TranslatedHessianMinors
open FixedEquationNormalization FixedEquationDimensionReduction

/-- The original ambient minors, reindexed by a finite interval. There is
no cubic equation in this family. -/
def rankEquations {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (r : ℕ)
    (i : Fin (Fintype.card (MinorIndex n r))) : MvPolynomial (Fin n) ℤ :=
  equation (hessianPolynomial F) ((Fintype.equivFin (MinorIndex n r)).symm i)

theorem rank_equationIdeal_eq {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (r : ℕ) :
    equationIdeal (rankEquations F r) ℚ =
      TranslatedHessianLeadingGeometry.rationalIdeal F r := by
  unfold equationIdeal equationsOver TranslatedHessianLeadingGeometry.rationalIdeal
  congr 1
  ext P
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨(Fintype.equivFin (MinorIndex n r)).symm i,
      (map_hessian_equation (Int.castRingHom ℚ) F _).symm⟩
  · rintro ⟨i,rfl⟩
    refine ⟨(Fintype.equivFin (MinorIndex n r)) i, ?_⟩
    simp only [rankEquations, Equiv.symm_apply_apply, map_hessian_equation]

/-- The literal common-zero set is the whole ambient rank locus over any
field, including points away from the cubic. -/
theorem rank_zeroSet_eq {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (r : ℕ)
    (K : Type*) [Field K] :
    zeroSet (rankEquations F r) K =
      {x : Fin n → K | (hessian (map (Int.castRingHom K) F) x).rank ≤ r} := by
  ext x
  change (∀ i, eval₂ (Int.castRingHom K) x (rankEquations F r i) = 0) ↔
    (hessian (map (Int.castRingHom K) F) x).rank ≤ r
  have h := hessian_translatedEquation_zero_iff (Int.castRingHom K) F 0 r x
  simp only [translatedEquation, translatedMinor, Matrix.map_zero, map_zero,
    add_zero, zero_add] at h
  rw [← h]
  constructor
  · intro hx i
    simpa only [rankEquations, Equiv.symm_apply_apply] using
      hx ((Fintype.equivFin (MinorIndex n r)) i)
  · intro hx i
    exact hx _

/-- For each fixed rank label the actual reduced coordinate ring has the
proved characteristic-zero dimension bound in every good characteristic. -/
theorem exists_rank_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (r : ℕ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (p : ℕ), p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p],
        ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
          {x : Fin 10 → K | (hessian (map (Int.castRingHom K) F) x).rank ≤ r}) ≤
          (TranslatedHessianLeadingGeometry.tauNat r : Dimension) := by
  have hp : equationIdeal (rankEquations F r) ℚ ≠ ⊤ := by
    rw [rank_equationIdeal_eq]
    exact TranslatedHessianLeadingGeometry.rationalIdeal_ne_top F hF r
  have hd : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
      equationIdeal (rankEquations F r) ℚ) ≤
        (TranslatedHessianLeadingGeometry.tauNat r : Dimension) := by
    rw [rank_equationIdeal_eq]
    exact TranslatedHessianLeadingGeometry.quotient_dimension_le F hF hA r
  obtain ⟨D,hD,hbound⟩ := exists_good_characteristic_dimension_bound
    (rankEquations F r) hp hd
  refine ⟨D,hD,?_⟩
  intro p hp hpD K _ _
  rw [← rank_zeroSet_eq F r K]
  exact (hbound p hp hpD K).2

theorem exists_rank_two_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (p : ℕ), p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p],
        ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
          {x : Fin 10 → K | (hessian (map (Int.castRingHom K) F) x).rank ≤ 2}) ≤ 4 := by
  simpa [TranslatedHessianLeadingGeometry.tauNat] using exists_rank_bound F hF hA 2

/-- The gradient-only zero set is controlled, without needing to divide
Euler's identity by three in the target field. -/
theorem exists_gradient_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (p : ℕ), p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p],
        ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
          {x : Fin 10 → K | gradient (map (Int.castRingHom K) F) x = 0}) ≤ 5 := by
  have he : equationIdeal (CubicMassEquations.gradientEquation F) ℚ =
      CubicMassEquations.rationalGradientIdeal F := rfl
  have hp : equationIdeal (CubicMassEquations.gradientEquation F) ℚ ≠ ⊤ := by
    rw [he]
    exact CubicMassEquations.rationalGradientIdeal_ne_top F hF
  have hd : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
      equationIdeal (CubicMassEquations.gradientEquation F) ℚ) ≤ (5 : Dimension) := by
    rw [he]
    exact CubicMassEquations.gradient_quotient_dimension_le_five F hF hA
  obtain ⟨D,hD,hbound⟩ := exists_good_characteristic_dimension_bound
    (CubicMassEquations.gradientEquation F) hp hd
  refine ⟨D,hD,?_⟩
  intro p hp hpD K _ _
  have hz : zeroSet (CubicMassEquations.gradientEquation F) K =
      {x : Fin 10 → K | gradient (map (Int.castRingHom K) F) x = 0} := by
    ext x
    exact CubicMassEquations.gradient_equations_zero_iff _ F x
  rw [← hz]
  exact (hbound p hp hpD K).2

/-- A single exceptional integer works for both ambient rank two and the
gradient zero set. -/
theorem exists_rank_two_and_gradient_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (p : ℕ), p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p],
        ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
          {x : Fin 10 → K | (hessian (map (Int.castRingHom K) F) x).rank ≤ 2}) ≤ 4 ∧
        ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
          {x : Fin 10 → K | gradient (map (Int.castRingHom K) F) x = 0}) ≤ 5 := by
  obtain ⟨D₁,hD₁,h₁⟩ := exists_rank_two_bound F hF hA
  obtain ⟨D₂,hD₂,h₂⟩ := exists_gradient_bound F hF hA
  refine ⟨D₁*D₂, by nlinarith, ?_⟩
  intro p hp hpD K _ _
  exact ⟨h₁ p hp (fun h => hpD (dvd_mul_of_dvd_left h _)) K,
    h₂ p hp (fun h => hpD (dvd_mul_of_dvd_right h _)) K⟩

/-- The actual hypersurface singular set retains both F=0 and all first
partials equal to zero. Its reduced coordinate ring is bounded by the
gradient-only one, in every field of each good characteristic. -/
theorem exists_rank_two_and_singular_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (p : ℕ), p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p],
        ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
          {x : Fin 10 → K | (hessian (map (Int.castRingHom K) F) x).rank ≤ 2}) ≤ 4 ∧
        ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
          {x : Fin 10 → K | eval₂ (Int.castRingHom K) x F = 0 ∧
            gradient (map (Int.castRingHom K) F) x = 0}) ≤ 5 := by
  obtain ⟨D,hD,hbound⟩ := exists_rank_two_and_gradient_bound F hF hA
  refine ⟨D,hD,?_⟩
  intro p hp hpD K _ _
  obtain ⟨hr,hg⟩ := hbound p hp hpD K
  refine ⟨hr, le_trans ?_ hg⟩
  apply ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor (show vanishingIdeal K
      {x : Fin 10 → K | gradient (map (Int.castRingHom K) F) x = 0} ≤
      vanishingIdeal K {x : Fin 10 → K | eval₂ (Int.castRingHom K) x F = 0 ∧
        gradient (map (Int.castRingHom K) F) x = 0} from
      fun _ hf x hx => hf x hx.2))
  exact Ideal.Quotient.factor_surjective _

end CubicTenVariables.ReducedHessianRankDimensions
