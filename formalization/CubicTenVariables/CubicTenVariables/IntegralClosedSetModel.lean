import CubicTenVariables.GaloisClosedSetModel
import CubicTenVariables.FiniteRationalModelIntegral

/-! Fixed integral equations for the same Galois-stable closed geometric set.
The extended equation ideal is the actual vanishing ideal, not just an ideal
with the same radical. No assertion about positive-characteristic fibers is
made here. -/

noncomputable section
namespace CubicTenVariables.IntegralClosedSetModel
open MvPolynomial HessianTheorem11 RationalComponentDescent
open FiniteRationalModelIntegral

theorem span_integralFamily {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) ℚ) :
    Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField)
      (integralFamily f i))) =
    Ideal.span (Set.range (fun i => map (algebraMap ℚ GeometricField) (f i))) := by
  have hD : (commonDenominator f : GeometricField) ≠ 0 := by
    exact_mod_cast (commonDenominator_pos f).ne'
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    dsimp only
    rw [map_integralFamily_geometric]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi := Ideal.mul_mem_left
      (Ideal.span (Set.range (fun j => map (Int.castRingHom GeometricField)
        (integralFamily f j))))
      (C (commonDenominator f : GeometricField)⁻¹)
      (Ideal.subset_span (Set.mem_range_self i))
    rw [map_integralFamily_geometric, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hD,
      C_1, one_mul] at hi
    exact hi

/-- All coefficients are fixed integers; extension gives exactly the reduced
geometric ideal. Closedness and Galois stability are the only set hypotheses. -/
theorem exists_integral_equations {n : ℕ} (Z : Set (GeometricPoint n))
    (hclosed : AlgebraicallyClosedSet Z)
    (hstable : ∀ (σ : GeometricField ≃ₐ[ℚ] GeometricField),
      ∀ x ∈ Z, galoisPoint σ x ∈ Z) :
    ∃ m : ℕ, ∃ G : Fin m → MvPolynomial (Fin n) ℤ,
      Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
        vanishingIdeal GeometricField Z ∧
      ∀ x : GeometricPoint n,
        x ∈ Z ↔ ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0 := by
  obtain ⟨m, f, hf, hzero⟩ :=
    GaloisClosedSetModel.exists_rational_equations Z hclosed hstable
  refine ⟨m, integralFamily f, (span_integralFamily f).trans hf, ?_⟩
  intro x
  rw [hzero]
  exact forall_congr' (fun i => by
    rw [eval_integralFamily_eq_zero_iff, eval_map])

end CubicTenVariables.IntegralClosedSetModel
