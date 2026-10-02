import TranslatedDepthSeven.IntegralHomogeneousIdealModel
import HessianTheorem11.AffineGeometry

/-! One actual integral equation family for a finite rational model. -/

noncomputable section
namespace CubicTenVariables.FiniteRationalModelIntegral
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The product of the already constructed coefficient denominators. -/
def commonDenominator (f : ι → MvPolynomial (Fin n) ℚ) : ℕ :=
  ∏ i, mvPolynomialRationalCommonDenominator (f i)

theorem commonDenominator_pos (f : ι → MvPolynomial (Fin n) ℚ) :
    0 < commonDenominator f :=
  Finset.prod_pos (fun i _ => mvPolynomialRationalCommonDenominator_pos (f i))

/-- Clear each equation using the existing coefficient construction, then
multiply it by all the other denominators to obtain one common scalar. -/
def integralFamily (f : ι → MvPolynomial (Fin n) ℚ) (i : ι) :
    MvPolynomial (Fin n) ℤ := by
  classical
  exact C ((∏ j ∈ Finset.univ.erase i,
    mvPolynomialRationalCommonDenominator (f j) : ℕ) : ℤ) *
      clearRationalMvPolynomial (f i)

/-- The constructed integer equation is literally the same fixed common
nonzero multiple of the original rational equation for every index. -/
theorem map_integralFamily (f : ι → MvPolynomial (Fin n) ℚ) (i : ι) :
    map (Int.castRingHom ℚ) (integralFamily f i) =
      C (commonDenominator f : ℚ) * f i := by
  classical
  unfold integralFamily
  rw [map_mul, map_C, map_clearRationalMvPolynomial, ← mul_assoc, ← C_mul]
  congr 2
  simp only [Int.coe_castRingHom, Int.cast_natCast]
  rw [← Nat.cast_mul]
  congr 1
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

/-- The same literal scalar identity after extension to the geometric
field, with the integral coefficients mapped directly. -/
theorem map_integralFamily_geometric (f : ι → MvPolynomial (Fin n) ℚ) (i : ι) :
    map (Int.castRingHom GeometricField) (integralFamily f i) =
      C (commonDenominator f : GeometricField) * map (algebraMap ℚ GeometricField) (f i) := by
  have hcomp : (algebraMap ℚ GeometricField).comp (Int.castRingHom ℚ) =
      Int.castRingHom GeometricField := by
    ext a
    simp
  have h := congrArg (map (algebraMap ℚ GeometricField)) (map_integralFamily f i)
  simpa only [map_map, hcomp, map_mul, map_C, map_natCast] using h

/-- Evaluation of the constructed integral equation is the same common
scalar times evaluation of the rational equation. -/
theorem eval_integralFamily_geometric (f : ι → MvPolynomial (Fin n) ℚ)
    (i : ι) (x : GeometricPoint n) :
    eval₂ (Int.castRingHom GeometricField) x (integralFamily f i) =
      (commonDenominator f : GeometricField) * eval₂ (algebraMap ℚ GeometricField) x (f i) := by
  have h := congrArg (eval x) (map_integralFamily_geometric f i)
  simpa only [eval_map, eval_mul, eval_C] using h

/-- Clearing the finite family changes none of its geometric solutions. -/
theorem eval_integralFamily_eq_zero_iff (f : ι → MvPolynomial (Fin n) ℚ)
    (i : ι) (x : GeometricPoint n) :
    eval₂ (Int.castRingHom GeometricField) x (integralFamily f i) = 0 ↔
      eval₂ (algebraMap ℚ GeometricField) x (f i) = 0 := by
  rw [eval_integralFamily_geometric]
  exact mul_eq_zero.trans (or_iff_right (by
    exact_mod_cast (commonDenominator_pos f).ne' : (commonDenominator f : GeometricField) ≠ 0))

/-- Literal equality of the complete simultaneous zero sets. -/
theorem zeroSet_integralFamily (f : ι → MvPolynomial (Fin n) ℚ) :
    {x : GeometricPoint n | ∀ i, eval₂ (Int.castRingHom GeometricField) x (integralFamily f i) = 0} =
      {x : GeometricPoint n | ∀ i, eval₂ (algebraMap ℚ GeometricField) x (f i) = 0} := by
  ext x
  exact forall_congr' (fun i => eval_integralFamily_eq_zero_iff f i x)

/-- A finite rational family has an indexed integral model with one
nonzero integer clearing scalar and exactly the same geometric zeros. -/
theorem exists_integral_family (f : ι → MvPolynomial (Fin n) ℚ) :
    ∃ (D : ℤ) (G : ι → MvPolynomial (Fin n) ℤ), D ≠ 0 ∧
      (∀ i, map (Int.castRingHom ℚ) (G i) = C (D:ℚ) * f i) ∧
      (∀ i, map (Int.castRingHom GeometricField) (G i) =
        C (D:GeometricField) * map (algebraMap ℚ GeometricField) (f i)) ∧
      {x : GeometricPoint n | ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0} =
        {x : GeometricPoint n | ∀ i, eval₂ (algebraMap ℚ GeometricField) x (f i) = 0} := by
  refine ⟨commonDenominator f, integralFamily f, ?_, ?_, ?_, zeroSet_integralFamily f⟩
  · exact_mod_cast (commonDenominator_pos f).ne'
  · intro i
    simpa only [Int.cast_natCast] using map_integralFamily f i
  · intro i
    simpa only [Int.cast_natCast] using map_integralFamily_geometric f i

end CubicTenVariables.FiniteRationalModelIntegral
