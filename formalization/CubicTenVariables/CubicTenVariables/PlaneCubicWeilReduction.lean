import CubicTenVariables.Literature.SmoothCubicWeil
import CubicTenVariables.PlaneCubicSingularGeometry
import CubicTenVariables.FiniteFieldCubicSingularPointCount
import CubicTenVariables.PlaneCurveHomogenizationCount
import CubicTenVariables.Literature.AffinePlaneCurveWeil

/-! Reduction of integral plane-cubic point counts to the smooth case.
Singular cubics use proved uniqueness, perfect-field descent and projection
from the resulting rational singular point. Only the smooth count is input.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlaneCubicWeilReduction
open MvPolynomial Literature PlaneCubicSingularGeometry

/-- A geometric singular point of an integral plane cubic descends over
every finite field. The existence hypothesis is the negation of the actual
geometric smoothness condition, not a supplied rational-point assumption. -/
theorem rational_singular_of_not_smooth
    {K : Type} [Field K] [Fintype K]
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3)
    (hI : GeometricallyIntegralForm F) (hs : ¬ ProjectivelySmooth F) :
    ∃ z : Fin 3 → K, z ≠ 0 ∧ eval z F = 0 ∧ HessianTheorem11.gradient F z = 0 := by
  apply exists_rational_singular_of_geometric F hF hI
  unfold ProjectivelySmooth at hs
  push_neg at hs
  obtain ⟨z, hz, hne⟩ := hs
  exact ⟨z, hne, hz⟩

/-- The constant is selected before the field and coefficients. Singular
integral cubics require no finite-field point-count input. -/
theorem exists_integral_cone_bound (weil : SmoothPlaneCubicWeil) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (K : Type) [Field K] [Fintype K]
        (F : MvPolynomial (Fin 3) K),
        F.IsHomogeneous 3 → (2 : K) ≠ 0 → (3 : K) ≠ 0 →
        GeometricallyIntegralForm F →
        ((affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^2)^2 ≤
          C * ((Fintype.card K : ℝ)-1)^2 * (Fintype.card K : ℝ) := by
  obtain ⟨B, hB, hsing⟩ := FiniteFieldCubicSingularPointCount.exists_bound 2 (by decide)
  refine ⟨100+B^2, by nlinarith [sq_nonneg B], ?_⟩
  intro K _ _ F hF h2 h3 hI
  have hq : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast Nat.succ_le_of_lt
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty K))
  by_cases hs : ProjectivelySmooth F
  · apply (weil K F hI.1 hF hs).trans
    gcongr
    nlinarith [sq_nonneg B]
  · have hb := hsing K F hF h2 h3 hI (geometricallyNonconical F hF hI)
      (rational_singular_of_not_smooth F hF hI hs)
    simp only [Nat.sub_self, pow_zero, mul_one] at hb
    have hsq : ((affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^2)^2 ≤
        (B * ((Fintype.card K : ℝ)-1))^2 := by
      have h := mul_self_le_mul_self (abs_nonneg _) hb
      simpa only [← sq, sq_abs] using h
    calc
      _ ≤ (B * ((Fintype.card K : ℝ)-1))^2 := hsq
      _ = B^2 * ((Fintype.card K : ℝ)-1)^2 := mul_pow _ _ _
      _ ≤ B^2 * ((Fintype.card K : ℝ)-1)^2 * (Fintype.card K : ℝ) :=
        le_mul_of_one_le_right (by positivity) hq
      _ ≤ _ := by
        gcongr
        linarith

/-- The plane-curve input used by the main theorem follows from a point
count for smooth projective cubics alone. The singular and affine-closure
steps are proved above and in the imported geometry/counting modules. -/
theorem affine (weil : SmoothPlaneCubicWeil) : AffinePlaneCubicWeil := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_cone_bound weil
  refine ⟨2*C+32, by linarith, ?_⟩
  intro K _ _ f h2 h3 hd hgeo
  apply PlaneCurveHomogenization.affine_square_bound_of_closure f hd C
  apply hbound K (PlaneCurveHomogenization.closure f) ?_ h2 h3
    (PlaneCurveHomogenization.closure_geometricallyIntegral f (by omega) hgeo)
  simpa only [hd] using PlaneCurveHomogenization.closure_isHomogeneous f

end CubicTenVariables.PlaneCubicWeilReduction
