import CubicTenVariables.Literature.HeathBrownTernaryPrimitiveCount
import TranslatedDepthSeven.PrimitiveProjectiveCurveAllChartsCountInternal
import TranslatedDepthSeven.AbsoluteIrreducibilityDescentInternal

/-! The fixed-form consequence of Heath-Brown used by this project is
proved here by elementary projective residue counting. This is the weaker
O_k(R^(1+η)) statement, not the published uniform R^(2/d+η) theorem. -/

namespace CubicTenVariables.HeathBrownTernaryPrimitiveCountInternal
noncomputable section
open MvPolynomial TranslatedDepthSeven TranslatedDepthSeven.Published Literature

/-- The literal former literature premise, with no counting premise. -/
theorem proved : HeathBrown2002FixedTernaryPrimitiveCount := by
  classical
  intro d hd k hkhom hk η hη
  obtain ⟨C, hC, hcount⟩ := exists_primitivePlaneCurve_linear_count
    hd k hkhom hk.irreducible
  refine ⟨C, hC, ?_⟩
  intro R hR
  have h := hcount R hR (primitiveTernaryZeros k R)
    (fun x hx ↦ (Finset.mem_filter.mp hx).2.1)
    (fun x hx ↦ (Finset.mem_filter.mp hx).2.2)
    (fun x hx ↦ (mem_integerSupNormBox_iff x).mp (Finset.mem_filter.mp hx).1)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hRreal (show (1 : ℝ) ≤ 1 + η by linarith)

end
end CubicTenVariables.HeathBrownTernaryPrimitiveCountInternal
