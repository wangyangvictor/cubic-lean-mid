import CubicTenVariables.DimensionReduction
import CubicTenVariables.Denominators

/-! Exact equivalence of the full rational hypersurface theorem with the
ten-variable integer problem. These are reductions; none asserts an inhabitant
of the still-open main theorem. Coefficients and solution coordinates are
cleared by the proved denominator constructions. -/

namespace CubicTenVariables
open MvPolynomial

/-- Clear polynomial coefficients, use an actual integral zero, then cancel
the nonzero scalar multiplying the original rational polynomial. -/
theorem ten_of_integer (h : IntegerTenVariableTheorem) : TenVariableTheorem := by
  intro F hF
  obtain ⟨c, hc, G, hG, hmap⟩ := exists_integral_homogeneous_multiple F hF
  have hz := hasRationalZero_of_hasIntegerZero (h G hG)
  rw [hmap] at hz
  exact (hasRationalZero_C_mul_iff F (c : ℚ) (by exact_mod_cast hc)).mp hz

/-- Conversely, a rational zero of an integer homogeneous cubic can be
cleared to a nonzero integer zero. -/
theorem integer_of_ten (h : TenVariableTheorem) : IntegerTenVariableTheorem := by
  intro G hG
  exact hasIntegerZero_of_hasRationalZero hG
    (h (map (Int.castRingHom ℚ) G) (hG.map _))

theorem ten_iff_integerTen : TenVariableTheorem ↔ IntegerTenVariableTheorem :=
  ⟨integer_of_ten, ten_of_integer⟩

/-- The complete n≥10 rational target, without any geometric restrictions,
is equivalent to the ten-variable integer target. -/
theorem main_iff_integerTen : MainTheorem ↔ IntegerTenVariableTheorem :=
  main_iff_ten.trans ten_iff_integerTen

theorem hypersurface_iff_integerTen :
    HypersurfaceTheorem ↔ IntegerTenVariableTheorem :=
  hypersurface_iff_main.trans main_iff_integerTen

/-- It suffices to contradict rational anisotropy for integer cubics in ten
variables. The hypothesis is the outstanding mathematical task, not a
literature assumption supplied by this development. -/
theorem main_of_integer_anisotropic_contradiction
    (h : ∀ G : MvPolynomial (Fin 10) ℤ, G.IsHomogeneous 3 →
      HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) G) → False) :
    MainTheorem := by
  apply main_iff_integerTen.mpr
  intro G hG
  apply (hasRationalZero_map_iff hG).mp
  apply (hasRationalZero_iff_not_anisotropic _).mpr
  exact h G hG

end CubicTenVariables
