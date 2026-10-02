import CubicTenVariables.Targets

/-! Exact dimension and anisotropy reductions for the full main theorem.
The ten-variable theorem remains an explicit, unproved target, not a
literature assumption. These lemmas justify reducing all n≥10 to n=10. -/
namespace CubicTenVariables
open MvPolynomial HessianTheorem11 PolynomialRestriction

theorem hasRationalZero_iff_not_anisotropic {n : ℕ} (F : RationalPolynomial n) :
    HasRationalZero F ↔ ¬ Anisotropic F := by
  classical
  simp only [HasRationalZero, Anisotropic]
  push_neg
  exact exists_congr fun x => and_comm

theorem hasRationalZero_of_restrict {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) ℚ) (hB : Function.Injective B.mulVec)
    (F : RationalPolynomial n) (h : HasRationalZero (restrict B F)) :
    HasRationalZero F := by
  obtain ⟨x,hx,hF⟩ := h
  refine ⟨B.mulVec x,?_,?_⟩
  · intro hz
    apply hx
    apply hB
    simpa only [Matrix.mulVec_zero] using hz
  · simpa only [eval_restrict] using hF

theorem hasRationalZero_zero {n : ℕ} (hn : 0 < n) :
    HasRationalZero (0 : RationalPolynomial n) := by
  refine ⟨fun _ => 1,?_,by simp⟩
  intro h
  have he := congrFun h ⟨0,hn⟩
  exact one_ne_zero he

/-- Restricting to the first ten coordinates proves every larger case;
the restricted polynomial is allowed to be zero. -/
theorem main_of_ten (h : TenVariableTheorem) : MainTheorem := by
  intro n hn F hF
  let B := coordinateInclusion (K := ℚ) hn
  exact hasRationalZero_of_restrict B (coordinateInclusion_injective hn) F
    (h (restrict B F) (homogeneous_restrict B F hF))

theorem main_iff_ten : MainTheorem ↔ TenVariableTheorem :=
  ⟨fun h => h 10 le_rfl,main_of_ten⟩

/-- The harmless zero polynomial is the only distinction between the
elementary statement and the nonzero-form hypersurface statement. -/
theorem hypersurface_iff_main : HypersurfaceTheorem ↔ MainTheorem := by
  constructor
  · intro h n hn F hF
    by_cases hz : F = 0
    · subst F
      exact hasRationalZero_zero (by omega)
    · exact h n hn F hz hF
  · intro h n hn F _ hF
    exact h n hn F hF

theorem ten_iff_no_anisotropic_cubic :
    TenVariableTheorem ↔ IsEmpty (AnisotropicCubic 10) := by
  constructor
  · intro h
    refine ⟨fun F => ?_⟩
    exact (hasRationalZero_iff_not_anisotropic F.polynomial).mp
      (h F.polynomial F.homogeneous) F.anisotropic
  · intro h F hF
    apply (hasRationalZero_iff_not_anisotropic F).mpr
    intro ha
    exact h.false ⟨F,hF,ha⟩

end CubicTenVariables
