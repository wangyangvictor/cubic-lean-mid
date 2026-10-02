import HessianTheorem11.AllColumns
import HessianTheorem11.BibleCompleted

/-! Individually named exact source targets completing the unconditional
ledger. Previously proved individual declarations retain their names. -/
noncomputable section
namespace HessianTheorem11.Unconditional
open Module MvPolynomial BibleTargets BibleProjectiveGeometry BibleRestrictions
  PolynomialRestriction BibleHyperplanes

theorem I12 : Targets.I12 := Completed.theorem1_1_columns.incidence12
theorem I13 : Targets.I13 := Completed.theorem1_1_columns.incidence13
theorem R11 : Targets.R11 := Completed.theorem1_1_columns.rank11
theorem S11 : Targets.S11 := Completed.theorem1_1_columns.singular11
theorem S12 : Targets.S12 := Completed.theorem1_1_columns.singular12

theorem B08 (F : AnisotropicCubic 12) : singularDimension F.polynomial ≤ 6 :=
  (BibleCompleted.theorem_I_1_1 F).singularDimension

theorem B11 (F : AnisotropicCubic 12)
    (B : Matrix (Fin 12) (Fin 11) GeometricField) (hB : Function.Injective B.mulVec) :
    Irreducible (sectionPolynomial F B) ∧
      IsDomain (GeometricPolynomial 11 ⧸ Ideal.span {sectionPolynomial F B}) :=
  (BibleCompleted.theorem_I_1_1 F).geometricSectionsIntegral B hB

theorem B12 (F : AnisotropicCubic 12)
    (B : Matrix (Fin 12) (Fin 11) GeometricField) (hB : Function.Injective B.mulVec) :
    projectiveDimension (singularCone (sectionPolynomial F B)) ≤ 6 :=
  (BibleCompleted.theorem_I_1_1 F).geometricSectionsSingular B hB

theorem B13 (F : AnisotropicCubic 12)
    (B : Matrix (Fin 12) (Fin 11) ℚ) (hB : Function.Injective B.mulVec) :
    projectiveDimension (singularLocus (restrict B F.polynomial)) ≤ 4 :=
  (BibleCompleted.theorem_I_1_1 F).rationalSectionsSingular B hB

theorem B18 (F : AnisotropicCubic 12) (M : Submodule ℚ (Fin 12 → ℚ))
    (hm : 11 ≤ finrank ℚ M) :
    singularDimension (subspaceCubic F M).polynomial ≤ (finrank ℚ M - 6 : ℕ) :=
  (BibleCompleted.theorem_I_1_1 F).restrictionsSingularStrong M hm

end HessianTheorem11.Unconditional
