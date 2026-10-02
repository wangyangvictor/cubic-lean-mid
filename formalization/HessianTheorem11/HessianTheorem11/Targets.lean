import HessianTheorem11.Geometry

/-! The exact nine requested propositions on the actual geometric invariants.
Their individual proofs are in the completed theorem modules; `AllColumns.lean`
proves the combined `Theorem11Columns` statement. -/

namespace HessianTheorem11.Targets

def I11 : Prop :=
  ∀ F : AnisotropicCubic 11, incidenceDimension F.polynomial ≤ 13
def I12 : Prop :=
  ∀ F : AnisotropicCubic 12, incidenceDimension F.polynomial ≤ 14
def I13 : Prop :=
  ∀ F : AnisotropicCubic 13, incidenceDimension F.polynomial ≤ 15

def R11 : Prop :=
  ∀ F : AnisotropicCubic 11, 10 ≤ genericHessianRank F.polynomial
def R12 : Prop :=
  ∀ F : AnisotropicCubic 12, 10 ≤ genericHessianRank F.polynomial
def R13 : Prop :=
  ∀ F : AnisotropicCubic 13, 10 ≤ genericHessianRank F.polynomial

def S11 : Prop :=
  ∀ F : AnisotropicCubic 11, singularDimension F.polynomial ≤ 5
def S12 : Prop :=
  ∀ F : AnisotropicCubic 12, singularDimension F.polynomial ≤ 6
def S13 : Prop :=
  ∀ F : AnisotropicCubic 13, singularDimension F.polynomial ≤ 7

/-- The combined statement proved in `Completed.theorem1_1_columns`. -/
structure Theorem11Columns : Prop where
  incidence11 : I11
  incidence12 : I12
  incidence13 : I13
  rank11 : R11
  rank12 : R12
  rank13 : R13
  singular11 : S11
  singular12 : S12
  singular13 : S13

end HessianTheorem11.Targets
