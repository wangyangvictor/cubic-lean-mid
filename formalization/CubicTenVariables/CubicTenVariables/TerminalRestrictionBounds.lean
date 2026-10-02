import CubicTenVariables.GeometryTen

/-!
The rational-restriction bound at the start of Bounds on terminal strata,
including restriction dimensions two and three. The final numerical deduction
is conditional on the actual contact-locus dimension lower bound, which is
not constructed here. All older geometry interfaces are supplied by proofs.
-/

noncomputable section
namespace CubicTenVariables.TerminalRestrictionBounds
open HessianTheorem11 Module

/-- The actual polynomial obtained by any injective rational restriction
obeys the radial singular-dimension bound in every positive dimension. -/
theorem restriction_singularDimension_le {n m : ℕ}
    (F : AnisotropicCubic n) (B : Matrix (Fin n) (Fin m) ℚ)
    (hB : Function.Injective B.mulVec) (hm : 0 < m) :
    singularDimension (PolynomialRestriction.restrict B F.polynomial) ≤
      ((2 * m - 3) / 3 : ℕ) :=
  BibleRestrictions.singularDimension_le_radial_floor
    Unconditional.finiteQuadraticConeCover provedSymmetricDeterminantalTangent
    (PolynomialRestriction.restrictedCubic B F hB) hm

/-- In actual finite-basis coordinates on every nonzero rational subspace. -/
theorem subspace_singularDimension_le {n : ℕ} (F : AnisotropicCubic n)
    (M : Submodule ℚ (Fin n → ℚ)) (hM : 0 < finrank ℚ M) :
    singularDimension (BibleRestrictions.subspaceCubic F M).polynomial ≤
      ((2 * finrank ℚ M - 3) / 3 : ℕ) :=
  restriction_singularDimension_le F (BibleRestrictions.subspaceMatrix M)
    (BibleRestrictions.subspaceMatrix_injective M) hM

/-- The ceiling in the rational terminal bound, expressed by natural-number
division. A contact locus of affine dimension at least t+1 forces this bound. -/
theorem terminal_codimension_numerics {n z d t : ℕ}
    (hd : 2 ≤ d) (hdim : d + z = n)
    (hcontact : t + 1 ≤ (2 * d - 3) / 3) :
    z ≤ n - (3 * (t + 2) + 1) / 2 := by
  omega

/-- Applies that numerical deduction to the actual singular dimension of a
rationally restricted anisotropic cubic. The contact lower bound remains
an explicit hypothesis, not a new geometric input or an existence claim. -/
theorem terminal_bound_of_contact_dimension {n z t : ℕ}
    (F : AnisotropicCubic n) (M : Submodule ℚ (Fin n → ℚ))
    (hM : 2 ≤ finrank ℚ M) (hdim : finrank ℚ M + z = n)
    (hcontact : (t + 1 : ℕ) ≤
      singularDimension (BibleRestrictions.subspaceCubic F M).polynomial) :
    z ≤ n - (3 * (t + 2) + 1) / 2 := by
  have hbound := subspace_singularDimension_le F M (by omega)
  have hnum : t + 1 ≤ (2 * finrank ℚ M - 3) / 3 := by
    exact_mod_cast hcontact.trans hbound
  exact terminal_codimension_numerics hM hdim hnum

/-- For n=10 and t=4 this gives affine exceptional-component dimension at
most one, once the geometric contact lower bound has been established. -/
theorem ten_variable_terminal_bound_of_contact_dimension {z : ℕ}
    (F : AnisotropicCubic 10) (M : Submodule ℚ (Fin 10 → ℚ))
    (hM : 2 ≤ finrank ℚ M) (hdim : finrank ℚ M + z = 10)
    (hcontact : (5 : ℕ) ≤
      singularDimension (BibleRestrictions.subspaceCubic F M).polynomial) :
    z ≤ 1 := by
  simpa using terminal_bound_of_contact_dimension (t := 4) F M hM hdim hcontact

end CubicTenVariables.TerminalRestrictionBounds
