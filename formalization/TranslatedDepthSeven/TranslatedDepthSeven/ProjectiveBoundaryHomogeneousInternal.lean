import TranslatedDepthSeven.AffineChartProjectionBoundaryTopPart

/-!
# Homogeneity of the projective boundary ideal

Setting the distinguished homogeneous coordinate equal to zero preserves
total degree.  Consequently the image of a homogeneous ideal under this
specialization is homogeneous in the remaining variables.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ideal-theoretic boundary at infinity of a homogeneous ideal is
again homogeneous. -/
theorem projectiveBoundaryIdeal_isHomogeneous {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ)) :
    (projectiveBoundaryIdeal I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) ℚ) := by
  rw [Ideal.IsHomogeneous.iff_exists] at hI
  obtain ⟨S, hS⟩ := hI
  unfold projectiveBoundaryIdeal
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨g, ⟨s, hs, rfl⟩, rfl⟩ := hf
  obtain ⟨d, hd⟩ := s.2
  refine ⟨d, ?_⟩
  simpa [rationalSpecializeFirstCoordinate,
    restrictFirstPolynomialToZero] using
    (restrictFirstPolynomialToZero_isHomogeneous hd)

end

end TranslatedDepthSeven
