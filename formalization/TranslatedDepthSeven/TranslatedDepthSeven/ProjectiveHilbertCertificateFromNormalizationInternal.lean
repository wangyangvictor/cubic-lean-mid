import TranslatedDepthSeven.HilbertPolynomialGrowthDegreeInternal
import TranslatedDepthSeven.PolynomialIntegralMultiplicityInternal
import TranslatedDepthSeven.StandardAlgebraicGeometry
import TranslatedDepthSeven.ParameterCountSurface
import TranslatedDepthSeven.FieldPolynomialKrullDimension

/-!
# The complete projective Hilbert certificate from linear normalization

The polynomial is constructed by homogeneous ideal induction. Finite
homogeneous module generators identify its degree and positive leading
coefficient. Integer values give integral multiplicity by forward
differences. Finally, integral-extension dimension identifies the number
of normalizing parameters with the affine cone dimension.

The only data displayed here is an actual finite injective homogeneous
linear normalization with at least one parameter; there is no Hilbert,
degree, or geometric-family assumption.
-/

namespace TranslatedDepthSeven

noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000

theorem exists_projectiveHilbertCertificate_of_normalization
    {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (D : HomogeneousLinearNormalizationData I) (hD : 0 < D.parameterCount) :
    ∃ d : ℕ, ∃ P : Polynomial ℚ,
      StandardAG.HasProjectiveDimensionDegreeWithPolynomial I (D.parameterCount - 1) d P := by
  obtain ⟨P, hdegree, hpositive, n₀, hP⟩ :=
    exists_homogeneousHilbertPolynomial_of_normalization I hIhom D hD
  obtain ⟨d, hd, hlc⟩ := exists_positive_nat_multiplicity_of_eventually_integral
    P hpositive (by
      refine ⟨n₀, ?_⟩
      intro n hn
      refine ⟨(Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1)) I n) : ℤ), ?_⟩
      simpa only [Int.cast_natCast] using (hP n hn).symm)
  refine ⟨d, P, ?_, hd, hdegree, ?_, n₀, ?_⟩
  · rw [D.ringKrullDim_eq_parameterPolynomial (N + 1) I hIprime,
      ringKrullDim_mvPolynomial_fin_eq_of_field K D.parameterCount]
    have heq : D.parameterCount - 1 + 1 = D.parameterCount := by omega
    exact_mod_cast heq.symm
  · simpa only [hdegree] using hlc
  · intro n hn
    exact hP n hn

end
end TranslatedDepthSeven
