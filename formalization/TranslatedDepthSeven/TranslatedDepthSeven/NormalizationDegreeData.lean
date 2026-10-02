import TranslatedDepthSeven.GenericRankShiftedBinomial
import TranslatedDepthSeven.HomogeneousLinearElimination

/-!
# Dimension and degree from a homogeneous linear normalization

For a homogeneous integral cone, a finite linear projection to affine space
has generic fibre length equal to the projective degree.  This file keeps the
datum completely literal: the parameters are displayed degree-one forms and
the degree is the fraction-field rank of the resulting finite algebra.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option synthInstance.maxHeartbeats 200000

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The generic rank of a displayed homogeneous linear normalization. -/
def HomogeneousLinearNormalizationData.genericRank
    {K : Type u} [Field K] {sigma : Type v}
    {I : Ideal (MvPolynomial sigma K)}
    (D : HomogeneousLinearNormalizationData I) : ℕ :=
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial sigma K ⧸ I
  let g := D.hom
  letI : Algebra B A := g.toRingHom.toAlgebra
  Module.finrank (FractionRing B)
    (LocalizedModule (nonZeroDivisors B) A)

/-- A homogeneous prime cone has affine dimension `n` and degree `d` when
it has a finite injective degree-one normalization by `n` parameters whose
literal generic rank is `d`. -/
def HasHomogeneousLinearNormalizationDimensionDegree
    {K : Type u} [Field K] {sigma : Type v}
    (I : Ideal (MvPolynomial sigma K)) (n d : ℕ) : Prop :=
  I.IsPrime ∧
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule sigma K) ∧
    ∃ D : HomogeneousLinearNormalizationData I,
      D.parameterCount = n ∧ D.genericRank = d

/-- Every displayed normalization of a prime homogeneous cone supplies its
own literal dimension--degree datum. -/
theorem HomogeneousLinearNormalizationData.hasDimensionDegree
    {K : Type u} [Field K] {sigma : Type v} [Finite sigma]
    {I : Ideal (MvPolynomial sigma K)}
    (D : HomogeneousLinearNormalizationData I)
    (hprime : I.IsPrime)
    (hhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule sigma K)) :
    HasHomogeneousLinearNormalizationDimensionDegree I
      D.parameterCount D.genericRank := by
  exact ⟨hprime, hhomogeneous, D, rfl, rfl⟩

/-- The degree supplied by a positive-dimensional finite injective
normalization is positive. -/
theorem HomogeneousLinearNormalizationData.genericRank_pos
    {K : Type u} [Field K] {sigma : Type v} [Finite sigma]
    {I : Ideal (MvPolynomial sigma K)}
    (D : HomogeneousLinearNormalizationData I)
    (hprime : I.IsPrime) : 0 < D.genericRank := by
  simpa only [HomogeneousLinearNormalizationData.genericRank,
    HomogeneousLinearNormalizationData.hom, linearNormalizationHomFin] using
    (genericRank_pos_of_finite_injective_linearNormalizationFin
      K sigma I D.forms hprime D.hom_finite D.hom_injective)

/-- The normalization-degree datum implies an explicit shifted-binomial
squeeze for the cumulative Hilbert function. -/
theorem HomogeneousLinearNormalizationData.exists_shiftedBinomialSqueeze
    {K : Type u} [Field K] {sigma : Type v} [Finite sigma]
    {I : Ideal (MvPolynomial sigma K)}
    (D : HomogeneousLinearNormalizationData I)
    (hpositive : 0 < D.parameterCount)
    (hprime : I.IsPrime)
    (hhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule sigma K)) :
    ∃ E C : ℕ, ∀ n : ℕ,
      D.genericRank * (n + D.parameterCount).choose D.parameterCount ≤
          Module.finrank K
            (quotientTotalDegreeFiltration K sigma I (n + E)) ∧
        Module.finrank K (quotientTotalDegreeFiltration K sigma I n) ≤
          D.genericRank *
            (n + C + D.parameterCount).choose D.parameterCount := by
  letI : NeZero D.parameterCount := ⟨hpositive.ne'⟩
  simpa only [HomogeneousLinearNormalizationData.genericRank,
    HomogeneousLinearNormalizationData.hom, linearNormalizationHomFin] using
    (exists_genericRank_shifted_binomial_squeeze_fin
      K sigma I hhomogeneous hprime D.forms D.forms_isHomogeneous
        D.hom_finite D.hom_injective)

end

end TranslatedDepthSeven
