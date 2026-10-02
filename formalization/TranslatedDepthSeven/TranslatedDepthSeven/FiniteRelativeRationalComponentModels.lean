import TranslatedDepthSeven.FiniteRelativeIntegralParameterHeight
import TranslatedDepthSeven.RelativePersistentMultiplicityCertificate
import TranslatedDepthSeven.RankSevenPersistentSurfaceSmoothDevissage

/-!
# Finite relative models for rational component unions

This file isolates the component-theoretic half of relative specialization,
before any Jacobian chart is chosen.  A finite model catalogue consists of
fixed integral equations on finitely many locally closed parameter pieces.
For an actual rational prime component, a witness records an integral point
of an enlarged parameter space and the two localization statements

`J_model ⊆ P_Z` and
`f ∈ P_Z ⇒ C(D(u))^e f ∈ J_model` for some `e=e(f)`.

These are exactly what equality after localizing at the nonzero denominator
says.  A single exponent may be chosen after one fibre is fixed, because
`P_Z` is then finitely generated, but neither localization nor arbitrary
specialization supplies exponent one or a uniform exponent over all fibres.
The pointwise-power formulation therefore avoids the generally false
assertion that specialization and contraction to
`\mathbb Z[x]` commute without localization.

Each auxiliary coordinate is stored after multiplication by one fixed power
of the principal-open denominator.  It is therefore integral over the base
and comes with a fixed monic equation over `\mathbb Z[u]`.  Cauchy's bound,
proved in `FiniteRelativeIntegralParameterHeight`, then gives the height of
every specialized coordinate; no effective primary decomposition is used.

`FiniteEtaleRationalPrimeComponentUnionSpreading` is the narrow standard-AG
input for this component-model step.  Its construction uses generic
component splitting after a finite etale cover, Galois descent of stable
subsets, generic flatness/geometric reducedness after shrinking, finite flat
stratification, and Noetherian induction on the closed complement (Stacks
Tags `054V`, `055A`, `052B`, and `0H3Z`).  The
displayed proposition is a derived package of those standard statements,
not a verbatim theorem from the Stacks Project.  It contains no smooth chart,
degree estimate, or counting assertion; the ensuing height estimate is
proved internally from its literal monic equations.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite list of denominator-localized component models over one fixed
enlarged integral parameter space.  Counts are padded once, so one common
finite type indexes the generators and stratum equations for every model. -/
structure RelativeRationalSurfaceComponentModelCatalogue (M N : ℕ) where
  liftedParameterCount : ℕ
  baseCoordinate : Fin M → Fin liftedParameterCount
  baseCoordinate_injective : Function.Injective baseCoordinate
  modelCount : ℕ
  componentGeneratorCount : ℕ
  stratumEquationCount : ℕ
  parameterRelationDegree : ℕ
  /-- One common base principal-open denominator for the scaled finite-cover
  coordinates attached to each model. -/
  coverCoordinateDenominator : Fin modelCount →
    MvPolynomial (Fin M) ℤ
  /-- Lower coefficients of fixed monic equations for every scaled
  finite-cover coordinate.  Degrees are padded to one common value. -/
  parameterRelationCoefficient : Fin modelCount →
    Fin liftedParameterCount → Fin parameterRelationDegree →
      MvPolynomial (Fin M) ℤ
  componentGenerator : Fin modelCount → Fin componentGeneratorCount →
    RelativeIntegralAffinePolynomial liftedParameterCount N
  stratumEquation : Fin modelCount → Fin stratumEquationCount →
    MvPolynomial (Fin liftedParameterCount) ℤ
  parameterDenominator : Fin modelCount →
    MvPolynomial (Fin liftedParameterCount) ℤ

/-- The specialized ideal of one fixed component-union model. -/
def RelativeRationalSurfaceComponentModelCatalogue.specializedComponentIdeal
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (model : Fin models.modelCount)
    (parameter : Fin models.liftedParameterCount → ℤ) :
    Ideal (MvPolynomial (Fin N) ℤ) :=
  Ideal.span (Set.range fun j ↦
    specializeRelativeIntegralAffinePolynomial parameter
      (models.componentGenerator model j))

/-- An enlarged integral parameter lies on the fixed closed stratum of one
model. -/
def RelativeRationalSurfaceComponentModelCatalogue.OnStratum
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (model : Fin models.modelCount)
    (parameter : Fin models.liftedParameterCount → ℤ) : Prop :=
  ∀ r, MvPolynomial.eval parameter (models.stratumEquation model r) = 0

/-- The denominator of one model is nonzero at the enlarged parameter. -/
def RelativeRationalSurfaceComponentModelCatalogue.InDenominatorOpen
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (model : Fin models.modelCount)
    (parameter : Fin models.liftedParameterCount → ℤ) : Prop :=
  MvPolynomial.eval parameter (models.parameterDenominator model) ≠ 0

/-- A literal rational component-union model for one specialized projective
prime.  The pointwise denominator-power condition is the exact integral form
of equality after localizing the base. -/
structure RelativeRationalSurfaceComponentModelWitness
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (baseParameter : Fin M → ℤ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) where
  liftedParameter : Fin models.liftedParameterCount → ℤ
  modelIndex : Fin models.modelCount
  base_specialization : ∀ j,
    liftedParameter (models.baseCoordinate j) = baseParameter j
  coverCoordinateDenominator_nonzero :
    MvPolynomial.eval baseParameter
      (models.coverCoordinateDenominator modelIndex) ≠ 0
  liftedParameter_relation : ∀ j,
    Polynomial.eval (liftedParameter j)
      (specializedMonicIntegralParameterRelation
        (models.parameterRelationCoefficient modelIndex)
        baseParameter j) = 0
  onStratum : models.OnStratum modelIndex liftedParameter
  inDenominatorOpen : models.InDenominatorOpen modelIndex liftedParameter
  componentIdeal_le :
    models.specializedComponentIdeal modelIndex liftedParameter ≤
      Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I)
  denominator_power_clears_componentModel :
    ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I),
      ∃ e : ℕ,
        MvPolynomial.C
            (MvPolynomial.eval liftedParameter
              (models.parameterDenominator modelIndex)) ^ e * f ∈
          models.specializedComponentIdeal modelIndex liftedParameter

/-- Uniform integral-coordinate bound for one fixed finite catalogue.  It is
the maximum over its finitely many model indices and is therefore selected
before the fibre parameter and before epsilon. -/
def RelativeRationalSurfaceComponentModelCatalogue.liftedParameterBound
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (Y : ℕ) : ℕ :=
  Finset.univ.sup fun model : Fin models.modelCount ↦
    monicIntegralParameterRelationSpecializationBound
      (models.parameterRelationCoefficient model) Y

/-- A single power exponent absorbing the auxiliary-coordinate bounds of
all models.  This finite supremum is fixed with the catalogue, before any
specialization and before epsilon. -/
def RelativeRationalSurfaceComponentModelCatalogue.liftedParameterHeightExponent
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (baseCoordinateExponent : ℕ) : ℕ :=
  Finset.univ.sup fun model : Fin models.modelCount ↦
    monicIntegralParameterRelationHeightExponent
      (models.parameterRelationCoefficient model) baseCoordinateExponent

theorem RelativeRationalSurfaceComponentModelCatalogue.liftedParameterBound_cast_le_heightPower
    {M N Y baseCoordinateExponent : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (H : NNReal) (hH : 2 ≤ H)
    (hY : (Y : ℝ) ≤ (H : ℝ) ^ baseCoordinateExponent) :
    (models.liftedParameterBound Y : NNReal) ≤
      H ^ models.liftedParameterHeightExponent baseCoordinateExponent := by
  unfold RelativeRationalSurfaceComponentModelCatalogue.liftedParameterBound
  rw [Nat.cast_finsetSup]
  apply Finset.sup_le
  intro model _hmodel
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_natCast, NNReal.coe_pow]
  refine (monicIntegralParameterRelationSpecializationBound_cast_le_heightPower
    (models.parameterRelationCoefficient model) (H : ℝ)
    (by exact_mod_cast hH) hY).trans ?_
  have honeNN : (1 : NNReal) ≤ H :=
    (by norm_num : (1 : NNReal) ≤ 2).trans hH
  apply pow_le_pow_right₀
    (show (1 : ℝ) ≤ (H : ℝ) by exact_mod_cast honeNN)
  exact Finset.le_sup (s := Finset.univ)
    (f := fun model : Fin models.modelCount ↦
      monicIntegralParameterRelationHeightExponent
        (models.parameterRelationCoefficient model) baseCoordinateExponent)
    (Finset.mem_univ model)

theorem RelativeRationalSurfaceComponentModelWitness.liftedParameter_natAbs_le
    {M N Y : ℕ}
    {models : RelativeRationalSurfaceComponentModelCatalogue M N}
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (w : RelativeRationalSurfaceComponentModelWitness
      models baseParameter I)
    (hbase : ∀ j, (baseParameter j).natAbs ≤ Y) (j : Fin models.liftedParameterCount) :
    (w.liftedParameter j).natAbs ≤ models.liftedParameterBound Y := by
  refine (specializedMonicIntegralParameterRelation_root_natAbs_le
    (models.parameterRelationCoefficient w.modelIndex)
    baseParameter hbase j (w.liftedParameter j)
    (w.liftedParameter_relation j)).trans ?_
  exact Finset.le_sup (s := Finset.univ)
    (f := fun model : Fin models.modelCount ↦
      monicIntegralParameterRelationSpecializationBound
        (models.parameterRelationCoefficient model) Y)
    (Finset.mem_univ w.modelIndex)

/-- The rational finite-cover coordinate represented by a scaled integral
coordinate and the fixed base denominator. -/
def RelativeRationalSurfaceComponentModelWitness.rationalLiftCoordinate
    {M N : ℕ}
    {models : RelativeRationalSurfaceComponentModelCatalogue M N}
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (w : RelativeRationalSurfaceComponentModelWitness
      models baseParameter I)
    (j : Fin models.liftedParameterCount) : ℚ :=
  (w.liftedParameter j : ℚ) /
    (MvPolynomial.eval baseParameter
      (models.coverCoordinateDenominator w.modelIndex) : ℚ)

/-- Fixed-polynomial evaluation bound for the common denominators of all
models in a catalogue. -/
def RelativeRationalSurfaceComponentModelCatalogue.coverDenominatorBound
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (Y : ℕ) : ℕ :=
  finiteIntegralPolynomialSupportBound models.coverCoordinateDenominator *
    finiteIntegralPolynomialCoefficientBound models.coverCoordinateDenominator *
    max 1 Y ^
      finiteIntegralPolynomialDegreeBound models.coverCoordinateDenominator

/-- Both numerator and denominator of the reduced rational auxiliary
coordinate are bounded by a fixed polynomial in the base height. -/
theorem RelativeRationalSurfaceComponentModelWitness.rationalLiftCoordinate_height_le
    {M N Y : ℕ}
    {models : RelativeRationalSurfaceComponentModelCatalogue M N}
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (w : RelativeRationalSurfaceComponentModelWitness
      models baseParameter I)
    (hbase : ∀ j, (baseParameter j).natAbs ≤ Y)
    (j : Fin models.liftedParameterCount) :
    rationalCoefficientHeight (w.rationalLiftCoordinate j) ≤
      max (models.liftedParameterBound Y)
        (models.coverDenominatorBound Y) := by
  let d : ℤ := MvPolynomial.eval baseParameter
    (models.coverCoordinateDenominator w.modelIndex)
  have hd : d ≠ 0 := w.coverCoordinateDenominator_nonzero
  have hnum : (w.liftedParameter j).natAbs ≤
      models.liftedParameterBound Y :=
    w.liftedParameter_natAbs_le hbase j
  have hden : d.natAbs ≤ models.coverDenominatorBound Y := by
    exact finiteIntegralPolynomialFamily_eval_natAbs_le
      models.coverCoordinateDenominator baseParameter hbase w.modelIndex
  change rationalCoefficientHeight
      ((w.liftedParameter j : ℚ) / (d : ℚ)) ≤ _
  refine (rationalCoefficientHeight_int_div_int_le
    (w.liftedParameter j) d hd).trans ?_
  exact max_le
    (hnum.trans (Nat.le_max_left _ _))
    (hden.trans (Nat.le_max_right _ _))

/-- Exact component-model coverage for a fixed projective relative family.
There is no point quantifier: smooth local equations are deliberately a
separate step. -/
def RelativeRationalSurfaceComponentModelCatalogue.CoversPrimeSurfaces
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (fibreEquations :
      (Fin M → ℤ) → Finset (MvPolynomial (Fin (N + 1)) ℚ)) : Prop :=
  ∀ (baseParameter : Fin M → ℤ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I ∈ finiteMinimalPrimes
      (finiteEquationIdeal (fibreEquations baseParameter)) →
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
    (∃ d : ℕ, HasProjectiveDimensionDegree I 2 d) →
      Nonempty
        (RelativeRationalSurfaceComponentModelWitness
          models baseParameter I)

namespace StandardAG

/-- **Finite-etale spreading of rational component unions.**

For each fixed integral relative projective family, finitely many enlarged
parameter models represent every rational prime surface component of every
integral fibre, with exact denominator-localized integral ideals.  This is
the component/descent statement only; it asserts neither smooth charts nor
arithmetic height bounds. -/
def FiniteEtaleRationalPrimeComponentUnionSpreading : Prop :=
  ∀ (M N : ℕ)
    (family : Finset (RelativeIntegralAffinePolynomial M (N + 1)))
    (fibreEquations :
      (Fin M → ℤ) → Finset (MvPolynomial (Fin (N + 1)) ℚ)),
    2 ≤ N →
    (∀ parameter, fibreEquations parameter =
      (family.image
        (specializeRelativeIntegralAffinePolynomial parameter)).image
          (MvPolynomial.map (Int.castRingHom ℚ))) →
      ∃ models : RelativeRationalSurfaceComponentModelCatalogue M N,
        models.CoversPrimeSurfaces fibreEquations

end StandardAG

end

end TranslatedDepthSeven
