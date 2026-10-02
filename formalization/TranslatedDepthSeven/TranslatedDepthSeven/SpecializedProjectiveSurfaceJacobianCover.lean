import TranslatedDepthSeven.GenericComponentJacobianChartSpreading
import TranslatedDepthSeven.FiniteRationalSmoothJacobianMenu
import TranslatedDepthSeven.FinitePrincipalOpenMultiplicityMenu
import TranslatedDepthSeven.PrimeAffineDimensionTranscendence
import TranslatedDepthSeven.ProjectiveAffineChartBridge
import TranslatedDepthSeven.RankSevenSourceSectionComponents
import TranslatedDepthSeven.RankSevenPersistentSurfaceSmoothDevissage

/-!
# Finite integral Jacobian charts for one specialized projective surface

This file is the fixed-fibre adapter between the generic component
calculation and the persistent multiplicity-one construction.  It uses two
standard textbook facts, stated below as general propositions rather than as
application-specific conclusions:

* the standard affine chart of an integral projective variety which meets
  that chart has the same dimension as the projective variety; and
* at a smooth rational point of an equidimensional affine variety, the
  residual module of differentials has the dimension of the variety.

Everything else is proved for literal polynomial ideals.  Starting with the
contracted integral affine ideal of a rational projective surface, we choose
a finite integral generating family.  The generic-point conormal theorem
gives one distinguished dense Jacobian chart.  Independently, the finitely
many row and column choices from the same generating family, together with
finite colon-ideal menus, cover every smooth integral point.  At every
covered point the output includes the exact local ideal equality, a nonzero
ordinary Jacobian determinant, and the resulting Hilbert--Samuel
multiplicity-one certificate in every residue characteristic avoiding one
explicit integer.

No point-counting theorem, auxiliary-form estimate, line contribution, or
branch estimate occurs here.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000

namespace StandardAG

/-- The standard affine chart of a homogeneous prime which meets `X₀ ≠ 0`
has the projective dimension of the original variety.

This is the dimension part of the usual projective--affine chart
correspondence.  It follows by identifying the affine chart with the
degree-zero part of the localization at `X₀`; see Hartshorne, Chapter I,
Sections 2 and 7, or the Stacks Project, Tags `01M3` and `00P0`. -/
def ProjectivePrimeAffineChartKrullDimension : Prop :=
  ∀ (N r d : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
    HasProjectiveDimensionDegree I r d →
      ringKrullDim
          (MvPolynomial (Fin N) ℚ ⧸
            Ideal.map rationalDehomogenizeAtZeroHom I) = r

/-- At a smooth rational point of an equidimensional affine variety, the
dimension of the residual module of Kaehler differentials is the dimension
of the variety.

This is the standard equality between relative dimension, the dimension of
the Zariski tangent space, and the rank of differentials at a smooth point;
see the Stacks Project, Lemmas `00TQ`, `00TS`, and `00TT`.  The statement is
kept in the exact local-ring form consumed by the conormal calculation. -/
def SmoothAffinePointDifferentialDimension : Prop :=
  ∀ (N s d : ℕ) (J : Ideal (MvPolynomial (Fin N) ℚ)),
    HasAffineDimensionDegree J s d →
    ∀ (z : Fin N → ℚ)
      (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom),
      IsSmoothAffineIdealRationalPoint J z →
        Module.finrank
          (IsLocalRing.ResidueField
            (AffineQuotientRationalPointLocalRing J z hJ))
          (IsLocalRing.ResidueField
              (AffineQuotientRationalPointLocalRing J z hJ) ⊗[
            AffineQuotientRationalPointLocalRing J z hJ]
              KaehlerDifferential ℚ
                (AffineQuotientRationalPointLocalRing J z hJ)) = s

end StandardAG

/-- A row choice from a fixed finite integral generating family. -/
abbrev IntegralSurfaceJacobianRows (N generatorCount : ℕ) :=
  Fin (N - 2) → Fin generatorCount

/-- A choice of distinct affine coordinate columns for a surface Jacobian
minor. -/
abbrev IntegralSurfaceJacobianColumns (N : ℕ) :=
  {cols : Fin (N - 2) → Fin N // Function.Injective cols}

/-- Literal fixed-fibre data for one rational projective surface.

The row and column types are finite.  For each pair, `menuCount` and `menu`
give a finite colon-ideal menu.  The final field states that these finitely
many choices cover every smooth integral point of the affine chart and
records the exact local equality and multiplicity-one certificate there.
The distinguished `generic*` fields are obtained at the generic point and
exhibit one nonempty dense principal chart; they are not used to disguise a
claim that this single chart covers the whole smooth locus. -/
structure SpecializedProjectiveSurfaceJacobianCover
    (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) where
  degree : ℕ
  projectiveDimensionDegree : HasProjectiveDimensionDegree I 2 degree
  affineDimensionDegree : HasAffineDimensionDegree
    (Ideal.map rationalDehomogenizeAtZeroHom I) 2 degree
  generatorCount : ℕ
  integralGenerator : Fin generatorCount → MvPolynomial (Fin N) ℤ
  integralGeneratorIdeal_eq :
    Ideal.span (Set.range integralGenerator) =
      Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I)
  genericRows : IntegralSurfaceJacobianRows N generatorCount
  genericRows_injective : Function.Injective genericRows
  genericColumns : IntegralSurfaceJacobianColumns N
  genericChart : MvPolynomial (Fin N) ℤ
  genericDenominator : ℤ
  genericDenominator_ne_zero : genericDenominator ≠ 0
  genericChart_not_mem :
    genericChart ∉
      (Ideal.map rationalDehomogenizeAtZeroHom I).comap
        (MvPolynomial.map (Int.castRingHom ℚ))
  genericJacobian_not_mem :
    selectedJacobianDeterminant
        (fun i ↦ integralGenerator (genericRows i)) genericColumns.1 ∉
      (Ideal.map rationalDehomogenizeAtZeroHom I).comap
        (MvPolynomial.map (Int.castRingHom ℚ))
  genericJacobian_dvd_chart :
    selectedJacobianDeterminant
        (fun i ↦ integralGenerator (genericRows i)) genericColumns.1 ∣
      genericChart
  genericClearing :
    ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I),
      MvPolynomial.C genericDenominator * genericChart * f ∈
        Ideal.span (Set.range fun i ↦ integralGenerator (genericRows i))
  menuCount : IntegralSurfaceJacobianRows N generatorCount →
    IntegralSurfaceJacobianColumns N → ℕ
  menu : ∀ rows cols, Fin (menuCount rows cols) →
    MvPolynomial (Fin N) ℤ
  menuClearing : ∀ rows cols mark,
    ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I),
      menu rows cols mark * f ∈
        Ideal.span (Set.range fun i ↦ integralGenerator (rows i))
  smoothIntegralPointCover :
    ∀ z : Fin N → ℤ,
      IsSmoothAffineIdealRationalPoint
          (Ideal.map rationalDehomogenizeAtZeroHom I)
          (fun i ↦ (z i : ℚ)) →
        ∃ rows : IntegralSurfaceJacobianRows N generatorCount,
        ∃ cols : IntegralSurfaceJacobianColumns N,
        ∃ mark : Fin (menuCount rows cols),
          Function.Injective rows ∧
          MvPolynomial.eval z (menu rows cols mark) ≠ 0 ∧
          MvPolynomial.eval z
              (selectedJacobianDeterminant
                (fun i ↦ integralGenerator (rows i)) cols.1) ≠ 0 ∧
          Ideal.map
              (algebraMap (MvPolynomial (Fin N) ℚ)
                (Localization.AtPrime
                  (RingHom.ker
                    (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
              (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
                (Ideal.span
                  (Set.range fun i ↦ integralGenerator (rows i)))) =
            Ideal.map
              (algebraMap (MvPolynomial (Fin N) ℚ)
                (Localization.AtPrime
                  (RingHom.ker
                    (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
              (Ideal.map rationalDehomogenizeAtZeroHom I) ∧
          let Δ : ℤ := integralSelectedJacobianChartCertificate
            (fun i ↦ integralGenerator (rows i)) cols.1
            (menu rows cols mark) z
          Δ ≠ 0 ∧
            ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
              HasHilbertSamuelMultiplicityAt hp
                (projectiveSpecialFiberIdeal I)
                (fun j ↦ (integralAffineProjectivePoint z j : ZMod p)) 2 1

/-- Every displayed finite chart uses equations lying in the actual
contracted integral affine component ideal. -/
theorem SpecializedProjectiveSurfaceJacobianCover.equationIdeal_le
    {N : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (data : SpecializedProjectiveSurfaceJacobianCover N I)
    (rows : IntegralSurfaceJacobianRows N data.generatorCount) :
    Ideal.span (Set.range fun i ↦ data.integralGenerator (rows i)) ≤
      Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I) := by
  rw [← data.integralGeneratorIdeal_eq]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Ideal.subset_span (Set.mem_range_self (rows i))

/-- The literal finite type indexing a row choice, an injective column
choice, and one member of the corresponding colon-ideal menu. -/
abbrev SpecializedProjectiveSurfaceJacobianCover.MarkedChartIndex
    {N : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (data : SpecializedProjectiveSurfaceJacobianCover N I) :=
  Σ rows : IntegralSurfaceJacobianRows N data.generatorCount,
    Σ cols : IntegralSurfaceJacobianColumns N,
      Fin (data.menuCount rows cols)

/-- Integral local equations attached to one marked finite chart. -/
def SpecializedProjectiveSurfaceJacobianCover.markedEquations
    {N : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (data : SpecializedProjectiveSurfaceJacobianCover N I)
    (c : data.MarkedChartIndex) :
    Fin (N - 2) → MvPolynomial (Fin N) ℤ :=
  fun i ↦ data.integralGenerator (c.1 i)

/-- Injective coordinate columns attached to one marked finite chart. -/
def SpecializedProjectiveSurfaceJacobianCover.markedSelectedVar
    {N : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (data : SpecializedProjectiveSurfaceJacobianCover N I)
    (c : data.MarkedChartIndex) : Fin (N - 2) → Fin N :=
  c.2.1.1

/-- The principal-open clearing polynomial attached to one marked finite
chart. -/
def SpecializedProjectiveSurfaceJacobianCover.markedClearing
    {N : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (data : SpecializedProjectiveSurfaceJacobianCover N I)
    (c : data.MarkedChartIndex) : MvPolynomial (Fin N) ℤ :=
  data.menu c.1 c.2.1 c.2.2

/-- The coordinate columns in every marked chart are distinct. -/
theorem SpecializedProjectiveSurfaceJacobianCover.markedSelectedVar_injective
    {N : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (data : SpecializedProjectiveSurfaceJacobianCover N I)
    (c : data.MarkedChartIndex) :
    Function.Injective (data.markedSelectedVar c) :=
  c.2.1.2

/-- The displayed principal-open polynomial clears the actual contracted
integral component ideal into the displayed local-equation ideal. -/
theorem SpecializedProjectiveSurfaceJacobianCover.markedClearing_mul_mem
    {N : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (data : SpecializedProjectiveSurfaceJacobianCover N I)
    (c : data.MarkedChartIndex) :
    ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I),
      data.markedClearing c * f ∈
        Ideal.span (Set.range (data.markedEquations c)) := by
  intro f hf
  exact data.menuClearing c.1 c.2.1 c.2.2 f hf

/-- The marked chart index really is finite; no point-dependent family of
polynomials is hidden in the construction. -/
noncomputable instance SpecializedProjectiveSurfaceJacobianCover.instFintypeMarkedChartIndex
    {N : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (data : SpecializedProjectiveSurfaceJacobianCover N I) :
    Fintype data.MarkedChartIndex := inferInstance

/-- Every smooth integral point is covered by one member of the literal
finite marked chart type.  The conclusion is written in the precise form
needed by the persistent multiplicity-one construction: containment in the
contracted integral component, equality in the rational local ring,
nonvanishing of both factors of the certificate, and factorwise
multiplicity one away from that certificate. -/
theorem SpecializedProjectiveSurfaceJacobianCover.exists_markedChart_of_smoothIntegralPoint
    {N : ℕ} {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (data : SpecializedProjectiveSurfaceJacobianCover N I)
    (z : Fin N → ℤ)
    (hz : IsSmoothAffineIdealRationalPoint
      (Ideal.map rationalDehomogenizeAtZeroHom I)
      (fun i ↦ (z i : ℚ))) :
    ∃ c : data.MarkedChartIndex,
      Function.Injective (data.markedSelectedVar c) ∧
      Ideal.span (Set.range (data.markedEquations c)) ≤
        Ideal.map integralDehomogenizeAtZeroHom
          (projectiveIntegralClosureIdeal I) ∧
      MvPolynomial.eval z (data.markedClearing c) ≠ 0 ∧
      MvPolynomial.eval z
          (selectedJacobianDeterminant
            (data.markedEquations c) (data.markedSelectedVar c)) ≠ 0 ∧
      Ideal.map
          (algebraMap (MvPolynomial (Fin N) ℚ)
            (Localization.AtPrime
              (RingHom.ker
                (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
          (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
            (Ideal.span (Set.range (data.markedEquations c)))) =
        Ideal.map
          (algebraMap (MvPolynomial (Fin N) ℚ)
            (Localization.AtPrime
              (RingHom.ker
                (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
          (Ideal.map rationalDehomogenizeAtZeroHom I) ∧
      let Δ : ℤ := integralSelectedJacobianChartCertificate
        (data.markedEquations c) (data.markedSelectedVar c)
        (data.markedClearing c) z
      Δ ≠ 0 ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
          HasHilbertSamuelMultiplicityAt hp
            (projectiveSpecialFiberIdeal I)
            (fun j ↦ (integralAffineProjectivePoint z j : ZMod p)) 2 1 := by
  obtain ⟨rows, cols, mark, _hrows, hclearing, hminor, hlocal, hcertificate⟩ :=
    data.smoothIntegralPointCover z hz
  let c : data.MarkedChartIndex := ⟨rows, cols, mark⟩
  refine ⟨c, cols.2, data.equationIdeal_le rows, ?_, ?_, ?_, ?_⟩
  · simpa only [c, SpecializedProjectiveSurfaceJacobianCover.markedClearing]
      using hclearing
  · simpa only [c, SpecializedProjectiveSurfaceJacobianCover.markedEquations,
      SpecializedProjectiveSurfaceJacobianCover.markedSelectedVar]
      using hminor
  · simpa only [c, SpecializedProjectiveSurfaceJacobianCover.markedEquations]
      using hlocal
  · simpa only [c, SpecializedProjectiveSurfaceJacobianCover.markedEquations,
      SpecializedProjectiveSurfaceJacobianCover.markedSelectedVar,
      SpecializedProjectiveSurfaceJacobianCover.markedClearing]
      using hcertificate

/-- Construction of the complete finite chart data for one projective
surface.  The two arguments in `StandardAG` are precisely the standard
textbook inputs; all ideal generation, denominator clearing, generic
Jacobian selection, finiteness of the chart menu, and specialization
certificates are kernel-proved below. -/
theorem exists_specializedProjectiveSurfaceJacobianCover
    (hAffineDimension : StandardAG.ProjectivePrimeAffineChartKrullDimension)
    (hSmoothDimension : StandardAG.SmoothAffinePointDifferentialDimension)
    {N d : ℕ} (hN : 2 ≤ N)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hXzero : MvPolynomial.X (0 : Fin (N + 1)) ∉ I)
    (hprojective : HasProjectiveDimensionDegree I 2 d) :
    Nonempty (SpecializedProjectiveSurfaceJacobianCover N I) := by
  classical
  let Q : Ideal (MvPolynomial (Fin N) ℚ) :=
    Ideal.map rationalDehomogenizeAtZeroHom I
  let K : Ideal (MvPolynomial (Fin N) ℤ) :=
    Ideal.map integralDehomogenizeAtZeroHom
      (projectiveIntegralClosureIdeal I)
  have hQprime : Q.IsPrime := by
    exact rationalStandardAffineChart_isPrime I hIhomogeneous hIprime hXzero
  letI : Q.IsPrime := hQprime
  have hQHilbert : HasAffineHilbertDimensionDegree Q 2 d := by
    exact hasAffineHilbertDimensionDegree_rationalStandardAffineChart
      I hIhomogeneous hIprime hXzero hprojective
  have hQdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ Q) = 2 := by
    simpa only [Q] using
      hAffineDimension N 2 d I hIprime hIhomogeneous hXzero hprojective
  have hQdimensionDegree : HasAffineDimensionDegree Q 2 d :=
    ⟨hQprime, hQdim, hQHilbert.2⟩
  have hKfg : K.FG := IsNoetherian.noetherian K
  obtain ⟨generatorCount, integralGenerator, hgeneratorSubmodule⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hKfg
  have hgeneratorIdeal :
      Ideal.span (Set.range integralGenerator) = K := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change integralGenerator i ∈
        (K : Submodule (MvPolynomial (Fin N) ℤ)
          (MvPolynomial (Fin N) ℤ))
      rw [← hgeneratorSubmodule]
      exact Submodule.subset_span (Set.mem_range_self i)
    · intro f hf
      change f ∈ Submodule.span (MvPolynomial (Fin N) ℤ)
        (Set.range integralGenerator)
      rw [hgeneratorSubmodule]
      exact hf
  let integralToRational : MvPolynomial (Fin N) ℤ →+*
      MvPolynomial (Fin N) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  let rationalGenerator : Fin generatorCount →
      MvPolynomial (Fin N) ℚ := fun i ↦
    integralToRational (integralGenerator i)
  have hmapK : Ideal.map integralToRational K = Q := by
    simpa only [integralToRational, K, Q] using
      map_integralAffineChart_projectiveIntegralClosureIdeal I
  have hrationalGenerator :
      Ideal.span (Set.range rationalGenerator) = Q := by
    rw [← hmapK, ← hgeneratorIdeal, Ideal.map_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  have htrdeg : Algebra.trdeg ℚ
      (MvPolynomial (Fin N) ℚ ⧸ Q) = (2 : Cardinal) :=
    trdeg_eq_nat_of_primeAffine_ringKrullDim_eq ℚ Q hQprime hQdim
  obtain ⟨normalization, hnormalization, hnormalizationFinite⟩ :=
    exists_finite_injective_normalization_of_primeAffine_of_trdeg_eq
      Q htrdeg
  obtain ⟨genericRows, genericCols, genericChart, genericDenominator,
      hgenericRows, hgenericCols, hgenericDenominator,
      hgenericChart, hgenericJacobian, hgenericDvd,
      hgenericClear, _hgenericAway⟩ :=
    exists_baseOpen_genericPrime_selectedJacobianChart
      Q integralGenerator
      (by simpa only [rationalGenerator, integralToRational] using
        hrationalGenerator)
      normalization hnormalization hnormalizationFinite
  let genericColumns : IntegralSurfaceJacobianColumns N :=
    ⟨genericCols, hgenericCols⟩
  have hgenericClearK : ∀ f ∈ K,
      MvPolynomial.C genericDenominator * genericChart * f ∈
        Ideal.span
          (Set.range fun i ↦ integralGenerator (genericRows i)) := by
    intro f hf
    apply hgenericClear f
    change integralToRational f ∈ Q
    have hfmap : integralToRational f ∈ Ideal.map integralToRational K :=
      Ideal.mem_map_of_mem integralToRational hf
    simpa only [hmapK] using hfmap
  have hchartMenu : ∀
      (rows : IntegralSurfaceJacobianRows N generatorCount)
      (cols : IntegralSurfaceJacobianColumns N),
      ∃ menuCount : ℕ,
      ∃ menu : Fin menuCount → MvPolynomial (Fin N) ℤ,
        (∀ mark, ∀ f ∈ K,
          menu mark * f ∈ Ideal.span
            (Set.range fun i ↦ integralGenerator (rows i))) ∧
        ∀ z : Fin N → ℤ,
          (∀ f ∈ Q,
            MvPolynomial.eval (fun i ↦ (z i : ℚ)) f = 0) →
          (Ideal.map
              (algebraMap (MvPolynomial (Fin N) ℚ)
                (Localization.AtPrime
                  (RingHom.ker
                    (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
              (Ideal.map integralToRational
                (Ideal.span
                  (Set.range fun i ↦ integralGenerator (rows i)))) =
            Ideal.map
              (algebraMap (MvPolynomial (Fin N) ℚ)
                (Localization.AtPrime
                  (RingHom.ker
                    (MvPolynomial.eval (fun i ↦ (z i : ℚ)))))) Q) →
          MvPolynomial.eval z
              (selectedJacobianDeterminant
                (fun i ↦ integralGenerator (rows i)) cols.1) ≠ 0 →
          ∃ mark : Fin menuCount,
            MvPolynomial.eval z (menu mark) ≠ 0 ∧
            let Δ : ℤ := integralSelectedJacobianChartCertificate
              (fun i ↦ integralGenerator (rows i)) cols.1
              (menu mark) z
            Δ ≠ 0 ∧
              (∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
                HasHilbertSamuelMultiplicityAt hp
                  (projectiveSpecialFiberIdeal I)
                  (fun j ↦
                    (integralAffineProjectivePoint z j : ZMod p)) 2 1) := by
    intro rows cols
    have hIJ : Ideal.span
        (Set.range fun i ↦ integralGenerator (rows i)) ≤ K := by
      rw [← hgeneratorIdeal]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span (Set.mem_range_self (rows i))
    obtain ⟨menuCount, menu, hmenuClear, hmenuCover⟩ :=
      exists_finite_projectiveSurface_multiplicityOne_menu
        hN I (fun i ↦ integralGenerator (rows i)) cols.1 cols.2
        (by simpa only [K] using hIJ)
    refine ⟨menuCount, menu, ?_, ?_⟩
    · intro mark f hf
      exact hmenuClear mark f (by simpa only [K] using hf)
    · intro z hpoint hlocal hminor
      obtain ⟨mark, hmark, hDelta, hmultiplicity, _hheight⟩ :=
        hmenuCover z
          (by simpa only [Q] using hpoint)
          (by simpa only [Q, integralToRational] using hlocal)
          hminor
      exact ⟨mark, hmark, hDelta, hmultiplicity⟩
  choose menuCount menu hmenuClear hmenuCover using hchartMenu
  have hsmoothCover : ∀ z : Fin N → ℤ,
      IsSmoothAffineIdealRationalPoint Q (fun i ↦ (z i : ℚ)) →
        ∃ rows : IntegralSurfaceJacobianRows N generatorCount,
        ∃ cols : IntegralSurfaceJacobianColumns N,
        ∃ mark : Fin (menuCount rows cols),
          Function.Injective rows ∧
          MvPolynomial.eval z (menu rows cols mark) ≠ 0 ∧
          MvPolynomial.eval z
              (selectedJacobianDeterminant
                (fun i ↦ integralGenerator (rows i)) cols.1) ≠ 0 ∧
          Ideal.map
              (algebraMap (MvPolynomial (Fin N) ℚ)
                (Localization.AtPrime
                  (RingHom.ker
                    (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
              (Ideal.map integralToRational
                (Ideal.span
                  (Set.range fun i ↦ integralGenerator (rows i)))) =
            Ideal.map
              (algebraMap (MvPolynomial (Fin N) ℚ)
                (Localization.AtPrime
                  (RingHom.ker
                    (MvPolynomial.eval (fun i ↦ (z i : ℚ)))))) Q ∧
          let Δ : ℤ := integralSelectedJacobianChartCertificate
            (fun i ↦ integralGenerator (rows i)) cols.1
            (menu rows cols mark) z
          Δ ≠ 0 ∧
            ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
              HasHilbertSamuelMultiplicityAt hp
                (projectiveSpecialFiberIdeal I)
                (fun j ↦ (integralAffineProjectivePoint z j : ZMod p)) 2 1 := by
    intro z hsmooth
    have hsmooth' := hsmooth
    obtain ⟨hz, hsmoothAt⟩ := hsmooth
    let zQ : Fin N → ℚ := fun i ↦ (z i : ℚ)
    let hzIdeal : Q ≤ RingHom.ker (MvPolynomial.aeval zQ).toRingHom :=
      (mem_affineIdealZeroLocus_iff_le_ker_aeval Q zQ).mp hz
    letI : Algebra.FormallySmooth ℚ
        (AffineQuotientRationalPointLocalRing Q zQ hzIdeal) := by
      change Algebra.FormallySmooth ℚ
        (Localization.AtPrime
          (RingHom.ker
            (affineQuotientRationalPoint Q zQ hzIdeal).toRingHom))
      simpa only [affineIdealRationalPointPrime, hzIdeal, zQ] using hsmoothAt
    have htarget :=
      hSmoothDimension N 2 d Q hQdimensionDegree zQ hzIdeal hsmooth'
    obtain ⟨rows, cols, hrows, hcols, hminorQ, hlocalQ⟩ :=
      exists_selected_affineIdeal_generators_and_literal_minor
        Q zQ hzIdeal htarget rationalGenerator hrationalGenerator
    let colsData : IntegralSurfaceJacobianColumns N := ⟨cols, hcols⟩
    have hminorZ : MvPolynomial.eval z
        (selectedJacobianDeterminant
          (fun i ↦ integralGenerator (rows i)) cols) ≠ 0 := by
      intro hzero
      apply hminorQ
      rw [← map_selectedJacobianDeterminant
        (Int.castRingHom ℚ)
        (fun i ↦ integralGenerator (rows i)) cols]
      rw [eval_map_intCast, hzero, Int.cast_zero]
    have hlocal :
        Ideal.map
            (algebraMap (MvPolynomial (Fin N) ℚ)
              (Localization.AtPrime
                (RingHom.ker (MvPolynomial.eval zQ))))
            (Ideal.map integralToRational
              (Ideal.span
                (Set.range fun i ↦ integralGenerator (rows i)))) =
          Ideal.map
            (algebraMap (MvPolynomial (Fin N) ℚ)
              (Localization.AtPrime
                (RingHom.ker (MvPolynomial.eval zQ)))) Q := by
      rw [affineQuotientLocalExtension_ker] at hlocalQ
      simpa only [integralToRational, rationalGenerator,
        affineEvaluationPrime, MvPolynomial.aeval_def,
        Ideal.map_span, Ideal.map_map, RingHom.coe_comp,
        Function.comp_apply, ← Set.range_comp] using hlocalQ
    obtain ⟨mark, hmark, hcertificate⟩ :=
      hmenuCover rows colsData z
        (by simpa only [zQ] using hz)
        (by simpa only [zQ] using hlocal) hminorZ
    exact ⟨rows, colsData, mark, hrows, hmark, hminorZ,
      by simpa only [zQ] using hlocal, hcertificate⟩
  exact ⟨{
    degree := d
    projectiveDimensionDegree := hprojective
    affineDimensionDegree := by
      simpa only [Q] using hQdimensionDegree
    generatorCount := generatorCount
    integralGenerator := integralGenerator
    integralGeneratorIdeal_eq := by simpa only [K] using hgeneratorIdeal
    genericRows := genericRows
    genericRows_injective := hgenericRows
    genericColumns := genericColumns
    genericChart := genericChart
    genericDenominator := genericDenominator
    genericDenominator_ne_zero := hgenericDenominator
    genericChart_not_mem := by simpa only [Q, integralToRational] using hgenericChart
    genericJacobian_not_mem := by
      simpa only [Q, integralToRational, genericColumns] using hgenericJacobian
    genericJacobian_dvd_chart := by
      simpa only [genericColumns] using hgenericDvd
    genericClearing := by simpa only [K] using hgenericClearK
    menuCount := menuCount
    menu := menu
    menuClearing := by
      intro rows cols mark f hf
      exact hmenuClear rows cols mark f (by simpa only [K] using hf)
    smoothIntegralPointCover := by
      intro z hz
      simpa only [Q] using hsmoothCover z (by simpa only [Q] using hz)
  }⟩

/-- Source-section specialization of the preceding theorem.  Membership in
the literal minimal-prime list supplies primality, and homogeneity descends
from the displayed homogeneous source equations.  The hypothesis `hXzero`
only records that this component meets the standard affine chart; in the
persistent application it is supplied by any point of the corresponding
nonempty record cell. -/
theorem exists_rankSevenSourceSectionSurfaceJacobianCover
    (hAffineDimension : StandardAG.ProjectivePrimeAffineChartKrullDimension)
    (hSmoothDimension : StandardAG.SmoothAffinePointDifferentialDimension)
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A))
    (hXzero : MvPolynomial.X (0 : Fin 14) ∉ I)
    {d : ℕ} (hprojective : HasProjectiveDimensionDegree I 2 d) :
    Nonempty (SpecializedProjectiveSurfaceJacobianCover 13 I) := by
  have hIprime : I.IsPrime := isPrime_of_mem_finiteMinimalPrimes hI
  have hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      (rankSevenSourceSectionIdeal_isHomogeneous
        x₀ hm equations hhomogeneous A)
      ((mem_finiteMinimalPrimes_iff _ _).mp hI)
  exact exists_specializedProjectiveSurfaceJacobianCover
    hAffineDimension hSmoothDimension (by norm_num) I hIprime
      hIhomogeneous hXzero hprojective

end

end TranslatedDepthSeven
