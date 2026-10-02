import CubicTenVariables.FixedLeadingSurfaceSurvivorResidual
import TranslatedDepthSeven.IsolatedVertexQuotientPersistentPila
import TranslatedDepthSeven.GeometricProgressionChangedComponentCount
import TranslatedDepthSeven.QbarPersistentRootComponentCellAggregation
import TranslatedDepthSeven.AffineProjectiveClosureUniquenessInternal
import TranslatedDepthSeven.RealAffineChartDegreeMassInternal
import TranslatedDepthSeven.IsolatedVertexQuotientRelativeSourceSectionFamily
import TranslatedDepthSeven.QuantitativePrefixRationalLineLedger

/-!
# Degree splitting for persistent root curves

This file counts the bounded-degree nonlinear root components directly, before
introducing any terminal auxiliary.  The Galois-stable branch is Pila's curve
bound after descent and residue-class rescaling.  The nonstable branch is the
internally proved intersection bound with a distinct conjugate.

The eventual high-degree branch is deliberately exposed at the numerical
endpoint of Salberger, *Proc. LMS* 126 (2023), Lemma 3.13.  Instantiating that
endpoint requires coefficient-height bounds for the source equation and the
root auxiliary.  The current survivor-auxiliary API records degrees and
properness, but not those heights.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

noncomputable section
namespace CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplit

open MvPolynomial TranslatedDepthSeven Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

local instance persistentRootDegreeSplitPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## A chart-minimality bridge for the rational line ledger -/

/-- Inclusion of standard affine charts reflects inclusion between
homogeneous primes which meet that chart. -/
theorem homogeneousPrime_le_of_map_dehomogenization_le
    {K : Type*} [Field K] {n : ℕ}
    (I J : Ideal (MvPolynomial (Option (Fin n)) K))
    (hIhom : I.IsHomogeneous
      (homogeneousSubmodule (Option (Fin n)) K))
    (hJhom : J.IsHomogeneous
      (homogeneousSubmodule (Option (Fin n)) K))
    (hJprime : J.IsPrime)
    (hJX : X (none : Option (Fin n)) ∉ J)
    (hchart : I.map multivariateDehomogenization.toRingHom ≤
      J.map multivariateDehomogenization.toRingHom) :
    I ≤ J := by
  intro f hf
  rw [← f.sum_homogeneousComponent]
  apply Ideal.sum_mem
  intro k _hk
  let p := homogeneousComponent k f
  have hpHom : p.IsHomogeneous k :=
    homogeneousComponent_isHomogeneous k f
  have hpI : p ∈ I := by
    have h := hIhom k hf
    change (MvPolynomial.decomposition.decompose' f k :
      MvPolynomial (Option (Fin n)) K) ∈ I at h
    simpa only [MvPolynomial.decomposition.decompose'_apply, p] using h
  have hpChart : multivariateDehomogenization p ∈
      J.map multivariateDehomogenization.toRingHom :=
    hchart (Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom hpI)
  have hpDegree :
      (multivariateDehomogenization p).totalDegree ≤ k :=
    (multivariateHomogenization_dehomogenization_of_isHomogeneous
      p hpHom).1
  have hpJ :
      multivariateHomogenization (multivariateDehomogenization p) k ∈ J :=
    (mem_map_dehomogenization_iff_homogenization_mem
      J hJhom hJprime hJX
      (multivariateDehomogenization p) hpDegree).1 hpChart
  rwa [(multivariateHomogenization_dehomogenization_of_isHomogeneous
    p hpHom).2] at hpJ

/-- Consecutive-coordinate form of the preceding order reflection. -/
theorem homogeneousPrime_le_of_map_standardDehomogenization_le
    {K : Type*} [Field K] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hIhom : I.IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) K))
    (hJhom : J.IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) K))
    (hJprime : J.IsPrime)
    (hJX : X (0 : Fin (n + 1)) ∉ J)
    (hchart : I.map (standardDehomogenizationHom K n) ≤
      J.map (standardDehomogenizationHom K n)) :
    I ≤ J := by
  let E := MvPolynomial.renameEquiv K (_root_.finSuccEquiv n)
  let I' := I.map E
  let J' := J.map E
  have hI'hom : I'.IsHomogeneous
      (homogeneousSubmodule (Option (Fin n)) K) :=
    map_renameEquiv_isHomogeneous (_root_.finSuccEquiv n) I hIhom
  obtain ⟨hJ'hom, hJ'prime, hJ'X⟩ :=
    finSuccRename_homogeneousPrime_avoids_none J hJhom hJprime hJX
  have hI'chart :
      I'.map multivariateDehomogenization.toRingHom =
        I.map (standardDehomogenizationHom K n) :=
    map_standardDehomogenizationHom_finSuccRename I
  have hJ'chart :
      J'.map multivariateDehomogenization.toRingHom =
        J.map (standardDehomogenizationHom K n) :=
    map_standardDehomogenizationHom_finSuccRename J
  have hI'J' : I' ≤ J' := by
    apply homogeneousPrime_le_of_map_dehomogenization_le
      I' J' hI'hom hJ'hom hJ'prime hJ'X
    rwa [hI'chart, hJ'chart]
  have hIback : I'.map E.symm = I := Ideal.map_of_equiv E.toRingEquiv
  have hJback : J'.map E.symm = J := Ideal.map_of_equiv E.toRingEquiv
  rw [← hIback, ← hJback]
  exact Ideal.map_mono hI'J'

/-- A projective minimal component which meets the standard chart remains a
minimal component after dehomogenization. -/
theorem map_standardDehomogenization_mem_finiteMinimalPrimes
    {K : Type*} [Field K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJhom : J.IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) K))
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : I ∈ finiteMinimalPrimes J)
    (hIX : X (0 : Fin (n + 1)) ∉ I) :
    I.map (standardDehomogenizationHom K n) ∈
      finiteMinimalPrimes
        (J.map (standardDehomogenizationHom K n)) := by
  classical
  let f := standardDehomogenizationHom K n
  have hIprime : I.IsPrime := isPrime_of_mem_finiteMinimalPrimes hI
  have hIhom : I.IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) K) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
      ((mem_finiteMinimalPrimes_iff J I).mp hI)
  have hAisPrime : (I.map f).IsPrime :=
    standardAffineChart_isPrime I hIhom hIprime hIX
  apply (mem_finiteMinimalPrimes_iff (J.map f) (I.map f)).mpr
  refine ⟨⟨hAisPrime, Ideal.map_mono (le_of_mem_finiteMinimalPrimes hI)⟩, ?_⟩
  intro P hP hPA
  letI : P.IsPrime := hP.1
  obtain ⟨P₀, hP₀, hP₀P⟩ := exists_finiteMinimalPrime_le hP.2
  obtain ⟨R, hR, hRX, hRchart⟩ :=
    exists_minimalConeComponent_of_minimalStandardChartComponent
      J hJhom P₀ hP₀
  have hRprime : R.IsPrime := isPrime_of_mem_finiteMinimalPrimes hR
  have hRhom : R.IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) K) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
      ((mem_finiteMinimalPrimes_iff J R).mp hR)
  have hRI : R ≤ I := by
    apply homogeneousPrime_le_of_map_standardDehomogenization_le
      R I hRhom hIhom hIprime hIX
    rw [hRchart]
    exact hP₀P.trans hPA
  have hIR : I ≤ R :=
    ((mem_finiteMinimalPrimes_iff J I).mp hI).2
      ⟨hRprime, le_of_mem_finiteMinimalPrimes hR⟩ hRI
  have hRIeq : R = I := le_antisymm hRI hIR
  have hP₀A : P₀ = I.map f := by
    rw [← hRchart, hRIeq]
  rw [← hP₀A]
  exact hP₀P

/-- A Galois-stable geometric projective line component descends to an
actual rational degree-one component in the standard affine chart. -/
theorem exists_rationalAffineLine_of_stableQbarProjectiveComponent
    (J : Ideal (MvPolynomial (Fin 4) ℚ))
    (hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ))
    (Q : Ideal (MvPolynomial (Fin 4) Qbar))
    (hQmin : Q ∈
      (J.map (MvPolynomial.map (algebraMap ℚ Qbar))).minimalPrimes)
    (hQhom : Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar))
    (hQprojective : HasProjectiveDimensionDegree Q 1 1)
    (hstable : ∀ g : Qbar ≃ₐ[ℚ] Qbar, conjugateIdeal g Q = Q)
    (hXQ : X (0 : Fin 4) ∉ Q) :
    ∃ I : Ideal (MvPolynomial (Fin 4) ℚ),
      I.map (MvPolynomial.map (algebraMap ℚ Qbar)) = Q ∧
      let A := I.map (standardDehomogenizationHom ℚ 3)
      A ∈ finiteMinimalPrimes
          (J.map (standardDehomogenizationHom ℚ 3)) ∧
        HasAffineHilbertDimensionDegree A 1 1 := by
  classical
  obtain ⟨I, hIhom, hIQ⟩ :=
    rationalHomogeneousIdeal_descent_of_galoisInvariant
      Q hstable hQhom
  have hQprime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQmin
  have hIprime : I.IsPrime :=
    rationalIdeal_isPrime_of_qbarCoefficientExtension_isPrime I (by
      rwa [hIQ])
  have hIprojective : HasProjectiveDimensionDegree I 1 1 :=
    rationalHasProjectiveDimensionDegree_of_qbar_map_eq
      I Q hIQ hQprime hQprojective
  have hIX : X (0 : Fin 4) ∉ I := by
    intro hX
    apply hXQ
    rw [← hIQ]
    have hmapX := Ideal.mem_map_of_mem
      (MvPolynomial.map (algebraMap ℚ Qbar)) hX
    simpa using hmapX
  have hImin : I ∈ finiteMinimalPrimes J :=
    rationalDescent_mem_finiteMinimalPrimes_of_qbarNodeComponent
      J Q I hIQ hQmin
  let A := I.map (standardDehomogenizationHom ℚ 3)
  have hAmin : A ∈ finiteMinimalPrimes
      (J.map (standardDehomogenizationHom ℚ 3)) :=
    map_standardDehomogenization_mem_finiteMinimalPrimes
      J hJhom I hImin hIX
  have hAdegree : HasAffineHilbertDimensionDegree A 1 1 :=
    hasAffineHilbertDimensionDegree_rationalStandardAffineChart
      I hIhom hIprime hIX hIprojective
  exact ⟨I, hIQ, hAmin, hAdegree⟩

/-- Pila for one bounded-degree geometric projective curve in a centered
residue packet, with the honest Galois dichotomy.  The constant is uniform in
the curve coefficients. -/
theorem exists_uniform_qbarProjectiveCurve_centeredPacket_pila
    (hPila : Pila1995TheoremARationalQbarPrime)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ}, 0 < q →
        ∀ (base : IntVector N)
          (Q : Ideal (MvPolynomial (Fin (N + 1)) Qbar))
          (d : ℕ),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) Qbar) →
        HasProjectiveDimensionDegree Q 1 d →
        2 ≤ d → d ≤ D →
        ∀ (S : Finset (IntVector N)),
        base ∈ S →
        (∀ z ∈ S,
          (fun i ↦ ((integralAffineChartVector z i : ℤ) : Qbar)) ∈
            affineIdealZeroLocus Q) →
        (∀ z ∈ S, IntVectorCongruent q z base) →
        ∀ (center : RealVector N) (R : ℝ), 0 ≤ R →
        (∀ z ∈ S, ∀ i, |(z i : ℝ) - center i| ≤ R) →
          (S.card : ℝ) ≤
            (D : ℝ) ^ 2 +
              C * (2 * R / (q : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨C, hC, hstableBound⟩ :=
    exists_uniform_rationalQbarPrime_pilaCurve_halfPower_boundedDegree
      hPila N D ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq base Q d hQprime hQhom hQprojective hd hdD S hbase
    hzero hcong center R hR hbox
  let V : ℝ := 2 * R / (q : ℝ) + 2
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiv : 0 ≤ 2 * R / (q : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hR) hqReal.le
  have hV : 1 < V := by
    dsimp only [V]
    linarith
  rcases conjugateIdeal_fixed_or_exists_distinct Q with hstable | ⟨g, hg⟩
  · obtain ⟨I, hIhom, hIQ⟩ :=
      rationalHomogeneousIdeal_descent_of_galoisInvariant Q hstable hQhom
    have hIprojective : HasProjectiveDimensionDegree I 1 d :=
      rationalHasProjectiveDimensionDegree_of_qbar_map_eq
        I Q hIQ hQprime hQprojective
    have hIQprime :
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
      rwa [hIQ]
    have hIprime : I.IsPrime :=
      rationalIdeal_isPrime_of_qbarCoefficientExtension_isPrime I hIQprime
    have hXQ : X (0 : Fin (N + 1)) ∉ Q := by
      intro hX
      have hzeroX := hzero base hbase (X (0 : Fin (N + 1))) hX
      simpa [integralAffineChartVector] using hzeroX
    have hXI : X (0 : Fin (N + 1)) ∉ I := by
      intro hX
      apply hXQ
      rw [← hIQ]
      have hmapX := Ideal.mem_map_of_mem
        (MvPolynomial.map (algebraMap ℚ Qbar)) hX
      simpa using hmapX
    let A : Ideal (MvPolynomial (Fin N) ℚ) :=
      I.map rationalDehomogenizeAtZeroHom
    have hAprojective : HasAffineHilbertDimensionDegree A 1 d := by
      exact hasAffineHilbertDimensionDegree_rationalStandardAffineChart
        I hIhom hIprime hXI hIprojective
    have hAQbar :
        (A.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
      exact rationalStandardAffineChart_qbarExtension_isPrime
        I Q hIQ hQhom hQprime hXQ
    let A' := A.map (affinePolynomialChangeAlgEquiv
      (fun i ↦ (base i : ℚ)) (q : ℚ)
      (by exact_mod_cast hq.ne'))
    have hA'projective : HasAffineHilbertDimensionDegree A' 1 d := by
      exact (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
        A (fun i ↦ (base i : ℚ)) (q : ℚ)
          (by exact_mod_cast hq.ne') 1 d).2 hAprojective
    have hA'Qbar :
        (A'.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
      exact qbarCoefficientExtension_affinePolynomialChange_isPrime
        A hAQbar (fun i ↦ (base i : ℚ)) (q : ℚ)
          (by exact_mod_cast hq.ne')
    have hinjective : Set.InjOn
        (congruenceDisplacementOrZero q base) (↑S : Set (IntVector N)) := by
      apply (congruenceDisplacementOrZero_injOn base).mono
      intro z hz
      exact hcong z hz
    have himage : ∀ z ∈ S,
        congruenceDisplacementOrZero q base z ∈
          rationalPilaIntegralPoints A' V := by
      intro z hz
      have hzQ := hzero z hz
      have hzI : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
          affineIdealZeroLocus I := by
        apply (rational_zero_of_ideal_iff_qbar_zero_of_extension
          I Q hIQ (fun i ↦ (integralAffineChartVector z i : ℚ))).2
        simpa using hzQ
      have hzA : (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus A := by
        rw [mem_affineIdealZeroLocus_iff]
        change I.map rationalDehomogenizeAtZeroHom ≤
          RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℚ)))
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        rw [Ideal.mem_comap, RingHom.mem_ker]
        rw [← standardDehomogenizationHom_rat_eq_rationalDehomogenizeAtZeroHom,
          eval_standardDehomogenizationHom]
        have hpoint :
            (fun i ↦ (integralAffineChartVector z i : ℚ)) =
              (fun i ↦ Fin.cases (1 : ℚ) (fun j ↦ (z j : ℚ)) i) := by
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;>
            simp [integralAffineChartVector]
        rw [← hpoint]
        exact hzI f hf
      apply intPoint_mem_rationalPilaIntegralPoints_packet
        hq A base (congruenceDisplacementOrZero q base z) V
      · intro i
        have hbound := congruenceDisplacementOrZero_coordinate_bound
          hq base z (hcong z hz) (hbox z hz) (hbox base hbase) i
        dsimp only [V]
        linarith
      · have hreconstruct : integralAffineMap base
            (congruenceDisplacementOrZero q base z) q = z := by
          funext i
          simp only [integralAffineMap]
          exact (congruenceDisplacementOrZero_spec base z (hcong z hz) i).symm
        rwa [hreconstruct]
    have hcard : S.card ≤ (rationalPilaIntegralPoints A' V).card :=
      Finset.card_le_card_of_injOn
        (congruenceDisplacementOrZero q base) himage hinjective
    have hstableCount : (S.card : ℝ) ≤ C * V ^ ((1 / 2 : ℝ) + ε) := by
      calc
        (S.card : ℝ) ≤ ((rationalPilaIntegralPoints A' V).card : ℝ) := by
          exact_mod_cast hcard
        _ ≤ C * V ^ ((1 / 2 : ℝ) + ε) :=
          hstableBound d hd hdD A' hA'Qbar hA'projective V hV
    exact hstableCount.trans (le_add_of_nonneg_left (sq_nonneg (D : ℝ)))
  · have hconjPrime : (conjugateIdeal g Q).IsPrime :=
      conjugateIdeal_isPrime g Q hQprime
    have hconjHom : (conjugateIdeal g Q).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) Qbar) :=
      conjugateIdeal_isHomogeneous g Q hQhom
    have hconjDegree : HasProjectiveDimensionDegree
        (conjugateIdeal g Q) 1 d := hConjugate N 1 d g Q hQprojective
    have hintersection : ∀ z ∈ S,
        (fun i ↦ (progressionHomogeneousPoint (0 : IntVector N) 1 z i : Qbar)) ∈
          affineIdealZeroLocus (Q ⊔ conjugateIdeal g Q) := by
      intro z hz
      rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
      apply sup_le
      · have hQle := hzero z hz
        rw [mem_affineIdealZeroLocus_iff_le_ker_aeval] at hQle
        simpa [progressionHomogeneousPoint, integralAffineChartVector] using hQle
      · have hQle := hzero z hz
        rw [mem_affineIdealZeroLocus_iff_le_ker_aeval] at hQle
        have hgQ := conjugateIdeal_le_rationalEvaluationKernel
          g Q (fun i ↦ (integralAffineChartVector z i : ℚ)) hQle
        simpa [progressionHomogeneousPoint, integralAffineChartVector] using hgQ
    have hcard := card_geometricProgression_on_distinct_curves_le_degree_mul
      (K := Qbar) (N := N) (d := d) (e := d) (m := 1) (by omega)
      Q (conjugateIdeal g Q) hQprime hconjPrime hQhom hconjHom
      hQprojective hconjDegree hg.symm (0 : IntVector N) S hintersection
    have hdegree : (S.card : ℝ) ≤ (D : ℝ) ^ 2 := by
      calc
        (S.card : ℝ) ≤ ((d * d : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (d : ℝ) ^ 2 := by norm_num [pow_two]
        _ ≤ (D : ℝ) ^ 2 := by gcongr
    exact hdegree.trans (le_add_of_nonneg_right
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)))

/-! ## The literal root-degree split -/

/-- Extend the degree function on actual root components to their option
labels.  The value at `none` is immaterial because actual component options
are always `some Q`. -/
def rootOptionDegree
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (o : Option (Ideal (MvPolynomial (Fin 4) Qbar))) : ℕ :=
  match o with
  | none => 0
  | some Q => degree Q

/-- Literal Galois stability of a geometric component over `ℚ`. -/
def IsQbarIdealGaloisStable
    (Q : Ideal (MvPolynomial (Fin 4) Qbar)) : Prop :=
  ∀ g : Qbar ≃ₐ[ℚ] Qbar, conjugateIdeal g Q = Q

/-- The literal union of all active degree-one root cells.  It is retained as
one set, so overlaps between lines are not counted with multiplicity. -/
def persistentRootLinePointUnion
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3)) : Finset (IntVector 3) :=
  active.biUnion fun o ↦
    if rootOptionDegree degree o = 1 then cell o else ∅

/-- Elementary Galois adapter from the geometric root-line union to the
existing rational prefix line ledger.  Stable geometric lines descend to
rational minimal components of the exact root cut.  A nonstable line meets a
distinct conjugate in at most one projective point, so its entire rational
cell contributes at most one point. -/
theorem persistentRootLinePointUnion_card_le_rationalLedger_add_active
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hsourceHom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (G₀ : MvPolynomial (Fin 4) ℚ) {e₀ : ℕ}
    (hG₀hom : G₀.IsHomogeneous e₀)
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (hrootData : ∀ Q ∈ finiteEquationMinimalPrimes
        (qbarSurfaceCutEquationFamily sourceEquations G₀),
      Q.IsPrime ∧
      Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
      HasProjectiveDimensionDegree Q 1 (degree Q))
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (u : IntVector 3) (m : ℕ) (hm : 0 < m) :
    let active := activeQbarPersistentRootComponentOptions
      sourceEquations G₀ cell
    (∀ o ∈ active, ∀ z ∈ cell o,
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations G₀)
        (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) = o) →
    ((persistentRootLinePointUnion degree active cell).card : ℝ) ≤
      ((quantitativePrefixPersistentRationalLinearPointUnion
        (finiteEquationIdeal sourceEquations) active (fun _ ↦ G₀)
          u m cell).card : ℝ) + active.card := by
  classical
  dsimp only
  intro hselected
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  let affineMap : IntVector 3 → IntVector 3 :=
    fun z ↦ integralAffineMap u z m
  let affineCell := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    quantitativePrefixPersistentAffineCell u m cell o
  let lineCell := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    if rootOptionDegree degree o = 1 then affineCell o else ∅
  let J : Ideal (MvPolynomial (Fin 4) ℚ) :=
    finiteEquationIdeal sourceEquations ⊔ Ideal.span ({G₀} : Set _)
  let chart : Ideal (MvPolynomial (Fin 3) ℚ) :=
    rationalAffineChartIntersectionIdeal
      (finiteEquationIdeal sourceEquations) G₀
  let rationalCell := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    finitePointsOnRationalLinearCurveComponents chart (affineCell o)
  let distinguished := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    if rootOptionDegree degree o = 1 then rationalCell o else ∅
  let affineLineUnion := active.biUnion lineCell
  have haffineInjective : Function.Injective affineMap :=
    integralAffineMap_injective hm u
  have himage :
      (persistentRootLinePointUnion degree active cell).image affineMap =
        affineLineUnion := by
    rw [persistentRootLinePointUnion, Finset.biUnion_image]
    dsimp only [affineLineUnion]
    apply Finset.biUnion_congr rfl
    intro o _ho
    by_cases hd : rootOptionDegree degree o = 1
    · simp [lineCell, affineCell, quantitativePrefixPersistentAffineCell, hd,
        affineMap]
    · simp [lineCell, hd]
  have hlineCard :
      (persistentRootLinePointUnion degree active cell).card =
        affineLineUnion.card := by
    rw [← himage]
    exact (Finset.card_image_iff.mpr haffineInjective.injOn).symm
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ) := by
    apply hsourceHom.sup
    apply Ideal.homogeneous_span
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨e₀, hG₀hom⟩
  have hcutIdeal :
      finiteEquationIdeal
          (qbarSurfaceCutEquationFamily sourceEquations G₀) =
        J.map (MvPolynomial.map (algebraMap ℚ Qbar)) := by
    unfold qbarSurfaceCutEquationFamily
    rw [finiteEquationIdeal_union,
      finiteEquationIdeal_qbarSurfaceEquationFamily]
    simp [finiteEquationIdeal, J, Ideal.map_sup, Ideal.map_span]
  have hrationalSubset : ∀ o,
      rationalCell o ⊆ affineCell o := by
    intro o x hx
    dsimp only [rationalCell] at hx
    rw [finitePointsOnRationalLinearCurveComponents] at hx
    obtain ⟨A, _hA, hxA⟩ := Finset.mem_biUnion.mp hx
    split at hxA
    · exact (mem_finitePointsOnRationalAffineIdeal_iff _ _ _).mp hxA |>.1
    · simp at hxA
  have hdistinguished : ∀ o ∈ active, distinguished o ⊆ lineCell o := by
    intro o _ho
    dsimp only [distinguished, lineCell]
    split
    · exact hrationalSubset o
    · exact Finset.Subset.rfl
  have hlocal : ∀ o ∈ active,
      ((lineCell o).card : ℝ) ≤ ((distinguished o).card : ℝ) + 1 := by
    intro o ho
    have hcomponent :=
      (mem_activeQbarPersistentRootComponentOptions_iff
        sourceEquations G₀ cell o).mp ho |>.1
    obtain ⟨Q, hQmin, hQo⟩ :=
      (mem_finiteEquationComponentOptions_iff
        (qbarSurfaceCutEquationFamily sourceEquations G₀) o).mp hcomponent
    subst o
    have hQdata := hrootData Q hQmin
    by_cases hline : degree Q = 1
    · rcases conjugateIdeal_fixed_or_exists_distinct Q with
        hstable | ⟨g, hg⟩
      · have hcellSubset : affineCell (some Q) ⊆ rationalCell (some Q) := by
          intro x hx
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
          have hlabel := hselected (some Q) ho z hz
          have hQpoint :
              (fun i ↦
                (progressionHomogeneousPoint u m z i : Qbar)) ∈
                affineIdealZeroLocus Q :=
            (selectedFiniteEquationComponent_spec
              (qbarSurfaceCutEquationFamily sourceEquations G₀)
              (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar))
              hlabel).2
          have hXQ : X (0 : Fin 4) ∉ Q := by
            intro hX
            have hzeroX := hQpoint (X (0 : Fin 4)) hX
            simpa [progressionHomogeneousPoint] using hzeroX
          have hQminimal : Q ∈
              (J.map (MvPolynomial.map (algebraMap ℚ Qbar))).minimalPrimes := by
            rw [← hcutIdeal]
            exact (mem_finiteMinimalPrimes_iff _ _).mp hQmin
          obtain ⟨I, hIQ, hAmin, hAdegree⟩ :=
            exists_rationalAffineLine_of_stableQbarProjectiveComponent
              J hJhom Q hQminimal hQdata.2.1
                (hline ▸ hQdata.2.2) hstable hXQ
          let A := I.map (standardDehomogenizationHom ℚ 3)
          have hzI :
              (fun i ↦ (progressionHomogeneousPoint u m z i : ℚ)) ∈
                affineIdealZeroLocus I := by
            apply (rational_zero_of_ideal_iff_qbar_zero_of_extension
              I Q hIQ
              (fun i ↦ (progressionHomogeneousPoint u m z i : ℚ))).2
            simpa using hQpoint
          have hxA :
              (fun i ↦ (integralAffineMap u z m i : ℚ)) ∈
                affineIdealZeroLocus A := by
            rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
            change I.map (standardDehomogenizationHom ℚ 3) ≤ _
            rw [Ideal.map_le_iff_le_comap]
            intro F hFI
            rw [Ideal.mem_comap, RingHom.mem_ker]
            change MvPolynomial.eval
              (fun i ↦ (integralAffineMap u z m i : ℚ))
                ((standardDehomogenizationHom ℚ 3) F) = 0
            rw [eval_standardDehomogenizationHom]
            have hpoint :
                (fun i ↦ (progressionHomogeneousPoint u m z i : ℚ)) =
                  (fun i ↦ Fin.cases (1 : ℚ)
                    (fun j ↦ (integralAffineMap u z m j : ℚ)) i) := by
              funext i
              refine Fin.cases ?_ (fun j ↦ ?_) i <;>
                simp [progressionHomogeneousPoint, integralAffineMap]
            rw [← hpoint]
            exact hzI F hFI
          dsimp only [rationalCell]
          rw [finitePointsOnRationalLinearCurveComponents]
          refine Finset.mem_biUnion.mpr ⟨A, ?_, ?_⟩
          · simpa [chart, rationalAffineChartIntersectionIdeal, J] using hAmin
          · have hxfinite : integralAffineMap u z m ∈
                finitePointsOnRationalAffineIdeal (affineCell (some Q)) A :=
              (mem_finitePointsOnRationalAffineIdeal_iff _ _ _).mpr
                ⟨hx, hxA⟩
            have hAdegree' : HasAffineHilbertDimensionDegree A 1 1 :=
              hAdegree
            split
            · exact hxfinite
            · rename_i hnot
              exact (hnot hAdegree').elim
        have hcard := Finset.card_le_card hcellSubset
        have hcardReal : ((affineCell (some Q)).card : ℝ) ≤
            ((rationalCell (some Q)).card : ℝ) + 1 := by
          simpa using
            (Nat.cast_le.mpr (hcard.trans (Nat.le_add_right _ 1)) :
              ((affineCell (some Q)).card : ℝ) ≤
                (((rationalCell (some Q)).card + 1 : ℕ) : ℝ))
        simpa [lineCell, distinguished, rootOptionDegree, hline] using hcardReal
      · have hconjPrime : (conjugateIdeal g Q).IsPrime :=
          conjugateIdeal_isPrime g Q hQdata.1
        have hconjHom : (conjugateIdeal g Q).IsHomogeneous
            (homogeneousSubmodule (Fin 4) Qbar) :=
          conjugateIdeal_isHomogeneous g Q hQdata.2.1
        have hconjDegree : HasProjectiveDimensionDegree
            (conjugateIdeal g Q) 1 1 :=
          hConjugate 3 1 1 g Q (hline ▸ hQdata.2.2)
        have hintersection : ∀ z ∈ cell (some Q),
            (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) ∈
              affineIdealZeroLocus (Q ⊔ conjugateIdeal g Q) := by
          intro z hz
          rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
          have hlabel := hselected (some Q) ho z hz
          have hQpoint :
              (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) ∈
                affineIdealZeroLocus Q :=
            (selectedFiniteEquationComponent_spec
              (qbarSurfaceCutEquationFamily sourceEquations G₀)
              (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar))
              hlabel).2
          have hQzero :=
            (mem_affineIdealZeroLocus_iff_le_ker_aeval Q _).mp hQpoint
          apply sup_le
          · exact hQzero
          · have hc := conjugateIdeal_le_rationalEvaluationKernel g Q
                (fun i ↦ (progressionHomogeneousPoint u m z i : ℚ)) hQzero
            simpa using hc
        have hcard :=
          card_geometricProgression_on_distinct_curves_le_degree_mul
            (K := Qbar) (N := 3) (d := 1) (e := 1) (m := m) hm
            Q (conjugateIdeal g Q) hQdata.1 hconjPrime hQdata.2.1
            hconjHom (hline ▸ hQdata.2.2) hconjDegree hg.symm u
            (cell (some Q)) hintersection
        have haffineCard : (affineCell (some Q)).card ≤ 1 := by
          rw [show affineCell (some Q) =
              (cell (some Q)).image affineMap by rfl,
            Finset.card_image_iff.mpr haffineInjective.injOn]
          simpa using hcard
        have hcardReal : ((affineCell (some Q)).card : ℝ) ≤
            ((distinguished (some Q)).card : ℝ) + 1 := by
          calc
            ((affineCell (some Q)).card : ℝ) ≤ 1 := by
              simpa using (Nat.cast_le.mpr haffineCard :
                ((affineCell (some Q)).card : ℝ) ≤ ((1 : ℕ) : ℝ))
            _ ≤ ((distinguished (some Q)).card : ℝ) + 1 := by
              have hnonneg : (0 : ℝ) ≤ (distinguished (some Q)).card := by
                positivity
              linarith
        simpa [lineCell, rootOptionDegree, hline] using hcardReal
    · simp [lineCell, distinguished, rootOptionDegree, hline]
  have htotal := card_le_globalDistinguished_add_sum_errors
    affineLineUnion active lineCell distinguished (fun _ ↦ (1 : ℝ))
      (by exact Finset.Subset.rfl) hdistinguished hlocal
  have hdistLedger : active.biUnion distinguished ⊆
      quantitativePrefixPersistentRationalLinearPointUnion
        (finiteEquationIdeal sourceEquations) active (fun _ ↦ G₀)
          u m cell := by
    intro x hx
    obtain ⟨o, ho, hxo⟩ := Finset.mem_biUnion.mp hx
    rw [quantitativePrefixPersistentRationalLinearPointUnion]
    refine Finset.mem_biUnion.mpr ⟨o, ho, ?_⟩
    dsimp only [distinguished] at hxo
    split at hxo
    · simpa [rationalCell, chart] using hxo
    · simp at hxo
  have hdistCard := Finset.card_le_card hdistLedger
  rw [hlineCard]
  calc
    (affineLineUnion.card : ℝ) ≤
        ((active.biUnion distinguished).card : ℝ) +
          ∑ _o ∈ active, (1 : ℝ) := htotal
    _ ≤ ((quantitativePrefixPersistentRationalLinearPointUnion
          (finiteEquationIdeal sourceEquations) active (fun _ ↦ G₀)
            u m cell).card : ℝ) + active.card := by
      have hdistCardReal : ((active.biUnion distinguished).card : ℝ) ≤
          ((quantitativePrefixPersistentRationalLinearPointUnion
            (finiteEquationIdeal sourceEquations) active (fun _ ↦ G₀)
              u m cell).card : ℝ) := by exact Nat.cast_le.mpr hdistCard
      simpa using add_le_add_right hdistCardReal (active.card : ℝ)

/-- The numerical conclusion of Salberger 2023, Lemma 3.13 for one integral
curve component of degree `delta`.  The degree-dependent constant is exposed
because the printed `O_{d,delta}` is not uniform in `delta`. -/
def salberger2023Lemma313CurveError
    (constant : ℕ → ℝ) (V : ℝ) (delta : ℕ) : ℝ :=
  constant delta * V ^ ((8 : ℝ) / ((delta : ℝ) + 3)) *
    (1 + Real.log V) ^ (3 : ℕ)

/-- The uniform high-degree majorant used in Salberger 2023, Theorem 3.16
and equation (3.20).  Its constant is independent of the current component
degree, the height, and the auxiliary equations. -/
def salberger2023Theorem316CurveError
    (constant ε V : ℝ) : ℝ :=
  constant * V ^ (ε / 2) * (1 + Real.log V) ^ (3 : ℕ)

/-- A degree-indexed Lemma 3.13 constant which represents the uniform
Theorem 3.16 majorant at one displayed height. -/
def lemma313ConstantForTheorem316
    (constant ε V : ℝ) (delta : ℕ) : ℝ :=
  salberger2023Theorem316CurveError constant ε V /
    (V ^ ((8 : ℝ) / ((delta : ℝ) + 3)) *
      (1 + Real.log V) ^ (3 : ℕ))

/-- The preceding specialization reproduces the uniform high-degree error
exactly. -/
theorem salberger2023Lemma313CurveError_lemma313ConstantForTheorem316
    (constant ε V : ℝ) (delta : ℕ) (hV : 1 < V) :
    salberger2023Lemma313CurveError
        (lemma313ConstantForTheorem316 constant ε V) V delta =
      salberger2023Theorem316CurveError constant ε V := by
  have hpow : V ^ ((8 : ℝ) / ((delta : ℝ) + 3)) ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
  have hlog : (1 + Real.log V) ^ (3 : ℕ) ≠ 0 := by
    have : 0 < 1 + Real.log V := by
      have := Real.log_pos hV
      linarith
    positivity
  unfold salberger2023Lemma313CurveError lemma313ConstantForTheorem316
  calc
    salberger2023Theorem316CurveError constant ε V /
          (V ^ ((8 : ℝ) / ((delta : ℝ) + 3)) *
            (1 + Real.log V) ^ (3 : ℕ)) *
          V ^ ((8 : ℝ) / ((delta : ℝ) + 3)) *
            (1 + Real.log V) ^ (3 : ℕ) =
        salberger2023Theorem316CurveError constant ε V /
          (V ^ ((8 : ℝ) / ((delta : ℝ) + 3)) *
            (1 + Real.log V) ^ (3 : ℕ)) *
          (V ^ ((8 : ℝ) / ((delta : ℝ) + 3)) *
            (1 + Real.log V) ^ (3 : ℕ)) := by ring
    _ =
        salberger2023Theorem316CurveError constant ε V := by
          exact div_mul_cancel₀ _ (mul_ne_zero hpow hlog)

/-- Application-specific high-degree callback.  It asks only for the actual
nonempty root-component cells, and its right side is exactly the exponent and
logarithmic factor in Salberger 2023, Lemma 3.13.

To construct this callback by Salberger's proof one must additionally carry
three facts which the present survivor API omits: the auxiliary degree is
`O(log V)`; the fixed source surface has polynomial height in `V`; and the
root auxiliary has height `V^(O(log V))`.  The last estimate is Salberger's
Lemma 2.8, based on Bombieri--Vaaler, *Invent. Math.* 73 (1983), Theorem 1;
a crude Cramer-rule bound is not a substitute. -/
def Salberger2023Lemma313PersistentRootCallback
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (G₀ : MvPolynomial (Fin 4) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (cutoff : ℕ) (constant : ℕ → ℝ) (V : ℝ) : Prop :=
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  ∀ Q, some Q ∈ active → cutoff < degree Q →
    IsQbarIdealGaloisStable Q →
    ((cell (some Q)).card : ℝ) ≤
      salberger2023Lemma313CurveError constant V (degree Q)

/-- Application-ready uniform high-degree callback corresponding to
Salberger 2023, Theorem 3.16 and equation (3.20).  A single displayed
constant controls every active degree above `cutoff`; quantifying that
constant before the surface data and `V` is what supplies the uniformity
which the pointwise `O_{d,delta}` statement alone does not provide. -/
def Salberger2023Theorem316PersistentRootCallback
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (G₀ : MvPolynomial (Fin 4) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (cutoff : ℕ) (constant ε V : ℝ) : Prop :=
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  ∀ Q, some Q ∈ active → cutoff < degree Q →
    IsQbarIdealGaloisStable Q →
    ((cell (some Q)).card : ℝ) ≤
      salberger2023Theorem316CurveError constant ε V

/-- The honest high-degree alternative.  A Galois-stable geometric curve is
eligible for the rational Salberger callback.  On a nonstable curve every
rational point also lies on a distinct conjugate, so projective Bezout gives
the degree-square error internally. -/
def persistentRootHighDegreeError
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (stableError : ℕ → ℝ)
    (o : Option (Ideal (MvPolynomial (Fin 4) Qbar))) : ℝ :=
  match o with
  | none => 0
  | some Q =>
      if IsQbarIdealGaloisStable Q then stableError (degree Q)
      else (degree Q : ℝ) ^ 2

/-- The local error attached to the three root-degree ranges.  Degree one is
charged zero because its entire cell is put in the literal line union;
degrees `2,...,cutoff` are handled by Pila; larger degrees use the precise
Lemma 3.13 callback. -/
def persistentRootDegreeSplitError
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (cutoff : ℕ) (lowError : ℝ)
    (highConstant : ℕ → ℝ) (V : ℝ)
    (o : Option (Ideal (MvPolynomial (Fin 4) Qbar))) : ℝ :=
  if rootOptionDegree degree o = 1 then 0
  else if rootOptionDegree degree o ≤ cutoff then lowError
  else persistentRootHighDegreeError degree
    (salberger2023Lemma313CurveError highConstant V) o

/-- The degree split with the uniform Theorem 3.16 high-degree error. -/
def persistentRootUniformDegreeSplitError
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (cutoff : ℕ) (lowError highConstant ε V : ℝ)
    (o : Option (Ideal (MvPolynomial (Fin 4) Qbar))) : ℝ :=
  if rootOptionDegree degree o = 1 then 0
  else if rootOptionDegree degree o ≤ cutoff then lowError
  else persistentRootHighDegreeError degree
    (fun _ ↦ salberger2023Theorem316CurveError highConstant ε V) o

/-- At height `V>1`, the pointwise degree-indexed encoding of the uniform
constant gives exactly the uniform split error. -/
theorem persistentRootDegreeSplitError_lemma313ConstantForTheorem316
    (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ)
    (cutoff : ℕ) (lowError highConstant ε V : ℝ)
    (o : Option (Ideal (MvPolynomial (Fin 4) Qbar))) (hV : 1 < V) :
    persistentRootDegreeSplitError degree cutoff lowError
        (lemma313ConstantForTheorem316 highConstant ε V) V o =
      persistentRootUniformDegreeSplitError degree cutoff lowError
        highConstant ε V o := by
  cases o with
  | none =>
      simp [persistentRootDegreeSplitError,
        persistentRootUniformDegreeSplitError, persistentRootHighDegreeError,
        rootOptionDegree]
  | some Q =>
      by_cases hline : degree Q = 1
      · simp [persistentRootDegreeSplitError,
          persistentRootUniformDegreeSplitError, rootOptionDegree, hline]
      · by_cases hbounded : degree Q ≤ cutoff
        · simp [persistentRootDegreeSplitError,
            persistentRootUniformDegreeSplitError, rootOptionDegree,
            hline, hbounded]
        · by_cases hstable : IsQbarIdealGaloisStable Q
          · simp [persistentRootDegreeSplitError,
              persistentRootUniformDegreeSplitError,
              persistentRootHighDegreeError, rootOptionDegree,
              hline, hbounded, hstable,
              salberger2023Lemma313CurveError_lemma313ConstantForTheorem316
                highConstant ε V (degree Q) hV]
          · simp [persistentRootDegreeSplitError,
              persistentRootUniformDegreeSplitError,
              persistentRootHighDegreeError, rootOptionDegree,
              hline, hbounded, hstable]

/-- Persistent root cells split by their *actual* geometric component degree.

The line range and bounded nonlinear range are completely internal, modulo
the stated rational form of Pila and the standard conjugation invariance of
projective Hilbert degree.  The sole remaining counting callback is the
application of Salberger 2023, Lemma 3.13 to the active high-degree root
components.  No terminal cut and no CDHNV curve-count theorem occurs here. -/
theorem exists_uniform_persistentRoot_degreeSplit
    (hPila : Pila1995TheoremARationalQbarPrime)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d e₀ : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (G₀ : MvPolynomial (Fin 4) ℚ),
        G₀.IsHomogeneous e₀ →
        G₀ ∉ finiteEquationIdeal sourceEquations →
      ∀ (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          Finset (IntVector 3))
        (u : IntVector 3) (m : ℕ), 0 < m →
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      (∀ o ∈ active, ∀ z ∈ cell o,
        selectedFiniteEquationComponent
          (qbarSurfaceCutEquationFamily sourceEquations G₀)
          (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) = o) →
      ∀ (center : RealVector 3) (R : ℝ), 0 ≤ R →
      (∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
        |(integralAffineMap u z m i : ℝ) - center i| ≤ R) →
      ∃ degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ,
        (∀ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀),
          Q.IsPrime ∧
          Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
          finiteEquationIdeal (qbarSurfaceEquationFamily sourceEquations) ≤ Q ∧
          HasProjectiveDimensionDegree Q 1 (degree Q)) ∧
        (∑ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q) ≤
          d * e₀ ∧
        active.card ≤ d * e₀ ∧
        ∀ (highConstant : ℕ → ℝ),
          Salberger2023Lemma313PersistentRootCallback sourceEquations G₀
            cell degree cutoff highConstant
              ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) →
          (((active.biUnion cell).card : ℕ) : ℝ) ≤
            ((persistentRootLinePointUnion degree active cell).card : ℝ) +
              ∑ o ∈ active,
                persistentRootDegreeSplitError degree cutoff
                  ((cutoff : ℝ) ^ 2 +
                    C * (2 * R / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
                  highConstant
                    ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) o := by
  classical
  obtain ⟨C, hC, hLow⟩ :=
    exists_uniform_qbarProjectiveCurve_centeredPacket_pila
      hPila hConjugate 3 cutoff ε hε
  refine ⟨C, hC, ?_⟩
  intro d e₀ sourceEquations hprime hgeometricPrime hhom hdegree
    G₀ hG₀hom hG₀not cell u m hm
  dsimp only
  intro hrootSelected center R hR hbox
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  let E := qbarSurfaceEquationFamily sourceEquations
  let G₀bar := MvPolynomial.map (algebraMap ℚ Qbar) G₀
  have hprimeE : (finiteEquationIdeal E).IsPrime := by
    dsimp [E]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact hgeometricPrime
  have hhomE : (finiteEquationIdeal E).IsHomogeneous
      (homogeneousSubmodule (Fin 4) Qbar) := by
    dsimp [E]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) _ hhom
  have hdegreeE : HasProjectiveDimensionDegree (finiteEquationIdeal E) 2 d := by
    dsimp [E]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarHasProjectiveDimensionDegree_of_rational _ hdegree hgeometricPrime
  have hG₀barHom : G₀bar.IsHomogeneous e₀ := hG₀hom.map _
  have hG₀barNot : G₀bar ∉ finiteEquationIdeal E := by
    dsimp [E, G₀bar]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarMap_not_mem_extendedIdeal_of_not_mem _ _ hG₀not
  obtain ⟨degree, hrootData, hrootMass, _hrootCard, hrootOptionsCard⟩ :=
    exists_geometricSurfaceRootComponentData E hprimeE hhomE hdegreeE
      G₀bar hG₀barHom hG₀barNot
  have hrootFamily : finiteEquationFamilyUnion E {G₀bar} =
      qbarSurfaceCutEquationFamily sourceEquations G₀ := by rfl
  have hrootData' : ∀ Q ∈ finiteEquationMinimalPrimes
      (qbarSurfaceCutEquationFamily sourceEquations G₀),
      Q.IsPrime ∧ Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
        finiteEquationIdeal E ≤ Q ∧
        HasProjectiveDimensionDegree Q 1 (degree Q) := by
    intro Q hQ
    apply hrootData Q
    rwa [hrootFamily]
  have hrootMass' :
      (∑ Q ∈ finiteEquationMinimalPrimes
        (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q) ≤
          d * e₀ := by
    rwa [hrootFamily] at hrootMass
  have hactiveSubset : active ⊆ finiteEquationComponentOptions
      (qbarSurfaceCutEquationFamily sourceEquations G₀) := by
    intro o ho
    exact (mem_activeQbarPersistentRootComponentOptions_iff
      sourceEquations G₀ cell o).mp ho |>.1
  have hactiveCard : active.card ≤ d * e₀ := by
    apply (Finset.card_le_card hactiveSubset).trans
    rw [← hrootFamily]
    exact hrootOptionsCard
  refine ⟨degree, hrootData', hrootMass', hactiveCard, ?_⟩
  intro highConstant hHigh
  let affineMap : IntVector 3 → IntVector 3 := fun z ↦ integralAffineMap u z m
  let affineCell := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    (cell o).image affineMap
  let lineCell := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    if rootOptionDegree degree o = 1 then cell o else ∅
  let side : ℝ := 2 * R / (m : ℝ) + 2
  let volume : ℝ := side ^ (3 : ℕ)
  let lowError : ℝ :=
    (cutoff : ℝ) ^ 2 + C * side ^ ((1 / 2 : ℝ) + ε)
  let error := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    persistentRootDegreeSplitError degree cutoff lowError
      highConstant volume o
  have haffineInjective : Function.Injective affineMap :=
    integralAffineMap_injective hm u
  have hchartEq (z : IntVector 3) :
      (fun i ↦ ((integralAffineChartVector (affineMap z) i : ℤ) : Qbar)) =
        (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · simp [affineMap, integralAffineMap, integralAffineChartVector,
        progressionHomogeneousPoint]
  have hlineSubset : ∀ o ∈ active, lineCell o ⊆ cell o := by
    intro o _ho
    dsimp only [lineCell]
    split <;> simp
  have hlocal : ∀ o ∈ active,
      ((cell o).card : ℝ) ≤ ((lineCell o).card : ℝ) + error o := by
    intro o ho
    have hcomponent := hactiveSubset ho
    obtain ⟨Q, hQmin, hQo⟩ :=
      (mem_finiteEquationComponentOptions_iff
        (qbarSurfaceCutEquationFamily sourceEquations G₀) o).mp hcomponent
    subst o
    have hQdata := hrootData' Q hQmin
    have hdegreePos : 0 < degree Q := hQdata.2.2.2.2.1
    by_cases hline : degree Q = 1
    · simp [lineCell, error, persistentRootDegreeSplitError,
        rootOptionDegree, hline]
    · have hnonlinear : 2 ≤ degree Q := by omega
      by_cases hbounded : degree Q ≤ cutoff
      · have hcellNonempty : (cell (some Q)).Nonempty :=
          (mem_activeQbarPersistentRootComponentOptions_iff
            sourceEquations G₀ cell (some Q)).mp ho |>.2
        let representative : IntVector 3 := Classical.choose hcellNonempty
        have hrepresentative : representative ∈ cell (some Q) :=
          Classical.choose_spec hcellNonempty
        have hbase : affineMap representative ∈ affineCell (some Q) :=
          Finset.mem_image.mpr ⟨representative, hrepresentative, rfl⟩
        have hzero : ∀ x ∈ affineCell (some Q),
            (fun i ↦ ((integralAffineChartVector x i : ℤ) : Qbar)) ∈
              affineIdealZeroLocus Q := by
          intro x hx
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
          rw [hchartEq]
          have hselected := hrootSelected (some Q) ho z hz
          exact (selectedFiniteEquationComponent_spec
            (qbarSurfaceCutEquationFamily sourceEquations G₀)
            (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar))
            hselected).2
        have hcong : ∀ x ∈ affineCell (some Q),
            IntVectorCongruent m x (affineMap representative) := by
          intro x hx i
          obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hx
          exact (integralAffineMap_congruent u z i).trans
            (integralAffineMap_congruent u representative i).symm
        have haffineBox : ∀ x ∈ affineCell (some Q), ∀ i,
            |(x i : ℝ) - center i| ≤ R := by
          intro x hx i
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
          exact hbox (some Q) ho z hz i
        have hraw := hLow hm (affineMap representative) Q (degree Q)
          hQdata.1 hQdata.2.1 hQdata.2.2.2 hnonlinear hbounded
          (affineCell (some Q)) hbase hzero hcong center R hR haffineBox
        have hcardEq : (affineCell (some Q)).card = (cell (some Q)).card :=
          Finset.card_image_iff.mpr haffineInjective.injOn
        rw [hcardEq] at hraw
        simpa [lineCell, error, persistentRootDegreeSplitError,
          rootOptionDegree, hline, hbounded, lowError, side] using hraw
      · have hhighDegree : cutoff < degree Q := by omega
        rcases conjugateIdeal_fixed_or_exists_distinct Q with
          hstable | ⟨g, hg⟩
        · have hraw := hHigh Q ho hhighDegree hstable
          simpa [lineCell, error, persistentRootDegreeSplitError,
            persistentRootHighDegreeError, rootOptionDegree, hline,
            hbounded, IsQbarIdealGaloisStable, hstable] using hraw
        · have hconjPrime : (conjugateIdeal g Q).IsPrime :=
            conjugateIdeal_isPrime g Q hQdata.1
          have hconjHom : (conjugateIdeal g Q).IsHomogeneous
              (homogeneousSubmodule (Fin 4) Qbar) :=
            conjugateIdeal_isHomogeneous g Q hQdata.2.1
          have hconjDegree : HasProjectiveDimensionDegree
              (conjugateIdeal g Q) 1 (degree Q) :=
            hConjugate 3 1 (degree Q) g Q hQdata.2.2.2
          have hintersection : ∀ z ∈ cell (some Q),
              (fun i ↦
                (progressionHomogeneousPoint u m z i : Qbar)) ∈
                affineIdealZeroLocus (Q ⊔ conjugateIdeal g Q) := by
            intro z hz
            rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
            have hselected := hrootSelected (some Q) ho z hz
            have hQpoint :
                (fun i ↦
                  (progressionHomogeneousPoint u m z i : Qbar)) ∈
                  affineIdealZeroLocus Q :=
              (selectedFiniteEquationComponent_spec
                (qbarSurfaceCutEquationFamily sourceEquations G₀)
                (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar))
                hselected).2
            have hQzero :=
              (mem_affineIdealZeroLocus_iff_le_ker_aeval Q _).mp hQpoint
            apply sup_le
            · exact hQzero
            · have hconjugate := conjugateIdeal_le_rationalEvaluationKernel
                g Q
                (fun i ↦
                  (progressionHomogeneousPoint u m z i : ℚ)) hQzero
              simpa using hconjugate
          have hcard :=
            card_geometricProgression_on_distinct_curves_le_degree_mul
              (K := Qbar) (N := 3) (d := degree Q) (e := degree Q)
              (m := m) hm Q (conjugateIdeal g Q) hQdata.1 hconjPrime
              hQdata.2.1 hconjHom hQdata.2.2.2 hconjDegree hg.symm u
              (cell (some Q)) hintersection
          have hdegree : ((cell (some Q)).card : ℝ) ≤
              (degree Q : ℝ) ^ 2 := by
            calc
              ((cell (some Q)).card : ℝ) ≤
                  (((degree Q) * (degree Q) : ℕ) : ℝ) := by
                    exact_mod_cast hcard
              _ = (degree Q : ℝ) ^ 2 := by norm_num [pow_two]
          have hnotStable : ¬ IsQbarIdealGaloisStable Q := by
            intro hs
            exact hg (hs g)
          simpa [lineCell, error, persistentRootDegreeSplitError,
            persistentRootHighDegreeError, rootOptionDegree, hline,
            hbounded, hnotStable] using hdegree
  have htotal := card_le_globalDistinguished_add_sum_errors
    (active.biUnion cell) active cell lineCell error (by
      intro z hz
      exact hz)
      hlineSubset hlocal
  simpa [active, persistentRootLinePointUnion, lineCell, error, lowError,
    volume, side]
    using htotal

/-- Uniform-high-degree form of `exists_uniform_persistentRoot_degreeSplit`.

The Salberger constant is quantified before the surface, auxiliary, height,
and active geometric degrees.  Thus this is composable with the genuinely
uniform conclusion of Salberger 2023, Theorem 3.16 / (3.20), whereas an
arbitrary family of constants indexed by a degree which may grow with the
height is not.  The Salberger parameter is the product of the four
projective coordinate bounds; on the chart `[1,z₁,z₂,z₃]` it is represented
here by the cube of the affine side parameter. -/
theorem exists_uniform_persistentRoot_degreeSplit_uniformHigh
    (hPila : Pila1995TheoremARationalQbarPrime)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (highConstant : ℝ),
      ∀ {d e₀ : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (G₀ : MvPolynomial (Fin 4) ℚ),
        G₀.IsHomogeneous e₀ →
        G₀ ∉ finiteEquationIdeal sourceEquations →
      ∀ (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          Finset (IntVector 3))
        (u : IntVector 3) (m : ℕ), 0 < m →
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      (∀ o ∈ active, ∀ z ∈ cell o,
        selectedFiniteEquationComponent
          (qbarSurfaceCutEquationFamily sourceEquations G₀)
          (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) = o) →
      ∀ (center : RealVector 3) (R : ℝ), 0 ≤ R →
      (∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
        |(integralAffineMap u z m i : ℝ) - center i| ≤ R) →
      ∃ degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ,
        (∀ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀),
          Q.IsPrime ∧
          Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
          finiteEquationIdeal (qbarSurfaceEquationFamily sourceEquations) ≤ Q ∧
          HasProjectiveDimensionDegree Q 1 (degree Q)) ∧
        (∑ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q) ≤
          d * e₀ ∧
        active.card ≤ d * e₀ ∧
        (Salberger2023Theorem316PersistentRootCallback sourceEquations G₀
          cell degree cutoff highConstant ε
            ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) →
        (((active.biUnion cell).card : ℕ) : ℝ) ≤
          ((persistentRootLinePointUnion degree active cell).card : ℝ) +
            ∑ o ∈ active,
              persistentRootUniformDegreeSplitError degree cutoff
                ((cutoff : ℝ) ^ 2 +
                  C * (2 * R / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
                highConstant ε ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) o) := by
  classical
  obtain ⟨C, hC, hpointwise⟩ :=
    exists_uniform_persistentRoot_degreeSplit
      hPila hConjugate cutoff ε hε
  refine ⟨C, hC, ?_⟩
  intro highConstant d e₀ sourceEquations hprime hgeometricPrime hhom hdegree
    G₀ hG₀hom hG₀not cell u m hm
  dsimp only
  intro hrootSelected center R hR hbox
  obtain ⟨degree, hrootData, hrootMass, hactiveCard, hbound⟩ :=
    hpointwise sourceEquations hprime hgeometricPrime hhom hdegree
      G₀ hG₀hom hG₀not cell u m hm hrootSelected center R hR hbox
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  let side : ℝ := 2 * R / (m : ℝ) + 2
  let volume : ℝ := side ^ (3 : ℕ)
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hside : 1 < side := by
    dsimp only [side]
    have hdiv : 0 ≤ 2 * R / (m : ℝ) :=
      div_nonneg (mul_nonneg (by norm_num) hR) hmReal.le
    linarith
  have hvolume : 1 < volume := by
    have hfactor : 0 < (side - 1) * (side ^ 2 + side + 1) := by
      apply mul_pos (sub_pos.mpr hside)
      nlinarith [sq_nonneg side]
    dsimp only [volume]
    nlinarith
  let pointConstant : ℕ → ℝ :=
    lemma313ConstantForTheorem316 highConstant ε volume
  refine ⟨degree, hrootData, hrootMass, hactiveCard, ?_⟩
  intro hUniform
  have hPointwise : Salberger2023Lemma313PersistentRootCallback
      sourceEquations G₀ cell degree cutoff pointConstant volume := by
    intro Q hQ hQdegree hstable
    have hraw := hUniform Q hQ hQdegree hstable
    simpa [pointConstant,
      salberger2023Lemma313CurveError_lemma313ConstantForTheorem316
        highConstant ε volume (degree Q) hvolume] using hraw
  have hraw := hbound pointConstant hPointwise
  have herr (o : Option (Ideal (MvPolynomial (Fin 4) Qbar))) :
      persistentRootDegreeSplitError degree cutoff
          ((cutoff : ℝ) ^ 2 +
            C * (2 * R / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
          pointConstant ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) o =
        persistentRootUniformDegreeSplitError degree cutoff
          ((cutoff : ℝ) ^ 2 +
            C * (2 * R / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
          highConstant ε ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) o := by
    apply persistentRootDegreeSplitError_lemma313ConstantForTheorem316
    simpa [side, volume] using hvolume
  simpa only [herr] using hraw

end CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplit
