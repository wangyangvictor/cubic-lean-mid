import TranslatedDepthSeven.RankSevenDegreeOneProperStarQbarReducible
import TranslatedDepthSeven.NongeometricProjectivePrimeProperDivisorPila
import TranslatedDepthSeven.NormalizedPointSpanHyperplane
import TranslatedDepthSeven.ProjectiveFourfoldHyperplanePila

/-!
# Uniform counting on one literal low nonvertex star

This file assembles the four mutually exclusive alternatives for each
actual minimal prime of the literal projective star:

* a geometrically reducible prime is treated on its source cone in
  dimension at most three, and on one proper hypersurface in dimension four,
  using Pila in both cases;
* a geometrically integral component of projective dimension at most three
  is treated directly by Pila;
* a geometrically integral fourfold of degree at least four is treated by
  Salberger after the bounded projection menu;
* for a geometrically integral fourfold of degree at most three, Cramer's
  rule applied to its counted points either gives a bounded containing
  codimension-two section, hence no nonexceptional points, or a proper
  hyperplane containing all those points; Pila treats the latter section.

The proof groups the given finite point set over the literal
`finiteMinimalPrimes` of the star and sums those four estimates.  There is
no assumed count for stars or for their components, and no effective
component-height input.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 16000000

/-- One coefficient-uniform estimate for every finite normalized point set
lying on a single low star centred at a nonvertex point.  The exceptional
cutoff is chosen before epsilon; the counting constants are then chosen
before the translated parameters, centre, and finite set. -/
theorem exists_uniform_low_nonvertex_projectiveStar_bound
    (hPila : Pila1995TheoremA)
    (hSalberger : Salberger2023Theorem04)
    (hProjection : StandardAG.BoundedDegreeHomogeneousProjectionMenu)
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hBezout : StandardAG.FiniteEquationProjectiveComponentBezoutBounds)
    (hstarVertex : StandardAG.ProjectiveStarEqualityForcesVertex)
    (hHyperplane :
      StandardAG.GeometricallyIntegralProjectiveFourfoldHyperplaneRealDegreeMass)
    (hDegreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (hRationalSmooth : StandardAG.RationalProjectiveSmoothPointGeometricIntegrality)
    (hQbarDetectsGeometricPrimeness :
      ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (qbarCoefficientExtensionIdeal I).IsPrime →
          GeometricallyPrimeMvPolynomialIdeal I)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    {originalDegree : ℕ}
    (hOriginal : HasProjectiveDimensionDegree
      (rationalDepthSevenEquationIdeal equations) 5 originalDegree)
    (hOriginalPrime :
      (rationalDepthSevenEquationIdeal equations).IsPrime)
    (hOriginalGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (rationalDepthSevenEquationIdeal equations)) :
    ∃ CF0 : ℕ, ∀ (epsilon : ℝ), 0 < epsilon →
    ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (CF : ℕ), CF0 ≤ CF →
      ∀ (p : Parameters) (x0 h : IntVector 13),
        directionHeight h ≤
            lowDirectionNaturalRadius (surfaceTangentRealSide p) →
        h ≠ 0 →
        IntegralCommonZero equations h →
        ¬ LiesInGeometricProjectiveVertex h
          (rationalDepthSevenEquationIdeal equations) →
        ∀ (M : ℕ), 1 ≤ M →
        ∀ (points : Finset (IntVector 13)),
          points ⊆ depthSevenNormalizedDisplacementFinset
            p x0 equations CF →
          (∀ z ∈ points, ∀ i, (z i).natAbs ≤ M) →
          (∀ z ∈ points,
            (fun i ↦ (integralAffineMap x0 z p.m i : ℚ)) ∈
              affineIdealZeroLocus
                (rationalProjectiveStarIdeal equations degree h)) →
          (points.card : ℝ) ≤ C *
            (((max 1 K * max 1 M + 1 : ℕ) : ℝ) ^
              ((4 : ℝ) + epsilon)) := by
  classical
  let Dstar : ℕ := max 1 (equationFamilyDegreeBound equations) ^ 13
  let CF0 : ℕ := 128
  refine ⟨CF0, ?_⟩
  intro epsilon hepsilon
  obtain ⟨CR, hCR, hReducible⟩ :=
    exists_uniform_qbarReducibleProjectivePrime_properDivisor_pilaBound
      hPila hRationalSmooth 12 Dstar epsilon hepsilon
  obtain ⟨K0, CP, CS, hCP, hCS, hPrimeBounds⟩ :=
    exists_uniform_properStarComponent_pila_salbergerBounds
      hPila hSalberger hProjection Dstar epsilon hepsilon
  obtain ⟨CH, hCH, hHyperplaneBound⟩ :=
    exists_uniform_projectiveFourfold_properHyperplane_pilaBound
      hPila hHyperplane 12 Dstar epsilon hepsilon
  let K : ℕ := max 1 K0
  let C0 : ℝ := CR + CP + CS + CH + 1
  let C : ℝ := (Dstar : ℝ) * C0
  have hDstar : 1 ≤ Dstar := by
    dsimp only [Dstar]
    exact one_le_pow₀ (by omega)
  have hC0 : 0 < C0 := by
    dsimp only [C0]
    linarith
  refine ⟨K, C, mul_pos (by exact_mod_cast hDstar) hC0, ?_⟩
  intro CF hCF p x0 h hlow hh hcenterZero hnotVertex M hM points
    hnormalized hbox hstar
  let star := rationalProjectiveStarIdeal equations degree h
  let components := finiteMinimalPrimes star
  let componentPoints := fun Q : Ideal (MvPolynomial (Fin 13) ℚ) ↦
    points.filter fun z ↦
      (fun i ↦ (integralAffineMap x0 z p.m i : ℚ)) ∈
        affineIdealZeroLocus Q
  let U : ℝ := ((max 1 K * max 1 M + 1 : ℕ) : ℝ)
  have hMbaseNat : M + 1 ≤ max 1 K * max 1 M + 1 := by
    have hmul : 1 * M ≤ max 1 K * max 1 M :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hKbaseNat : K0 * max 1 M ≤ max 1 K * max 1 M + 1 := by
    have hmul : K0 * max 1 M ≤ max 1 K * max 1 M :=
      Nat.mul_le_mul_right (max 1 M) (by
        dsimp only [K]
        omega)
    omega
  have hMbase : (M : ℝ) + 1 ≤ U := by
    dsimp only [U]
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact_mod_cast hMbaseNat
  have hKbase : ((K0 * max 1 M : ℕ) : ℝ) ≤ U := by
    dsimp only [U]
    exact_mod_cast hKbaseNat
  have hUpos : 0 < U := by
    dsimp only [U]
    positivity
  have hexponent : 0 ≤ (4 : ℝ) + epsilon := by linarith
  have hcover : points ⊆ components.biUnion componentPoints := by
    intro z hz
    let x : Fin 13 → ℚ :=
      fun i ↦ (integralAffineMap x0 z p.m i : ℚ)
    let Tzero : Ideal (MvPolynomial (Fin 13) ℚ) :=
      RingHom.ker (MvPolynomial.eval x)
    letI : Tzero.IsPrime := RingHom.ker_isPrime _
    have hstarT : star ≤ Tzero := by
      have hzstar := hstar z hz
      rw [mem_affineIdealZeroLocus_iff] at hzstar
      simpa only [star, x] using hzstar
    obtain ⟨Q, hQ, hQT⟩ := exists_finiteMinimalPrime_le hstarT
    refine Finset.mem_biUnion.mpr ⟨Q, ?_, ?_⟩
    · simpa only [components] using hQ
    · rw [Finset.mem_filter]
      refine ⟨hz, ?_⟩
      rw [mem_affineIdealZeroLocus_iff]
      simpa only [x] using hQT
  have hcomponent : ∀ Q ∈ components,
      ((componentPoints Q).card : ℝ) ≤ C0 * U ^ ((4 : ℝ) + epsilon) := by
    intro Q hQ
    by_cases hempty : componentPoints Q = ∅
    · simp [hempty]
      positivity
    · obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hzdata := Finset.mem_filter.mp hz
      have hzNormalized := hnormalized hzdata.1
      have hznormData := (Finset.mem_filter.mp hzNormalized).2
      dsimp only at hznormData
      obtain ⟨_hztranslated, _hzoriginal, hxne,
        _hznonlinear, _hznotExceptional⟩ := hznormData
      let x : Fin 13 → ℚ :=
        fun i ↦ (integralAffineMap x0 z p.m i : ℚ)
      have hxneQ : x ≠ 0 := intCast_ne_zero hxne
      have hxQ : x ∈ affineIdealZeroLocus Q := by
        simpa only [x] using hzdata.2
      have hOriginalDim : ringKrullDim
          (MvPolynomial (Fin 13) ℚ ⧸
            rationalDepthSevenEquationIdeal equations) = 6 := by
        simpa using hOriginal.1
      obtain ⟨r, d, hQprojective, hr4, hdD, halt⟩ :=
        nonvertexStar_minimalPrime_staticAlternatives
          hHilbert hBezout hstarVertex equations degree hdegree h hh
            hcenterZero hnotVertex hOriginalPrime hOriginalDim Q
            (by simpa only [components, star] using hQ) x hxneQ hxQ
      have hQprime : Q.IsPrime :=
        isPrime_of_mem_finiteMinimalPrimes
          (by simpa only [components, star] using hQ)
      have hQhom : Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) :=
        nonvertexStar_minimalPrime_isHomogeneous equations degree h Q
          (by simpa only [components, star] using hQ)
      have hcellBox : ∀ w ∈ componentPoints Q, ∀ i,
          (w i).natAbs ≤ M := by
        intro w hw i
        exact hbox w (Finset.mem_filter.mp hw).1 i
      have hcellZero : ∀ w ∈ componentPoints Q,
          let y : Fin 13 → ℚ :=
            fun i ↦ (integralAffineMap x0 w p.m i : ℚ)
          y ≠ 0 ∧ y ∈ affineIdealZeroLocus Q := by
        intro w hw
        have hwdata := Finset.mem_filter.mp hw
        have hwnorm := hnormalized hwdata.1
        have hwnormData := (Finset.mem_filter.mp hwnorm).2
        dsimp only at hwnormData
        obtain ⟨_hwtranslated, _hwzero, hwne,
          _hwnonlinear, _hwnotExceptional⟩ := hwnormData
        exact ⟨intCast_ne_zero hwne, hwdata.2⟩
      rcases halt with hReducibleCase |
          ⟨hGeomPrime, hr⟩ |
          ⟨hGeomPrime, hr, hdsmall⟩ |
          ⟨hGeomPrime, hr, hdlarge⟩
      · have hraw := hReducible Q r d p.m M hQprime hQhom
          hQprojective hr4 hdD hReducibleCase p.hm hM x0
          (componentPoints Q) hcellBox hcellZero
        have hpower : ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) ≤
            U ^ ((4 : ℝ) + epsilon) :=
          Real.rpow_le_rpow (by positivity) hMbase hexponent
        calc
          ((componentPoints Q).card : ℝ) ≤
              CR * ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) := hraw
          _ ≤ C0 * U ^ ((4 : ℝ) + epsilon) := by
            have hCRC0 : CR ≤ C0 := by
              dsimp only [C0]
              linarith only [hCP, hCS, hCH]
            exact mul_le_mul hCRC0 hpower
              (Real.rpow_nonneg (by positivity) _) hC0.le
      · have hgeom := hQbarDetectsGeometricPrimeness 13 Q hGeomPrime
        have hraw := hPrimeBounds.1 r d p.m M hr hdD hM p.hm Q hQhom
          hgeom hQprojective x0 (componentPoints Q) hcellBox (by
            intro w hw
            exact (hcellZero w hw).2)
        have hpower : ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) ≤
            U ^ ((4 : ℝ) + epsilon) :=
          Real.rpow_le_rpow (by positivity) hMbase hexponent
        have hCPC0 : CP ≤ C0 := by
          dsimp only [C0]
          linarith only [hCR, hCS, hCH]
        exact hraw.trans (mul_le_mul hCPC0 hpower
          (Real.rpow_nonneg (by positivity) _) hC0.le)
      · have hfour : HasProjectiveDimensionDegree Q 4 d := by
          simpa only [hr] using hQprojective
        have hspan := hDegreeSpan 12 4 d Q hQprime hGeomPrime hQhom hfour
        rw [← finrank_rationalLinearFormsInIdeal_eq_degreeOnePart Q] at hspan
        have hlinear : 2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal Q) := by
          omega
        have hIQ : rationalDepthSevenEquationIdeal equations ≤ Q :=
          (rationalDepthSevenEquationIdeal_le_rationalProjectiveStarIdeal
            equations degree hdegree h).trans
              (le_of_mem_finiteMinimalPrimes
                (by simpa only [components, star] using hQ))
        rcases normalizedPointSubset_empty_or_proper_hyperplane
            p x0 equations hCF hOriginal hOriginalGeometricallyPrime Q
            hQhom hGeomPrime hfour hIQ hlinear (componentPoints Q)
            (fun w hw ↦ hnormalized (Finset.mem_filter.mp hw).1)
            (fun w hw ↦ (hcellZero w hw).2) with hEmpty | ⟨f, hfhom, hfQ, hfzero⟩
        · simp only [hEmpty, Finset.card_empty, Nat.cast_zero]
          positivity
        · have hgeom := hQbarDetectsGeometricPrimeness 13 Q hGeomPrime
          have hraw := hHyperplaneBound Q d hQprime hQhom hgeom hfour hdD
            f hfhom hfQ p.m M p.hm hM x0 (componentPoints Q) hcellBox
            (fun w hw ↦ ⟨(hcellZero w hw).2, hfzero w hw⟩)
          have hpower : ((M : ℝ) + 1) ^ ((4 : ℝ) + epsilon) ≤
              U ^ ((4 : ℝ) + epsilon) :=
            Real.rpow_le_rpow (by positivity) hMbase hexponent
          have hCHC0 : CH ≤ C0 := by
            dsimp only [C0]
            linarith only [hCR, hCP, hCS]
          exact hraw.trans (mul_le_mul hCHC0 hpower
            (Real.rpow_nonneg (by positivity) _) hC0.le)
      · have hgeom := hQbarDetectsGeometricPrimeness 13 Q hGeomPrime
        have hirrelevant : ¬ projectiveIrrelevantIdeal ℚ 12 ≤ Q := by
          intro hirr
          exact hxneQ (eq_zero_of_mem_affineIdealZeroLocus_of_irrelevant_le
            hirr hxQ)
        have hraw := hPrimeBounds.2 d p.m M hdlarge hdD p.hm Q hQprime
          hgeom hQhom hirrelevant (by simpa only [hr] using hQprojective)
          x0 (componentPoints Q) hcellBox (by
            intro w hw
            exact (hcellZero w hw).2)
        have hpower :
            (((K0 * max 1 M : ℕ) : ℝ) ^ ((4 : ℝ) + epsilon)) ≤
              U ^ ((4 : ℝ) + epsilon) :=
          Real.rpow_le_rpow (by positivity) hKbase hexponent
        have hCSC0 : CS ≤ C0 := by
          dsimp only [C0]
          linarith only [hCR, hCP, hCH]
        exact hraw.trans (mul_le_mul hCSC0 hpower
          (Real.rpow_nonneg (by positivity) _) hC0.le)
  have hcard : points.card ≤
      ∑ Q ∈ components, (componentPoints Q).card := by
    calc
      points.card ≤ (components.biUnion componentPoints).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ Q ∈ components, (componentPoints Q).card :=
        Finset.card_biUnion_le
  have hcomponentCount : components.card ≤ Dstar := by
    simpa only [components, star, Dstar] using
      (rationalProjectiveStar_componentBezoutBounds
        hBezout equations degree hdegree h).1
  have hsum :
      (∑ Q ∈ components, ((componentPoints Q).card : ℝ)) ≤
        ∑ _Q ∈ components, C0 * U ^ ((4 : ℝ) + epsilon) := by
    exact Finset.sum_le_sum fun Q hQ ↦ hcomponent Q hQ
  calc
    (points.card : ℝ) ≤
        ∑ Q ∈ components, ((componentPoints Q).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _Q ∈ components, C0 * U ^ ((4 : ℝ) + epsilon) := hsum
    _ = (components.card : ℝ) * C0 *
        U ^ ((4 : ℝ) + epsilon) := by simp [mul_assoc]
    _ ≤ (Dstar : ℝ) * C0 * U ^ ((4 : ℝ) + epsilon) := by
      gcongr
    _ = C * (((max 1 K * max 1 M + 1 : ℕ) : ℝ) ^
        ((4 : ℝ) + epsilon)) := rfl

end

end TranslatedDepthSeven
