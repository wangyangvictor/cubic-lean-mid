import TranslatedDepthSeven.RankSevenDegreeOneProperStarCounting
import TranslatedDepthSeven.StrictRankAtMostSixStandardAG
import TranslatedDepthSeven.StrictRankAtMostSixLowDegree

/-!
# The low-degree fourfolds in a singular projective star

The only effective input isolated here is the following standard
fixed-degree elimination consequence: if a minimal component of a bounded
integral homogeneous equation family contains two independent rational
linear forms, two such forms admit a basis of polynomially bounded
Pluecker height.  The input is purely algebraic; it contains no point count,
line count, star count, or assertion about a translated box.

For the literal star equations, their coefficient height is proved directly
from the displayed formula for `f(h + Tz)`.  The classical degree--span
inequality supplies the two independent forms for a projective fourfold of
degree at most three.  The resulting bounded-height codimension-two section
puts every rational point of that component in the concrete exceptional
locus already used by the depth-seven statement.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 12000000

/-- The literal coefficient majorant for all equations of the projective
star centred at `h`. -/
def projectiveStarEquationCoefficientHeight
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (h : IntVector 13) : ℕ :=
  equationFamilySupportBound equations *
    equationFamilyCoefficientBound equations *
    (2 * max 1 (directionHeight h)) ^
      equationFamilyDegreeBound equations

/-- Every coefficient of every displayed integral star equation is bounded
by the preceding literal majorant. -/
theorem projectiveStarEquation_coeff_natAbs_le
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (h : IntVector 13)
    {g : MvPolynomial (Fin 13) ℤ}
    (hg : g ∈ projectiveStarEquationFamily equations degree h)
    {mu : Fin 13 →₀ ℕ} (hmu : mu ∈ g.support) :
    (g.coeff mu).natAbs ≤
      projectiveStarEquationCoefficientHeight equations h := by
  classical
  rw [projectiveStarEquationFamily, Finset.mem_biUnion] at hg
  obtain ⟨f, hf, hgf⟩ := hg
  rw [Finset.mem_image] at hgf
  obtain ⟨k, _hk, rfl⟩ := hgf
  calc
    ((starCoefficient f h k).coeff mu).natAbs ≤
        f.support.card * equationFamilyCoefficientBound equations *
          (2 * max 1 (directionHeight h)) ^
            equationFamilyDegreeBound equations := by
      apply starCoefficient_coeff_natAbs_le f h k mu
        (equationFamilyDegreeBound equations)
        (equationFamilyCoefficientBound equations)
        (directionHeight h)
      · intro nu hnu
        exact coeff_natAbs_le_equationFamilyCoefficientBound hf hnu
      · exact totalDegree_le_equationFamilyDegreeBound hf
      · exact intVector_natAbs_le_directionHeight h
    _ ≤ equationFamilySupportBound equations *
        equationFamilyCoefficientBound equations *
          (2 * max 1 (directionHeight h)) ^
            equationFamilyDegreeBound equations := by
      gcongr
      exact support_card_le_equationFamilySupportBound hf
    _ = projectiveStarEquationCoefficientHeight equations h := rfl

/-- Every star equation is homogeneous of degree at most the maximum degree
of the original fixed family. -/
theorem projectiveStarEquation_homogeneous_degree_le
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (h : IntVector 13)
    {g : MvPolynomial (Fin 13) ℤ}
    (hg : g ∈ projectiveStarEquationFamily equations degree h) :
    ∃ e : ℕ, g.IsHomogeneous e ∧
      e ≤ equationFamilyDegreeBound equations := by
  classical
  rw [projectiveStarEquationFamily, Finset.mem_biUnion] at hg
  obtain ⟨f, hf, hgf⟩ := hg
  rw [Finset.mem_image] at hgf
  obtain ⟨k, hk, rfl⟩ := hgf
  by_cases hfzero : f = 0
  · subst f
    refine ⟨0, ?_, by omega⟩
    simp only [starCoefficient, symbolicLinePolynomial, map_zero,
      Polynomial.coeff_zero]
    intro mu hmu
    exact (hmu (MvPolynomial.coeff_zero mu)).elim
  · refine ⟨k, starCoefficient_isHomogeneous f h k, ?_⟩
    have hkdegree : k ≤ degree f :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hdegreeEq : degree f = f.totalDegree :=
      (hdegree f hf).totalDegree hfzero |>.symm
    rw [hdegreeEq] at hkdegree
    exact hkdegree.trans (totalDegree_le_equationFamilyDegreeBound hf)

/-- The fixed coefficient factor in the literal star majorant. -/
def projectiveStarCoefficientHeightConstant
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) : ℕ :=
  equationFamilySupportBound equations *
    equationFamilyCoefficientBound equations *
    2 ^ equationFamilyDegreeBound equations

/-- A deliberately generous fixed exponent absorbing the coefficient factor
and the height of every low direction. -/
def projectiveStarCoefficientHeightExponent
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) : ℕ :=
  projectiveStarCoefficientHeightConstant equations +
    equationFamilyDegreeBound equations + 1

/-- At a low direction the entire star equation family has coefficient
height at most one fixed power of the manuscript height. -/
theorem projectiveStarEquationCoefficientHeight_cast_le_heightPower
    (p : Parameters)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (h : IntVector 13)
    (hlow : directionHeight h ≤
      lowDirectionNaturalRadius (surfaceTangentRealSide p)) :
    (projectiveStarEquationCoefficientHeight equations h : ℝ) ≤
      p.H ^ projectiveStarCoefficientHeightExponent equations := by
  let C := projectiveStarCoefficientHeightConstant equations
  let e := equationFamilyDegreeBound equations
  have hH : (2 : ℝ) ≤ p.H := by linarith [p.five_le_H]
  have hdir : (max 1 (directionHeight h) : ℝ) ≤ p.H :=
    max_le (by linarith [p.five_le_H])
      (lowDirectionHeight_cast_le_manuscriptHeight p h hlow)
  have hC : (C : ℝ) ≤ p.H ^ C := by
    have hself : C ≤ 2 ^ C := self_le_two_pow C
    have hselfReal : (C : ℝ) ≤ (2 : ℝ) ^ C := by exact_mod_cast hself
    exact hselfReal.trans (pow_le_pow_left₀ (by positivity) hH C)
  have hraw :
      (projectiveStarEquationCoefficientHeight equations h : ℝ) =
        (C : ℝ) * (max 1 (directionHeight h) : ℝ) ^ e := by
    dsimp only [projectiveStarEquationCoefficientHeight,
      projectiveStarCoefficientHeightConstant, C, e]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_max,
      Nat.cast_one]
    ring
  rw [hraw, projectiveStarCoefficientHeightExponent]
  dsimp only [C, e]
  calc
    (projectiveStarCoefficientHeightConstant equations : ℝ) *
        (max 1 (directionHeight h) : ℝ) ^
          equationFamilyDegreeBound equations ≤
      p.H ^ projectiveStarCoefficientHeightConstant equations *
        p.H ^ equationFamilyDegreeBound equations := by
          gcongr
    _ = p.H ^ (projectiveStarCoefficientHeightConstant equations +
        equationFamilyDegreeBound equations) := by rw [pow_add]
    _ ≤ p.H ^ (projectiveStarCoefficientHeightConstant equations +
        equationFamilyDegreeBound equations + 1) := by
      apply pow_le_pow_right₀ (by linarith [p.five_le_H])
      omega

namespace StandardAG

/-- Fixed-degree effective elimination for the degree-one part of an actual
minimal component.  The exponent is chosen from the ambient dimension and
degree bound before the equation family, its coefficients, and the selected
component.

This is the precise narrow height consequence of effective primary
decomposition (equivalently, arithmetic Bezout plus linear algebra) used in
the low-degree branch. -/
def EffectiveMinimalComponentTwoRowHeight : Prop :=
  ∀ (N D : ℕ), ∃ kappa : ℕ, 1 ≤ kappa ∧
    ∀ (family : Finset (MvPolynomial (Fin (N + 1)) ℤ)) (H : ℕ),
      (∀ f ∈ family, ∃ e : ℕ, f.IsHomogeneous e ∧ e ≤ D) →
      (∀ f ∈ family, ∀ mu ∈ f.support, (f.coeff mu).natAbs ≤ H) →
      ∀ (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        Q ∈ finiteMinimalPrimes
          (finiteEquationIdeal (rationalizedEquationFinset family)) →
        2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal Q) →
          ∃ A : Matrix (Fin 2) (Fin (N + 1)) ℚ,
            A.rank = 2 ∧
            finiteEquationIdeal
              (rationalMatrixRowLinearEquationFamily A) ≤ Q ∧
            rationalProjectiveLinearHeight A ≤ (max 2 H) ^ kappa

end StandardAG

/-- Uniform bounded-height two-row spans for every geometrically integral
low-degree fourfold component of every literal low-direction star.  The
exponent `kappa` is selected before `p`, the direction, and the component.
Rational primes which split geometrically are not covered by this lemma;
the actual counting argument treats their rational points by the separate
geometric-component intersection estimate. -/
theorem exists_uniform_lowDegreeStar_twoRowSpan
    (hEffective : StandardAG.EffectiveMinimalComponentTwoRowHeight)
    (hDegreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f)) :
    ∃ kappa : ℕ, 1 ≤ kappa ∧
      ∀ (p : Parameters) (h : IntVector 13),
        directionHeight h ≤
            lowDirectionNaturalRadius (surfaceTangentRealSide p) →
        ∀ (Q : Ideal (MvPolynomial (Fin 13) ℚ)),
          Q ∈ finiteMinimalPrimes
              (rationalProjectiveStarIdeal equations degree h) →
          (Q.map (MvPolynomial.map
            (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime →
          ∀ d : ℕ, HasProjectiveDimensionDegree Q 4 d → d ≤ 3 →
            ∃ A : Matrix (Fin 2) (Fin 13) ℚ,
              A.rank = 2 ∧
              finiteEquationIdeal
                (rationalMatrixRowLinearEquationFamily A) ≤ Q ∧
              rationalProjectiveLinearHeight A ≤
                ⌈p.H ^
                  (projectiveStarCoefficientHeightExponent equations *
                    kappa)⌉₊ := by
  obtain ⟨kappa, hkappa, heffective⟩ :=
    hEffective 12 (equationFamilyDegreeBound equations)
  refine ⟨kappa, hkappa, ?_⟩
  intro p h hlow Q hQ hQgeometric d hQprojective hd
  have hQprime : Q.IsPrime := isPrime_of_mem_finiteMinimalPrimes hQ
  have hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) :=
    nonvertexStar_minimalPrime_isHomogeneous equations degree h Q hQ
  have hspan := hDegreeSpan 12 4 d Q hQprime hQgeometric hQhomogeneous hQprojective
  rw [← finrank_rationalLinearFormsInIdeal_eq_degreeOnePart Q] at hspan
  have htwo : 2 ≤ Module.finrank ℚ (rationalLinearFormsInIdeal Q) := by
    omega
  obtain ⟨A, hArank, hAQ, hAheight⟩ := heffective
    (projectiveStarEquationFamily equations degree h)
    (projectiveStarEquationCoefficientHeight equations h)
    (fun f hf ↦ projectiveStarEquation_homogeneous_degree_le
      equations degree hdegree h hf)
    (fun f hf mu hmu ↦ projectiveStarEquation_coeff_natAbs_le
      equations degree h hf hmu)
    Q (by simpa only [rationalProjectiveStarIdeal] using hQ) htwo
  refine ⟨A, hArank, hAQ, hAheight.trans ?_⟩
  have hraw := projectiveStarEquationCoefficientHeight_cast_le_heightPower
    p equations h hlow
  have hbase : (max 2
      (projectiveStarEquationCoefficientHeight equations h) : ℝ) ≤
      p.H ^ projectiveStarCoefficientHeightExponent equations := by
    apply max_le
    · have hpowFive : (5 : ℝ) ≤
          p.H ^ projectiveStarCoefficientHeightExponent equations := by
        have hexp : 1 ≤ projectiveStarCoefficientHeightExponent equations := by
          unfold projectiveStarCoefficientHeightExponent
          omega
        calc
          (5 : ℝ) ≤ p.H := p.five_le_H
          _ = p.H ^ 1 := by ring
          _ ≤ p.H ^ projectiveStarCoefficientHeightExponent equations :=
            pow_le_pow_right₀ (by linarith [p.five_le_H]) hexp
      exact (by norm_num : (2 : ℝ) ≤ 5).trans hpowFive
    · exact hraw
  have hpow : ((max 2
      (projectiveStarEquationCoefficientHeight equations h)) ^ kappa : ℕ) ≤
      (p.H ^ (projectiveStarCoefficientHeightExponent equations *
        kappa) : ℝ) := by
    have := pow_le_pow_left₀ (by positivity) hbase kappa
    rw [← pow_mul] at this
    exact_mod_cast this
  exact_mod_cast hpow.trans (Nat.le_ceil
    (p.H ^ (projectiveStarCoefficientHeightExponent equations * kappa)))

/-- A nonexceptional normalized point cannot lie on a geometrically
integral projective fourfold of degree at most three contained in a
low-direction star.  The contradiction uses the literal codimension-two
section and the already-defined exceptional locus. -/
theorem no_normalizedPoint_on_lowDegree_geometricallyPrimeStarComponent
    {equations : Finset (MvPolynomial (Fin 13) ℤ)}
    {originalDegree : ℕ}
    {degree : MvPolynomial (Fin 13) ℤ → ℕ}
    (hOriginal : HasProjectiveDimensionDegree
      (rationalDepthSevenEquationIdeal equations) 5 originalDegree)
    (hOriginalGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (rationalDepthSevenEquationIdeal equations))
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    {kappa CF : ℕ}
    (hCF : projectiveStarCoefficientHeightExponent equations * kappa ≤ CF)
    (hspan : ∀ (p : Parameters) (h : IntVector 13),
      directionHeight h ≤
          lowDirectionNaturalRadius (surfaceTangentRealSide p) →
      ∀ (Q : Ideal (MvPolynomial (Fin 13) ℚ)),
        Q ∈ finiteMinimalPrimes
            (rationalProjectiveStarIdeal equations degree h) →
        ∀ d : ℕ, HasProjectiveDimensionDegree Q 4 d → d ≤ 3 →
          ∃ A : Matrix (Fin 2) (Fin 13) ℚ,
            A.rank = 2 ∧
            finiteEquationIdeal
              (rationalMatrixRowLinearEquationFamily A) ≤ Q ∧
            rationalProjectiveLinearHeight A ≤
              ⌈p.H ^
                (projectiveStarCoefficientHeightExponent equations *
                  kappa)⌉₊)
    (p : Parameters) (x0 h : IntVector 13)
    (hlow : directionHeight h ≤
      lowDirectionNaturalRadius (surfaceTangentRealSide p))
    (Q : Ideal (MvPolynomial (Fin 13) ℚ))
    (hQ : Q ∈ finiteMinimalPrimes
      (rationalProjectiveStarIdeal equations degree h))
    (hQbar : (qbarCoefficientExtensionIdeal Q).IsPrime)
    {d : ℕ} (hQprojective : HasProjectiveDimensionDegree Q 4 d)
    (hd : d ≤ 3)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x0 equations CF)
    (hzQ : (fun i ↦ (integralAffineMap x0 z p.m i : ℚ)) ∈
      affineIdealZeroLocus Q) : False := by
  classical
  obtain ⟨A, hArank, hAQ, hAheightRaw⟩ :=
    hspan p h hlow Q hQ d hQprojective hd
  have hAheight : rationalProjectiveLinearHeight A ≤ ⌈p.H ^ CF⌉₊ :=
    hAheightRaw.trans (Nat.ceil_mono
      (pow_le_pow_right₀ (by linarith [p.five_le_H] : (1 : ℝ) ≤ p.H) hCF))
  have hIQ : rationalDepthSevenEquationIdeal equations ≤ Q :=
    (rationalDepthSevenEquationIdeal_le_rationalProjectiveStarIdeal
      equations degree hdegree h).trans (le_of_mem_finiteMinimalPrimes hQ)
  let R : Ideal (MvPolynomial (Fin 13) Qbar) :=
    qbarCoefficientExtensionIdeal Q
  have hsectionR : finiteEquationIdeal
      (geometricLinearSectionEquationFinset equations A) ≤ R := by
    apply geometricLinearSectionIdeal_le_of_rational_containment
      equations A Q R
    · simpa only [rationalDepthSevenEquationIdeal] using hIQ
    · exact hAQ
    · exact le_rfl
  have hRprojective : HasGeometricProjectiveDimensionDegree R 4 d :=
    qbarHasProjectiveDimensionDegree_of_rational Q hQprojective hQbar
  have hzdata := (Finset.mem_filter.mp hz).2
  dsimp only at hzdata
  obtain ⟨_hzbox, _hzzero, hxne, _hnonlinear, hnotExceptional⟩ := hzdata
  have hxR : ProjectivePointVanishesOnGeometricIdeal R
      (integralProjectiveClass (integralAffineMap x0 z p.m) hxne) := by
    exact projectivePointVanishesOn_qbarCoefficientExtension Q
      (nonvertexStar_minimalPrime_isHomogeneous equations degree h Q hQ)
      (integralAffineMap x0 z p.m) hxne hzQ
  apply hnotExceptional
  exact memDepthSevenExceptionalLocus_of_codimensionTwo_fourfold_section
    equations ⌈p.H ^ CF⌉₊ A hArank hAheight
      (by simpa only [rationalDepthSevenEquationIdeal] using hOriginal)
      (by simpa only [rationalDepthSevenEquationIdeal] using
        hOriginalGeometricallyPrime)
      R hQbar hsectionR hRprojective
      (integralProjectiveClass (integralAffineMap x0 z p.m) hxne) hxR

end

end TranslatedDepthSeven
