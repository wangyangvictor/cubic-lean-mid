import TranslatedDepthSeven.ProjectiveDegreeTwoSpan
import TranslatedDepthSeven.ProjectiveDegreeTwoSpanInternal
import TranslatedDepthSeven.StrictRankAtMostSixDegreeSplit
import TranslatedDepthSeven.StrictRankAtMostSixQbarFrontier

/-!
# Elimination of the degree-at-most-two low-rank components

A top-dimensional component of the Jacobian-exceptional locus having
projective degree one or two is contained in a fixed rational linear space
of codimension at least two.  Once the exponent in the definition of the
literal exceptional locus dominates the fixed Pluecker heights, every
normalized point on such a component is therefore excluded.  Thus this
branch contributes zero; no point-counting theorem is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance strictRankAtMostSixLowDegreeClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- A nonzero rational point of a homogeneous rational ideal lies on its
literal coefficient extension to `Qbar`, including for the representative
chosen by `Projectivization`. -/
theorem projectivePointVanishesOn_qbarCoefficientExtension
    (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (x : IntVector 13) (hx : x ≠ 0)
    (hxI : (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus I) :
    ProjectivePointVanishesOnGeometricIdeal
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar)))
      (integralProjectiveClass x hx) := by
  let Ibar : Ideal (MvPolynomial (Fin 13) Qbar) :=
    I.map (MvPolynomial.map (algebraMap ℚ Qbar))
  let xbar : Fin 13 → Qbar := fun i ↦ algebraMap ℚ Qbar (x i : ℚ)
  have hxbar : xbar ∈ affineIdealZeroLocus Ibar := by
    change Ibar ≤ RingHom.ker (MvPolynomial.eval xbar)
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    change MvPolynomial.map (algebraMap ℚ Qbar) f ∈
      RingHom.ker (MvPolynomial.eval xbar)
    rw [RingHom.mem_ker]
    change MvPolynomial.eval xbar
      (MvPolynomial.map (algebraMap ℚ Qbar) f) = 0
    rw [MvPolynomial.eval_map]
    have hzero := hxI f hf
    change MvPolynomial.eval (fun i ↦ (x i : ℚ)) f = 0 at hzero
    change MvPolynomial.eval₂ (algebraMap ℚ Qbar)
      ((algebraMap ℚ Qbar) ∘ fun i ↦ (x i : ℚ)) f = 0
    rw [← MvPolynomial.eval₂_comp, hzero, map_zero]
  have hIbarHomogeneous :
      Ibar.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) := by
    exact isHomogeneous_map_mvPolynomialMap
      (algebraMap ℚ Qbar) I hIhomogeneous
  let xrat : Fin 13 → ℚ := fun i ↦ (x i : ℚ)
  have hxrat : xrat ≠ 0 := intCast_ne_zero hx
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℚ xrat hxrat
  have ha' : a • xrat = (integralProjectiveClass x hx).rep := by
    simpa only [integralProjectiveClass, xrat] using ha
  have hscaled := smul_mem_affineIdealZeroLocus_of_isHomogeneous
    Ibar hIbarHomogeneous hxbar (algebraMap ℚ Qbar (a : ℚ))
  have hrep :
      (fun i ↦ algebraMap ℚ Qbar
        ((integralProjectiveClass x hx).rep i)) =
      fun i ↦ algebraMap ℚ Qbar (a : ℚ) * xbar i := by
    funext i
    have hi := congrFun ha' i
    change algebraMap ℚ Qbar ((integralProjectiveClass x hx).rep i) = _
    rw [← hi]
    change algebraMap ℚ Qbar ((a : ℚ) * (x i : ℚ)) =
      algebraMap ℚ Qbar (a : ℚ) * algebraMap ℚ Qbar (x i : ℚ)
    exact map_mul (algebraMap ℚ Qbar) (a : ℚ) (x i : ℚ)
  rw [ProjectivePointVanishesOnGeometricIdeal, hrep]
  exact hscaled

/-- A natural number is bounded by the ceiling of the corresponding fixed
power of every strict height occurring in the argument. -/
theorem fixedNatural_le_ceil_strictHeight_pow
    (C CF : ℕ) (hCF : C ≤ CF) (p : Parameters) :
    C ≤ ⌈p.H ^ CF⌉₊ := by
  have hCtwo : (C : ℝ) ≤ (2 : ℝ) ^ C := by
    exact_mod_cast self_le_two_pow C
  have htwoH : (2 : ℝ) ≤ p.H := by linarith [p.five_le_H]
  have hpowBase : (2 : ℝ) ^ C ≤ p.H ^ C :=
    pow_le_pow_left₀ (by positivity) htwoH C
  have hpowExponent : p.H ^ C ≤ p.H ^ CF :=
    pow_le_pow_right₀ (by linarith [p.five_le_H] : (1 : ℝ) ≤ p.H) hCF
  have hreal : (C : ℝ) ≤ p.H ^ CF :=
    hCtwo.trans (hpowBase.trans hpowExponent)
  exact_mod_cast hreal.trans (Nat.le_ceil (p.H ^ CF))

/-- The actual low-degree list after the geometrically reducible rational
components have been removed. -/
noncomputable def qbarPrimeDegreeAtMostTwoTopComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (degreeAtMostTwoTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      (qbarCoefficientExtensionIdeal Q.1).IsPrime

/-- Every contribution from a Qbar-prime projective fourfold of degree at
most two vanishes once the exceptional-height exponent dominates one fixed
integer.  The required degree-two span estimate is proved internally from
the displayed homogeneous normalization and the literal Qbar-prime test.
The projective Hilbert dimension--degree certificate is already part of
membership in the displayed degree-at-most-two list.

No counting estimate or branch majorant occurs among the hypotheses. -/
theorem exists_degreeAtMostTwo_componentSum_eq_zero
    (integralEquations : Finset (MvPolynomial (Fin 13) ℤ))
    (componentEquations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous :
      ∀ f ∈ componentEquations, ∃ d : ℕ, f.IsHomogeneous d)
    (hspan : Ideal.span
        (componentEquations : Set (MvPolynomial (Fin 13) ℚ)) =
      rationalDepthSevenEquationIdeal integralEquations)
    (originalDegree : ℕ)
    (hOriginal : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal integralEquations)
        5 originalDegree)
    (hOriginalGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (rationalDepthSevenEquationIdeal integralEquations))
    (hqualification :
      ∀ (Q : JacobianExceptionalComponent componentEquations),
        Q ∈ topProjectiveJacobianExceptionalComponents
          componentEquations hhomogeneous →
        (jacobianExceptionalComponentNormalization
              componentEquations hhomogeneous Q).parameterCount = 5 ∧
          Q.1.IsHomogeneous
            (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) ∧
          IsSaturatedByProjectiveIrrelevantIdeal Q.1 ∧
          Q.1.IsPrime ∧
          ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) < 6 ∧
          ∀ r d : ℕ, HasProjectiveDimensionDegree Q.1 r d → r = 4) :
    ∃ CF₀ : ℕ, ∀ CF : ℕ, CF₀ ≤ CF →
      ∀ (p : Parameters) (x₀ : IntVector 13),
        (∑ Q ∈ qbarPrimeDegreeAtMostTwoTopComponents
              componentEquations hhomogeneous,
          ((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1).card) = 0 := by
  classical
  let components := qbarPrimeDegreeAtMostTwoTopComponents
    componentEquations hhomogeneous
  have hdegreeData : ∀ Q : {Q // Q ∈ components},
      ∃ d : ℕ,
        HasProjectiveDimensionDegree Q.1.1 4 d ∧ d ≤ 2 := by
    intro Q
    have hQlow := (Finset.mem_filter.mp Q.2).1
    exact (Finset.mem_filter.mp hQlow).2
  choose degree hQprojective hQdegree using hdegreeData
  have hQtop : ∀ Q : {Q // Q ∈ components},
      Q.1 ∈ topProjectiveJacobianExceptionalComponents
        componentEquations hhomogeneous := by
    intro Q
    exact (Finset.mem_filter.mp
      ((Finset.mem_filter.mp Q.2).1)).1
  let selectedDegree : JacobianExceptionalComponent componentEquations → ℕ :=
    fun Q ↦ if hQ : Q ∈ components then degree ⟨Q, hQ⟩ else 0
  obtain ⟨heightBound, hspaces⟩ :=
    exists_uniform_twoRow_linearSpan_of_finite_degreeAtMostTwo_qbarPrime
      components (fun Q ↦ Q.1)
        (fun Q ↦ jacobianExceptionalComponentNormalization
          componentEquations hhomogeneous Q)
        selectedDegree
        (fun Q hQ ↦ (hqualification Q (hQtop ⟨Q, hQ⟩)).2.2.2.1)
        (fun Q hQ ↦ (hqualification Q (hQtop ⟨Q, hQ⟩)).2.1)
        (fun Q hQ ↦ (hqualification Q (hQtop ⟨Q, hQ⟩)).1)
        (fun Q hQ ↦ by
          simpa only [selectedDegree, dif_pos hQ] using
            hQprojective ⟨Q, hQ⟩)
        (fun Q hQ ↦ by
          simpa only [selectedDegree, dif_pos hQ] using hQdegree ⟨Q, hQ⟩)
        (fun Q hQ ↦ (Finset.mem_filter.mp hQ).2)
  refine ⟨heightBound, ?_⟩
  intro CF hCF p x₀
  apply Finset.sum_eq_zero
  intro Q hQ
  obtain ⟨v, _hvIndependent, hvrank, hvrows, hvheight⟩ :=
    hspaces Q hQ
  let A : Matrix (Fin 2) (Fin 13) ℚ := rationalLinearFormMatrix v
  have hArank : A.rank = 2 := hvrank
  have hAheight : rationalProjectiveLinearHeight A ≤ ⌈p.H ^ CF⌉₊ :=
    hvheight.trans (fixedNatural_le_ceil_strictHeight_pow
      heightBound CF hCF p)
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzbase := (Finset.mem_filter.mp hz).1
  have hzQ := (Finset.mem_filter.mp hz).2
  let x : IntVector 13 := integralAffineMap x₀ z p.m
  have hzdata := (Finset.mem_filter.mp hzbase).2
  dsimp only at hzdata
  obtain ⟨_hbox, _hzero, hx, _hlinear, hnotExceptional⟩ := hzdata
  have hQtop' := hQtop ⟨Q, hQ⟩
  have hQdata := hqualification Q hQtop'
  let R : Ideal (MvPolynomial (Fin 13) Qbar) :=
    qbarCoefficientExtensionIdeal Q.1
  have hRprime : R.IsPrime := by
    exact (Finset.mem_filter.mp hQ).2
  have hOriginalQ :
      finiteEquationIdeal (rationalizedEquationFinset integralEquations) ≤
        Q.1 := by
    calc
      finiteEquationIdeal (rationalizedEquationFinset integralEquations) =
          rationalDepthSevenEquationIdeal integralEquations := rfl
      _ = Ideal.span
          (componentEquations : Set (MvPolynomial (Fin 13) ℚ)) := hspan.symm
      _ ≤ depthSevenJacobianExceptionalIdeal componentEquations :=
        span_le_depthSevenJacobianExceptionalIdeal componentEquations
      _ ≤ Q.1 := le_of_mem_finiteMinimalPrimes Q.2
  have hRowsQ : finiteEquationIdeal
      (rationalMatrixRowLinearEquationFamily A) ≤ Q.1 := by
    exact finiteEquationIdeal_rowLinear_le_of_rows_mem v Q.1 hvrows
  have hsectionR : finiteEquationIdeal
      (geometricLinearSectionEquationFinset integralEquations A) ≤ R := by
    exact geometricLinearSectionIdeal_le_of_rational_containment
      integralEquations A Q.1 R hOriginalQ hRowsQ le_rfl
  have hRprojective : HasGeometricProjectiveDimensionDegree
      R 4 (degree ⟨Q, hQ⟩) := by
    exact qbarHasProjectiveDimensionDegree_of_rational
      Q.1 (hQprojective ⟨Q, hQ⟩) hRprime
  have hxR : ProjectivePointVanishesOnGeometricIdeal R
      (integralProjectiveClass x hx) := by
    exact projectivePointVanishesOn_qbarCoefficientExtension
      Q.1 hQdata.2.1 x hx hzQ
  apply hnotExceptional
  exact memDepthSevenExceptionalLocus_of_codimensionTwo_fourfold_section
    integralEquations ⌈p.H ^ CF⌉₊ A hArank hAheight
      hOriginal.2.2.2 hOriginalGeometricallyPrime R hRprime
      hsectionR hRprojective (integralProjectiveClass x hx) hxR

end

end TranslatedDepthSeven
