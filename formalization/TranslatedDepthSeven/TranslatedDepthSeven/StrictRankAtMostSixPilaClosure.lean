import TranslatedDepthSeven.StrictRankAtMostSixLowDegree
import TranslatedDepthSeven.StrictRankAtMostSixGeometricPila

/-!
# Published Pila input for the remaining strict low-rank components

This file removes the formerly introduced rational-Qbar variant of Pila's
theorem from the low-rank branch.  The counting input is exactly
`Published.Pila1995TheoremA`.  The only standard algebraic-geometric bridge
accepted as a hypothesis is the usual criterion that primeness after base
change to an algebraic closure implies geometric integrality, i.e. primeness
after every field extension.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance strictRankAtMostSixPilaClosureClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- The Qbar-prime part of the certified degree-at-least-three list. -/
noncomputable def qbarPrimeDegreeAtLeastThreeTopComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (degreeAtLeastThreeTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      (qbarCoefficientExtensionIdeal Q.1).IsPrime

/-- Once every top component has its ordinary projective Hilbert
polynomial, the Qbar-prime top list is exactly the disjoint low/high degree
split used by the argument. -/
theorem sum_qbarPrimeTop_eq_degreeAtMostTwo_add_degreeAtLeastThree
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (hcertified : ∀ Q ∈ topProjectiveJacobianExceptionalComponents
      equations hhomogeneous, HasCertifiedProjectiveDegree Q)
    (weight : JacobianExceptionalComponent equations → ℕ) :
    (∑ Q ∈ qbarPrimeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous, weight Q) =
      (∑ Q ∈ qbarPrimeDegreeAtMostTwoTopComponents
          equations hhomogeneous, weight Q) +
      ∑ Q ∈ qbarPrimeDegreeAtLeastThreeTopComponents
          equations hhomogeneous, weight Q := by
  classical
  let top := qbarPrimeTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous
  let low := degreeAtMostTwoTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous
  have hlow : top.filter (fun Q ↦ Q ∈ low) =
      qbarPrimeDegreeAtMostTwoTopComponents equations hhomogeneous := by
    ext Q
    simp only [Finset.mem_filter, top, low,
      qbarPrimeTopProjectiveJacobianExceptionalComponents,
      qbarPrimeDegreeAtMostTwoTopComponents,
      degreeAtMostTwoTopProjectiveJacobianExceptionalComponents]
    tauto
  have hhigh : top.filter (fun Q ↦ Q ∉ low) =
      qbarPrimeDegreeAtLeastThreeTopComponents equations hhomogeneous := by
    ext Q
    simp only [Finset.mem_filter, top, low,
      qbarPrimeTopProjectiveJacobianExceptionalComponents,
      qbarPrimeDegreeAtLeastThreeTopComponents,
      degreeAtLeastThreeTopProjectiveJacobianExceptionalComponents]
    constructor
    · rintro ⟨⟨hQtop, hQbar⟩, hQnotlow⟩
      exact ⟨⟨hQtop, hQnotlow, hcertified Q hQtop⟩, hQbar⟩
    · rintro ⟨⟨hQtop, hQnotlow, _hQcertified⟩, hQbar⟩
      exact ⟨⟨hQtop, hQbar⟩, hQnotlow⟩
  have hsplit := (Finset.sum_filter_add_sum_filter_not
    top (fun Q ↦ Q ∈ low) weight).symm
  rw [hlow, hhigh] at hsplit
  simpa only [top] using hsplit

/-- Under the standard algebraic-closure criterion, the literal Qbar-prime
high-degree list agrees with the geometrically prime list to which the
already formalized real-coefficient form of Pila applies. -/
theorem qbarPrimeDegreeAtLeastThree_eq_geometricallyPrime
    (hQbarDetectsGeometricPrimeness :
      ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          GeometricallyPrimeMvPolynomialIdeal I)
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    qbarPrimeDegreeAtLeastThreeTopComponents equations hhomogeneous =
      geometricallyPrimeDegreeAtLeastThreeJacobianExceptionalComponents
        equations hhomogeneous := by
  classical
  ext Q
  simp only [qbarPrimeDegreeAtLeastThreeTopComponents,
    geometricallyPrimeDegreeAtLeastThreeJacobianExceptionalComponents,
    Finset.mem_filter]
  constructor
  · rintro ⟨hQthree, hQbar⟩
    exact ⟨hQthree, hQbarDetectsGeometricPrimeness 13 Q.1 hQbar⟩
  · rintro ⟨hQthree, hQgeometric⟩
    exact ⟨hQthree, hQgeometric Qbar⟩

/-- Exact repair of the Pila-interface mismatch: the remaining
Qbar-prime, degree-at-least-three sum is bounded using only the printed
real-coefficient form `Published.Pila1995TheoremA`, plus the standard
algebraic-closure criterion displayed in the preceding theorem. -/
theorem exists_qbarPrimeDegreeAtLeastThree_componentSum_le_pila
    (hPila : Pila1995TheoremA)
    (hQbarDetectsGeometricPrimeness :
      ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          GeometricallyPrimeMvPolynomialIdeal I)
    (integralEquations : Finset (MvPolynomial (Fin 13) ℤ))
    (componentEquations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ componentEquations, ∃ d : ℕ, f.IsHomogeneous d)
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
          ∀ r d : ℕ, HasProjectiveDimensionDegree Q.1 r d → r = 4)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
        (∑ Q ∈ qbarPrimeDegreeAtLeastThreeTopComponents
            componentEquations hhomogeneous,
          (((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1).card : ℝ)) ≤
          ((qbarPrimeDegreeAtLeastThreeTopComponents
              componentEquations hhomogeneous).card : ℝ) * C *
            ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
              ((13 / 3 : ℝ) + epsilon) := by
  rw [qbarPrimeDegreeAtLeastThree_eq_geometricallyPrime
    hQbarDetectsGeometricPrimeness componentEquations hhomogeneous]
  exact exists_geometricallyPrimeDegreeAtLeastThree_componentSum_le_pila
    hPila integralEquations componentEquations hhomogeneous
      hqualification epsilon hepsilon

/-- Complete strict low-rank endpoint.  Apart from Pila's printed theorem,
the hypotheses are precisely two standard projective-algebraic facts:

* Hilbert--Serre supplies the eventual projective Hilbert polynomial;
* primeness over an algebraic closure detects geometric integrality.

The degree-at-most-two linear-span estimate is proved internally.

The conclusion is the uniform `13/3 + epsilon` bound for the exact
rank-at-most-six normalized finset.  In particular, it contains neither an
assumed branch estimate nor the formerly introduced strengthened Pila
interface. -/
theorem exists_strictRankAtMostSix_card_le_thirteenThirds
    (hPila : Pila1995TheoremA)
    (hHilbertSerre :
      ∀ (N r : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        I.IsPrime →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        ¬ projectiveIrrelevantIdeal ℚ N ≤ I →
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) = r + 1 →
        ∃ d : ℕ, HasProjectiveDimensionDegree I r d)
    (hQbarDetectsGeometricPrimeness :
      ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          GeometricallyPrimeMvPolynomialIdeal I)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (degree : ℕ)
    (hGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (rationalDepthSevenEquationIdeal equations))
    (hI : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree) :
    ∃ CF₀ : ℕ, ∀ CF : ℕ, CF₀ ≤ CF →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 < C ∧
          ∀ (p : Parameters) (x₀ : IntVector 13),
            ((depthSevenNormalizedRankAtMostSixFinset
                p x₀ equations CF).card : ℝ) ≤
              C * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
                ((13 / 3 : ℝ) + epsilon) := by
  classical
  obtain ⟨componentEquations, hhomogeneous, chart, K₀, hspan,
      hdeterminant, hqualification, hbase⟩ :=
    exists_strictRankAtMostSix_card_le_fourthPower_add_qbarPrimeTop
      equations degree hI
  have hcertified :
      ∀ Q ∈ topProjectiveJacobianExceptionalComponents
        componentEquations hhomogeneous, HasCertifiedProjectiveDegree Q := by
    intro Q hQ
    have hQdata := hqualification Q hQ
    let D := jacobianExceptionalComponentNormalization
      componentEquations hhomogeneous Q
    have hQlower : (5 : WithBot ℕ∞) ≤
        ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) := by
      have hpoly := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
        (R := ℚ) (Fin 5)
      simp only [ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_fin] at hpoly
      rw [D.ringKrullDim_eq_parameterPolynomial
        13 Q.1 hQdata.2.2.2.1, hQdata.1]
      exact hpoly
    have hQupper :
        ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) ≤
          (5 : WithBot ℕ∞) :=
      WithBot.lt_add_one_iff.mp hQdata.2.2.2.2.1
    have hQdim :
        ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) = 4 + 1 := by
      norm_num
      exact le_antisymm hQupper hQlower
    have hQnotIrrelevant :
        ¬ projectiveIrrelevantIdeal ℚ 12 ≤ Q.1 :=
      (Finset.mem_filter.mp hQ).2.2
    obtain ⟨d, hd⟩ := hHilbertSerre 12 4 Q.1
      hQdata.2.2.2.1 hQdata.2.1 hQnotIrrelevant hQdim
    exact ⟨d, hd⟩
  obtain ⟨CF₀, hlowZero⟩ :=
    exists_degreeAtMostTwo_componentSum_eq_zero
      equations componentEquations hhomogeneous hspan degree hI
        hGeometricallyPrime hqualification
  refine ⟨CF₀, ?_⟩
  intro CF hCF epsilon hepsilon
  obtain ⟨C₁, hC₁, hhigh⟩ :=
    exists_qbarPrimeDegreeAtLeastThree_componentSum_le_pila
      hPila hQbarDetectsGeometricPrimeness equations componentEquations
        hhomogeneous hqualification epsilon hepsilon
  let numberOfHighComponents :=
    (qbarPrimeDegreeAtLeastThreeTopComponents
      componentEquations hhomogeneous).card
  let C : ℝ := 1 + (K₀ : ℝ) + (numberOfHighComponents : ℝ) * C₁
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro p x₀
  let componentPoints := fun Q : JacobianExceptionalComponent
      componentEquations ↦
    ((depthSevenNormalizedDisplacementFinset
        p x₀ equations CF).filter fun z ↦
      (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
        affineIdealZeroLocus Q.1).card
  have hsplit :=
    sum_qbarPrimeTop_eq_degreeAtMostTwo_add_degreeAtLeastThree
      componentEquations hhomogeneous hcertified componentPoints
  have hlow := hlowZero CF hCF p x₀
  have hbaseNat := hbase p x₀ CF
  change (depthSevenNormalizedRankAtMostSixFinset
      p x₀ equations CF).card ≤
    K₀ * (surfaceTangentNaturalSide p) ^ 4 +
      ∑ Q ∈ qbarPrimeTopProjectiveJacobianExceptionalComponents
        componentEquations hhomogeneous, componentPoints Q at hbaseNat
  rw [hsplit, hlow, zero_add] at hbaseNat
  have hbaseReal :
      ((depthSevenNormalizedRankAtMostSixFinset
          p x₀ equations CF).card : ℝ) ≤
        (K₀ : ℝ) * (surfaceTangentNaturalSide p : ℝ) ^ 4 +
          ∑ Q ∈ qbarPrimeDegreeAtLeastThreeTopComponents
              componentEquations hhomogeneous,
            (componentPoints Q : ℝ) := by
    exact_mod_cast hbaseNat
  have hhighBound := hhigh p x₀ CF
  change (∑ Q ∈ qbarPrimeDegreeAtLeastThreeTopComponents
      componentEquations hhomogeneous, (componentPoints Q : ℝ)) ≤
    (numberOfHighComponents : ℝ) * C₁ *
      ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
        ((13 / 3 : ℝ) + epsilon) at hhighBound
  let B : ℝ := ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ)
  have hBone : (1 : ℝ) ≤ B := by
    dsimp only [B]
    exact_mod_cast (by omega : 1 ≤ 2 * surfaceTangentNaturalSide p + 1)
  have hsideB : (surfaceTangentNaturalSide p : ℝ) ≤ B := by
    dsimp only [B]
    exact_mod_cast (by omega : surfaceTangentNaturalSide p ≤
      2 * surfaceTangentNaturalSide p + 1)
  have hexponent : (4 : ℝ) ≤ (13 / 3 : ℝ) + epsilon := by
    norm_num
    linarith
  have hsidePower : (surfaceTangentNaturalSide p : ℝ) ^ 4 ≤
      B ^ ((13 / 3 : ℝ) + epsilon) := by
    calc
      (surfaceTangentNaturalSide p : ℝ) ^ 4 ≤ B ^ 4 :=
        pow_le_pow_left₀ (by positivity) hsideB 4
      _ = B ^ (4 : ℝ) := (Real.rpow_natCast B 4).symm
      _ ≤ B ^ ((13 / 3 : ℝ) + epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hBone hexponent
  have hKbound :
      (K₀ : ℝ) * (surfaceTangentNaturalSide p : ℝ) ^ 4 ≤
        (K₀ : ℝ) * B ^ ((13 / 3 : ℝ) + epsilon) :=
    mul_le_mul_of_nonneg_left hsidePower (by positivity)
  calc
    ((depthSevenNormalizedRankAtMostSixFinset
        p x₀ equations CF).card : ℝ) ≤
      (K₀ : ℝ) * (surfaceTangentNaturalSide p : ℝ) ^ 4 +
        ∑ Q ∈ qbarPrimeDegreeAtLeastThreeTopComponents
            componentEquations hhomogeneous,
          (componentPoints Q : ℝ) := hbaseReal
    _ ≤ (K₀ : ℝ) * B ^ ((13 / 3 : ℝ) + epsilon) +
        (numberOfHighComponents : ℝ) * C₁ *
          B ^ ((13 / 3 : ℝ) + epsilon) := by
      exact add_le_add hKbound hhighBound
    _ = ((K₀ : ℝ) + (numberOfHighComponents : ℝ) * C₁) *
        B ^ ((13 / 3 : ℝ) + epsilon) := by ring
    _ ≤ C * B ^ ((13 / 3 : ℝ) + epsilon) := by
      apply mul_le_mul_of_nonneg_right
      · dsimp only [C]
        linarith
      · exact Real.rpow_nonneg (by positivity) _
    _ = C * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
        ((13 / 3 : ℝ) + epsilon) := rfl

end

end TranslatedDepthSeven
