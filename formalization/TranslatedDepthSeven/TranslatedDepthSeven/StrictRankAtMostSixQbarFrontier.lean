import TranslatedDepthSeven.StrictRankAtMostSixDegreeSplit
import TranslatedDepthSeven.RationalPrimeGeometricFrontier

/-!
# Qbar frontier contribution to the strict low-rank cell

The high-degree residual components are partitioned according to whether
their literal coefficient extension to `Qbar` is prime.  For every component
in the reducible part, `RationalPrimeGeometricFrontier` supplies one fixed
homogeneous rational ideal of smaller dimension containing all rational
points.  Homogeneous linear normalization then bounds its contribution by
`O(T^4)`.

This removes the whole geometrically reducible contribution before Pila is
used.  No geometric-primality predicate and no counting hypothesis occurs
in this file.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance strictRankAtMostSixQbarFrontierClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- Top-dimensional projective Jacobian-exceptional components whose literal
`Qbar` coefficient extension is prime. -/
noncomputable def qbarPrimeTopProjectiveJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (topProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      (qbarCoefficientExtensionIdeal Q.1).IsPrime

/-- The complementary top-dimensional projective components, whose literal
`Qbar` coefficient extension is reducible. -/
noncomputable def qbarReducibleTopProjectiveJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (topProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      ¬ (qbarCoefficientExtensionIdeal Q.1).IsPrime

/-- Exact partition of the complete top-dimensional residual sum. -/
theorem sum_top_eq_qbarPrime_add_qbarReducible
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (weight : JacobianExceptionalComponent equations → ℕ) :
    (∑ Q ∈ topProjectiveJacobianExceptionalComponents
        equations hhomogeneous, weight Q) =
      (∑ Q ∈ qbarPrimeTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q) +
      ∑ Q ∈ qbarReducibleTopProjectiveJacobianExceptionalComponents
          equations hhomogeneous, weight Q := by
  classical
  simpa only [qbarPrimeTopProjectiveJacobianExceptionalComponents,
    qbarReducibleTopProjectiveJacobianExceptionalComponents] using
    (Finset.sum_filter_add_sum_filter_not
      (topProjectiveJacobianExceptionalComponents equations hhomogeneous)
      (fun Q ↦ (qbarCoefficientExtensionIdeal Q.1).IsPrime)
      weight).symm

/-- Certified degree-at-least-eight residual components whose literal
`Qbar` coefficient extension is prime. -/
noncomputable def qbarPrimeHighDegreeJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (highDegreeTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      (qbarCoefficientExtensionIdeal Q.1).IsPrime

/-- The complementary high-degree components, whose literal `Qbar`
coefficient extension is reducible. -/
noncomputable def qbarReducibleHighDegreeJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (highDegreeTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      ¬ (qbarCoefficientExtensionIdeal Q.1).IsPrime

/-- Exact partition of the high-degree residual sum. -/
theorem sum_highDegree_eq_qbarPrime_add_qbarReducible
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (weight : JacobianExceptionalComponent equations → ℕ) :
    (∑ Q ∈ highDegreeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous, weight Q) =
      (∑ Q ∈ qbarPrimeHighDegreeJacobianExceptionalComponents
          equations hhomogeneous, weight Q) +
      ∑ Q ∈ qbarReducibleHighDegreeJacobianExceptionalComponents
          equations hhomogeneous, weight Q := by
  classical
  simpa only [qbarPrimeHighDegreeJacobianExceptionalComponents,
    qbarReducibleHighDegreeJacobianExceptionalComponents] using
    (Finset.sum_filter_add_sum_filter_not
      (highDegreeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous)
      (fun Q ↦ (qbarCoefficientExtensionIdeal Q.1).IsPrime)
      weight).symm

/-- Any fixed finite family of top-dimensional Jacobian-exceptional
components whose literal `Qbar` coefficient extensions are reducible has
total contribution `O(T^4)`.  This supplied-finset form makes explicit that
neither a Hilbert polynomial nor a degree certificate is used in the
frontier argument. -/
theorem exists_qbarReducibleComponentSum_le_fourthPower
    (integralEquations : Finset (MvPolynomial (Fin 13) ℤ))
    (componentEquations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ componentEquations,
      ∃ d : ℕ, f.IsHomogeneous d)
    (components : Finset (JacobianExceptionalComponent componentEquations))
    (hcomponents : ∀ Q ∈ components,
      Q ∈ topProjectiveJacobianExceptionalComponents
        componentEquations hhomogeneous)
    (hnotPrime : ∀ Q ∈ components,
      ¬ (qbarCoefficientExtensionIdeal Q.1).IsPrime)
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
    ∃ K : ℕ, ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
      (∑ Q ∈ components,
        ((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1).card) ≤
        K * (surfaceTangentNaturalSide p) ^ 4 := by
  classical
  have hEach : ∀ Q : {Q // Q ∈ components}, ∃ K : ℕ,
      ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
        ((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1.1).card ≤
          K * (surfaceTangentNaturalSide p) ^ 4 := by
    intro Q
    have hQdata := hqualification Q.1 (hcomponents Q.1 Q.2)
    let D := jacobianExceptionalComponentNormalization
      componentEquations hhomogeneous Q.1
    have hQlower : (5 : WithBot ℕ∞) ≤
        ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1.1) := by
      have hpoly := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
        (R := ℚ) (Fin 5)
      simp only [ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_fin] at hpoly
      rw [D.ringKrullDim_eq_parameterPolynomial
        13 Q.1.1 hQdata.2.2.2.1, hQdata.1]
      exact hpoly
    have hQupper :
        ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1.1) ≤
          (5 : WithBot ℕ∞) := by
      exact WithBot.lt_add_one_iff.mp hQdata.2.2.2.2.1
    have hQdim : ringKrullDim
        (MvPolynomial (Fin 13) ℚ ⧸ Q.1.1) = 5 := by
      exact le_antisymm hQupper hQlower
    obtain ⟨K, hK⟩ :=
      exists_card_le_mul_fourthPower_of_qbarExtension_notPrime
        Q.1.1 hQdata.2.2.2.1 hQdata.2.1 hQdim
          (hnotPrime Q.1 Q.2)
    refine ⟨16 * K, ?_⟩
    intro p x₀ CF
    let X := (depthSevenNormalizedDisplacementFinset
      p x₀ integralEquations CF).filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
          affineIdealZeroLocus Q.1.1
    have hbound := hK X x₀ p.m (2 * surfaceTangentNaturalSide p)
      p.hm (by
        have := one_le_surfaceTangentNaturalSide p
        omega)
      (by
        intro z hz i
        exact depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
          p x₀ integralEquations CF (Finset.mem_filter.mp hz).1 i)
      (by
        intro z hz
        exact (Finset.mem_filter.mp hz).2)
    calc
      X.card ≤ K * (2 * surfaceTangentNaturalSide p) ^ 4 := hbound
      _ = (16 * K) * (surfaceTangentNaturalSide p) ^ 4 := by ring
  choose componentConstant hcomponentConstant using hEach
  let K : ℕ := ∑ Q : {Q // Q ∈ components}, componentConstant Q
  refine ⟨K, ?_⟩
  intro p x₀ CF
  calc
    (∑ Q ∈ components,
      ((depthSevenNormalizedDisplacementFinset
        p x₀ integralEquations CF).filter fun z ↦
          (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
            affineIdealZeroLocus Q.1).card) =
        ∑ Q : {Q // Q ∈ components},
          ((depthSevenNormalizedDisplacementFinset
            p x₀ integralEquations CF).filter fun z ↦
              (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
                affineIdealZeroLocus Q.1.1).card := by
      rw [← Finset.sum_attach]
      rfl
    _ ≤ ∑ Q : {Q // Q ∈ components},
        componentConstant Q * (surfaceTangentNaturalSide p) ^ 4 := by
      exact Finset.sum_le_sum fun Q _ ↦ hcomponentConstant Q p x₀ CF
    _ = K * (surfaceTangentNaturalSide p) ^ 4 := by
      simp only [K, Finset.sum_mul]

/-- The complete Qbar-reducible top-dimensional contribution is `O(T^4)`.
In particular this conclusion is independent of all projective degree
certificates. -/
theorem exists_qbarReducibleTop_componentSum_le_fourthPower
    (integralEquations : Finset (MvPolynomial (Fin 13) ℤ))
    (componentEquations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ componentEquations,
      ∃ d : ℕ, f.IsHomogeneous d)
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
    ∃ K : ℕ, ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
      (∑ Q ∈ qbarReducibleTopProjectiveJacobianExceptionalComponents
          componentEquations hhomogeneous,
        ((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1).card) ≤
        K * (surfaceTangentNaturalSide p) ^ 4 := by
  apply exists_qbarReducibleComponentSum_le_fourthPower
    integralEquations componentEquations hhomogeneous
      (qbarReducibleTopProjectiveJacobianExceptionalComponents
        componentEquations hhomogeneous)
  · intro Q hQ
    exact (Finset.mem_filter.mp hQ).1
  · intro Q hQ
    exact (Finset.mem_filter.mp hQ).2
  · exact hqualification

/-- The complete Qbar-reducible high-degree contribution is `O(T^4)` for
the literal normalized displacement finset.  All constants are chosen only
from the fixed finite component list, before `p`, `x₀`, and `CF`. -/
theorem exists_qbarReducibleHighDegree_componentSum_le_fourthPower
    (integralEquations : Finset (MvPolynomial (Fin 13) ℤ))
    (componentEquations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ componentEquations,
      ∃ d : ℕ, f.IsHomogeneous d)
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
    ∃ K : ℕ, ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
      (∑ Q ∈ qbarReducibleHighDegreeJacobianExceptionalComponents
          componentEquations hhomogeneous,
        ((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1).card) ≤
        K * (surfaceTangentNaturalSide p) ^ 4 := by
  classical
  let components :=
    qbarReducibleHighDegreeJacobianExceptionalComponents
      componentEquations hhomogeneous
  have hEach : ∀ Q : {Q // Q ∈ components}, ∃ K : ℕ,
      ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
        ((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1.1).card ≤
          K * (surfaceTangentNaturalSide p) ^ 4 := by
    intro Q
    have hQhigh := (Finset.mem_filter.mp Q.2).1
    have hQtop := (Finset.mem_filter.mp hQhigh).1
    have hQnotPrime := (Finset.mem_filter.mp Q.2).2
    have hQdata := hqualification Q.1 hQtop
    let D := jacobianExceptionalComponentNormalization
      componentEquations hhomogeneous Q.1
    have hQlower : (5 : WithBot ℕ∞) ≤
        ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1.1) := by
      have hpoly := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
        (R := ℚ) (Fin 5)
      simp only [ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_fin] at hpoly
      rw [D.ringKrullDim_eq_parameterPolynomial
        13 Q.1.1 hQdata.2.2.2.1, hQdata.1]
      exact hpoly
    have hQupper :
        ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1.1) ≤
          (5 : WithBot ℕ∞) := by
      exact WithBot.lt_add_one_iff.mp hQdata.2.2.2.2.1
    have hQdim : ringKrullDim
        (MvPolynomial (Fin 13) ℚ ⧸ Q.1.1) = 5 := by
      exact le_antisymm hQupper hQlower
    obtain ⟨K, hK⟩ :=
      exists_card_le_mul_fourthPower_of_qbarExtension_notPrime
        Q.1.1 hQdata.2.2.2.1 hQdata.2.1 hQdim hQnotPrime
    refine ⟨16 * K, ?_⟩
    intro p x₀ CF
    let X := (depthSevenNormalizedDisplacementFinset
      p x₀ integralEquations CF).filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
          affineIdealZeroLocus Q.1.1
    have hbound := hK X x₀ p.m (2 * surfaceTangentNaturalSide p)
      p.hm (by
        have := one_le_surfaceTangentNaturalSide p
        omega)
      (by
        intro z hz i
        exact depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
          p x₀ integralEquations CF (Finset.mem_filter.mp hz).1 i)
      (by
        intro z hz
        exact (Finset.mem_filter.mp hz).2)
    calc
      X.card ≤ K * (2 * surfaceTangentNaturalSide p) ^ 4 := hbound
      _ = (16 * K) * (surfaceTangentNaturalSide p) ^ 4 := by ring
  choose componentConstant hcomponentConstant using hEach
  let K : ℕ := ∑ Q : {Q // Q ∈ components}, componentConstant Q
  refine ⟨K, ?_⟩
  intro p x₀ CF
  calc
    (∑ Q ∈ qbarReducibleHighDegreeJacobianExceptionalComponents
        componentEquations hhomogeneous,
      ((depthSevenNormalizedDisplacementFinset
        p x₀ integralEquations CF).filter fun z ↦
          (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
            affineIdealZeroLocus Q.1).card) =
        ∑ Q : {Q // Q ∈ components},
          ((depthSevenNormalizedDisplacementFinset
            p x₀ integralEquations CF).filter fun z ↦
              (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
                affineIdealZeroLocus Q.1.1).card := by
      rw [← Finset.sum_attach]
      rfl
    _ ≤ ∑ Q : {Q // Q ∈ components},
        componentConstant Q * (surfaceTangentNaturalSide p) ^ 4 := by
      exact Finset.sum_le_sum fun Q _ ↦ hcomponentConstant Q p x₀ CF
    _ = K * (surfaceTangentNaturalSide p) ^ 4 := by
      simp only [K, Finset.sum_mul]

/-- Exact unconditional strict low-rank endpoint after the Galois-frontier
argument.  Every top-dimensional component whose literal `Qbar` coefficient
extension is reducible has been absorbed into `K*T^4`; the displayed sum is
over precisely the remaining top components.  No Hilbert polynomial or
degree certificate occurs in this statement. -/
theorem exists_strictRankAtMostSix_card_le_fourthPower_add_qbarPrimeTop
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (degree : ℕ)
    (hI : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree) :
    ∃ E : Finset (MvPolynomial (Fin 13) ℚ),
      ∃ hEhomogeneous : ∀ f ∈ E, ∃ d : ℕ, f.IsHomogeneous d,
      ∃ C : DepthSevenJacobianChartIndex E,
      ∃ K : ℕ,
        Ideal.span (E : Set (MvPolynomial (Fin 13) ℚ)) =
            rationalDepthSevenEquationIdeal equations ∧
        C.determinant ∉ rationalDepthSevenEquationIdeal equations ∧
        (∀ (Q : JacobianExceptionalComponent E),
          Q ∈ topProjectiveJacobianExceptionalComponents E hEhomogeneous →
          (jacobianExceptionalComponentNormalization
                E hEhomogeneous Q).parameterCount = 5 ∧
            Q.1.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) ∧
            IsSaturatedByProjectiveIrrelevantIdeal Q.1 ∧
            Q.1.IsPrime ∧
            ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) < 6 ∧
            ∀ r d : ℕ, HasProjectiveDimensionDegree Q.1 r d → r = 4) ∧
        ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
          let componentPoints := fun Q : JacobianExceptionalComponent E ↦
            ((depthSevenNormalizedDisplacementFinset
                p x₀ equations CF).filter fun z ↦
              (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
                affineIdealZeroLocus Q.1).card
          (depthSevenNormalizedRankAtMostSixFinset
              p x₀ equations CF).card ≤
            K * (surfaceTangentNaturalSide p) ^ 4 +
              ∑ Q ∈ qbarPrimeTopProjectiveJacobianExceptionalComponents
                    E hEhomogeneous, componentPoints Q := by
  classical
  obtain ⟨E, hEhomogeneous, C, K₀, hspan, hdeterminant,
      hqualification, hbound⟩ :=
    exists_strictRankAtMostSix_card_le_fourthPower_add_projectiveFourfoldComponents
      equations degree hI
  obtain ⟨K₁, hK₁⟩ :=
    exists_qbarReducibleTop_componentSum_le_fourthPower
      equations E hEhomogeneous hqualification
  refine ⟨E, hEhomogeneous, C, K₀ + K₁, hspan, hdeterminant,
    hqualification, ?_⟩
  intro p x₀ CF
  let componentPoints := fun Q : JacobianExceptionalComponent E ↦
    ((depthSevenNormalizedDisplacementFinset
        p x₀ equations CF).filter fun z ↦
      (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
        affineIdealZeroLocus Q.1).card
  change (depthSevenNormalizedRankAtMostSixFinset
      p x₀ equations CF).card ≤
    (K₀ + K₁) * (surfaceTangentNaturalSide p) ^ 4 +
      ∑ Q ∈ qbarPrimeTopProjectiveJacobianExceptionalComponents
        E hEhomogeneous, componentPoints Q
  have hbase := hbound p x₀ CF
  change (depthSevenNormalizedRankAtMostSixFinset
      p x₀ equations CF).card ≤
    K₀ * (surfaceTangentNaturalSide p) ^ 4 +
      ∑ Q ∈ topProjectiveJacobianExceptionalComponents
        E hEhomogeneous, componentPoints Q at hbase
  have hsplit := sum_top_eq_qbarPrime_add_qbarReducible
    E hEhomogeneous componentPoints
  have hreducible :
      (∑ Q ∈ qbarReducibleTopProjectiveJacobianExceptionalComponents
          E hEhomogeneous, componentPoints Q) ≤
        K₁ * (surfaceTangentNaturalSide p) ^ 4 :=
    hK₁ p x₀ CF
  rw [hsplit] at hbase
  rw [Nat.add_mul]
  omega

end

end TranslatedDepthSeven
