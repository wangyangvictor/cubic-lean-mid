import TranslatedDepthSeven.PrimeProjectiveSaturation

/-!
# The exact low-dimensional/projective split of the Jacobian exceptional locus

Let a homogeneous prime affine cone have Krull dimension six and suppose one
displayed `7 x 7` Jacobian minor is nonzero at its generic point.  Every
minimal component of the rank-at-most-six locus then has a homogeneous linear
normalization with fewer than six parameters.

This file makes the useful split literal.  Components with at most four
normalization parameters have an elementary `O(T^4)` translated-box count.
An irrelevant component contributes at most the cone vertex.  The only
components left over have a five-parameter homogeneous normalization and
survive projectivization; they are actual homogeneous saturated primes.  No
dimension, degree, component, or counting predicate is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 300000

local instance jacobianExceptionalProjectiveSplitClassicalDecidablePred
    {A : Type*} (p : A → Prop) : DecidablePred p := Classical.decPred p

/-- The finite type of actual minimal primes of the literal Jacobian
exceptional ideal. -/
abbrev JacobianExceptionalComponent
    (equations : Finset (MvPolynomial (Fin 13) ℚ)) :=
  {Q : Ideal (MvPolynomial (Fin 13) ℚ) //
    Q ∈ finiteMinimalPrimes
      (depthSevenJacobianExceptionalIdeal equations)}

/-- Choose one actual homogeneous linear normalization for each actual
minimal component.  The choice uses only homogeneous Noether normalization
already proved in `HomogeneousLinearElimination`. -/
noncomputable def jacobianExceptionalComponentNormalization
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (Q : JacobianExceptionalComponent equations) :
    HomogeneousLinearNormalizationData Q.1 := by
  have hQprime : Q.1.IsPrime :=
    isPrime_of_mem_finiteMinimalPrimes Q.2
  have hQhom : Q.1.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) :=
    exceptionalMinimalPrime_isHomogeneous equations hhomogeneous Q.2
  exact Classical.choice
    (exists_homogeneousLinearNormalizationData 13 Q.1 hQprime hQhom)

/-- Every selected exceptional-component normalization has at most five
parameters. -/
theorem jacobianExceptionalComponentNormalization_parameterCount_lt_six
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (P : Ideal (MvPolynomial (Fin 13) ℚ)) [P.IsPrime]
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin 13) ℚ)) = P)
    (C : DepthSevenJacobianChartIndex equations)
    (hD : C.determinant ∉ P)
    (hPdim : ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ P) = 6)
    (Q : JacobianExceptionalComponent equations) :
    (jacobianExceptionalComponentNormalization
      equations hhomogeneous Q).parameterCount < 6 := by
  let D := jacobianExceptionalComponentNormalization
    equations hhomogeneous Q
  letI : Q.1.IsPrime := isPrime_of_mem_finiteMinimalPrimes Q.2
  have hQdim : ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) < 6 :=
    ringKrullDim_exceptionalMinimalPrime_lt_nat_of_determinant_notMem
      P Q.1 hP C hD Q.2 hPdim
  exact normalization_parameter_lt_of_ringKrullDim_lt_nat
    D.hom D.hom_injective D.hom_finite.to_isIntegral hQdim

/-- The finite residual list: exactly those exceptional components whose
chosen linear normalization has five parameters and which do not contain
the irrelevant coordinate ideal. -/
noncomputable def topProjectiveJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) := by
  classical
  exact Finset.univ.filter fun Q ↦
    (jacobianExceptionalComponentNormalization
      equations hhomogeneous Q).parameterCount = 5 ∧
    ¬ Published.projectiveIrrelevantIdeal ℚ 12 ≤ Q.1

/-- Every component on the residual list is an actual homogeneous saturated
prime, has a five-parameter homogeneous normalization, and has cone
dimension strictly below six.  The only projective datum not supplied here
is its eventual Hilbert polynomial (equivalently its dimension and degree in
the exact format required by the published counting theorem). -/
theorem mem_topProjectiveJacobianExceptionalComponents_qualification
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (P : Ideal (MvPolynomial (Fin 13) ℚ)) [P.IsPrime]
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin 13) ℚ)) = P)
    (C : DepthSevenJacobianChartIndex equations)
    (hD : C.determinant ∉ P)
    (hPdim : ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ P) = 6)
    {Q : JacobianExceptionalComponent equations}
    (hQ : Q ∈ topProjectiveJacobianExceptionalComponents
      equations hhomogeneous) :
    (jacobianExceptionalComponentNormalization
        equations hhomogeneous Q).parameterCount = 5 ∧
      Q.1.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) ∧
      Published.IsSaturatedByProjectiveIrrelevantIdeal Q.1 ∧
      Q.1.IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) < 6 := by
  have hmem := Finset.mem_filter.mp hQ
  have hprojective := exceptionalMinimalPrime_projectiveQualification
    equations hhomogeneous Q.1 Q.2 hmem.2.2
  refine ⟨hmem.2.1, hprojective.1, hprojective.2.1,
    hprojective.2.2, ?_⟩
  exact ringKrullDim_exceptionalMinimalPrime_lt_nat_of_determinant_notMem
    P Q.1 hP C hD Q.2 hPdim

/-- Any literal projective dimension-and-degree certificate for a residual
component necessarily has projective dimension four.  This is a numerical
consequence of its five-parameter finite normalization and the strict drop
from affine-cone dimension six; no Hilbert-polynomial existence theorem is
used here. -/
theorem projectiveDimension_eq_four_of_mem_topProjectiveJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (P : Ideal (MvPolynomial (Fin 13) ℚ)) [P.IsPrime]
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin 13) ℚ)) = P)
    (C : DepthSevenJacobianChartIndex equations)
    (hD : C.determinant ∉ P)
    (hPdim : ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ P) = 6)
    {Q : JacobianExceptionalComponent equations}
    (hQ : Q ∈ topProjectiveJacobianExceptionalComponents
      equations hhomogeneous)
    {r d : ℕ}
    (hprojective : Published.HasProjectiveDimensionDegree Q.1 r d) :
    r = 4 := by
  let D := jacobianExceptionalComponentNormalization
    equations hhomogeneous Q
  have hqualification :=
    mem_topProjectiveJacobianExceptionalComponents_qualification
      equations hhomogeneous P hP C hD hPdim hQ
  letI : Q.1.IsPrime := hqualification.2.2.2.1
  have hparameters : D.parameterCount = 5 := hqualification.1
  have hparameterLe : D.parameterCount ≤ r + 1 :=
    normalization_parameter_le_of_ringKrullDim_eq
      D.hom D.hom_injective D.hom_finite.to_isIntegral hprojective.1
  have hlower : 5 ≤ r + 1 := by simpa [hparameters] using hparameterLe
  have hupper' := hqualification.2.2.2.2
  rw [hprojective.1] at hupper'
  have hupper : r + 1 < 6 := by exact_mod_cast hupper'
  omega

/-- Exact count reduction.  Apart from the explicitly displayed residual
five-parameter projective components, the whole rank-at-most-six locus is
uniformly `O(T^4)` in every positive affine rescaling. -/
theorem exists_rankAtMostSix_card_le_fourthPower_add_topProjectiveComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (P : Ideal (MvPolynomial (Fin 13) ℚ)) [P.IsPrime]
    (hP : Ideal.span (equations : Set (MvPolynomial (Fin 13) ℚ)) = P)
    (C : DepthSevenJacobianChartIndex equations)
    (hD : C.determinant ∉ P)
    (hPdim : ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ P) = 6) :
    ∃ K : ℕ, ∀ (points : Finset (IntVector 13))
      (x₀ : IntVector 13) (m T : ℕ), 0 < m → 1 ≤ T →
      (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)).card ≤
        K * T ^ 4 +
          ∑ Q ∈ topProjectiveJacobianExceptionalComponents
              equations hhomogeneous,
            (points.filter fun z ↦
              (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
                affineIdealZeroLocus Q.1).card := by
  classical
  let top := topProjectiveJacobianExceptionalComponents
    equations hhomogeneous
  let D := fun Q : JacobianExceptionalComponent equations ↦
    jacobianExceptionalComponentNormalization equations hhomogeneous Q
  have hLow : ∀ Q : JacobianExceptionalComponent equations, Q ∉ top →
      ∃ K : ℕ, ∀ (points : Finset (IntVector 13))
        (x₀ : IntVector 13) (m T : ℕ), 0 < m → 1 ≤ T →
        (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
        (∀ z ∈ points,
          (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
            affineIdealZeroLocus Q.1) →
        points.card ≤ K * T ^ 4 := by
    intro Q hQtop
    have hparameterlt : (D Q).parameterCount < 6 :=
      jacobianExceptionalComponentNormalization_parameterCount_lt_six
        equations hhomogeneous P hP C hD hPdim Q
    by_cases hirr : Published.projectiveIrrelevantIdeal ℚ 12 ≤ Q.1
    · refine ⟨1, ?_⟩
      intro points x₀ m T hm hT _hbox hzero
      have hcard : points.card ≤ 1 := by
        have heq : points.filter (fun z ↦
            (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
              affineIdealZeroLocus Q.1) = points := by
          ext z
          simp only [Finset.mem_filter]
          exact and_iff_left_iff_imp.mpr fun hz ↦ hzero z hz
        rw [← heq]
        exact irrelevantComponent_affineDisplacement_card_le_one
          Q.1 hirr points x₀ m hm
      exact hcard.trans (by
        simpa only [one_mul] using one_le_pow_of_one_le' hT 4)
    · have hparam : (D Q).parameterCount ≤ 4 := by
        have hnotfive : (D Q).parameterCount ≠ 5 := by
          intro hfive
          apply hQtop
          simpa [top, topProjectiveJacobianExceptionalComponents] using
            (show (D Q).parameterCount = 5 ∧
                ¬ Published.projectiveIrrelevantIdeal ℚ 12 ≤ Q.1 from
              ⟨hfive, hirr⟩)
        omega
      exact exists_card_le_mul_fourthPower_of_parameterCount_le_four
        (D Q) hparam
  choose lowConstant hlowConstant using hLow
  let K : ℕ := ∑ Q : JacobianExceptionalComponent equations,
    if hQ : Q ∈ top then 0 else lowConstant Q hQ
  refine ⟨K, ?_⟩
  intro points x₀ m T hm hT hbox
  let componentPoints := fun Q : JacobianExceptionalComponent equations ↦
    points.filter fun z ↦
      (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
        affineIdealZeroLocus Q.1
  have hcover :
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)).card ≤
        ∑ Q : JacobianExceptionalComponent equations,
          (componentPoints Q).card := by
    have h := exceptionalDisplacement_card_le_sum_componentBounds
      equations points x₀ m
      (fun Q ↦ (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          affineIdealZeroLocus Q).card)
      (by intro Q hQ; exact le_rfl)
    rw [← Finset.sum_attach] at h
    simpa [componentPoints] using h
  have hlow : ∀ (Q : JacobianExceptionalComponent equations)
      (hQnot : Q ∉ top),
      (componentPoints Q).card ≤
        lowConstant Q hQnot * T ^ 4 := by
    intro Q hQnot
    apply hlowConstant Q hQnot (componentPoints Q) x₀ m T hm hT
    · intro z hz i
      exact hbox z (Finset.mem_filter.mp hz).1 i
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  have hsumLow :
      ∑ Q ∈ (Finset.univ.filter fun Q :
          JacobianExceptionalComponent equations ↦ Q ∉ top),
          (componentPoints Q).card ≤ K * T ^ 4 := by
    calc
      ∑ Q ∈ (Finset.univ.filter fun Q :
          JacobianExceptionalComponent equations ↦ Q ∉ top),
          (componentPoints Q).card ≤
          ∑ Q ∈ (Finset.univ.filter fun Q :
            JacobianExceptionalComponent equations ↦ Q ∉ top),
            (if hQ : Q ∈ top then 0 else lowConstant Q hQ) * T ^ 4 := by
              apply Finset.sum_le_sum
              intro Q hQ
              have hQnot : Q ∉ top := (Finset.mem_filter.mp hQ).2
              simpa [hQnot] using hlow Q hQnot
      _ ≤ K * T ^ 4 := by
        rw [← Finset.sum_mul]
        apply Nat.mul_le_mul_right
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro Q hQ; exact Finset.mem_univ Q)
          (by intros; positivity)
  have hsplit :
      (∑ Q : JacobianExceptionalComponent equations,
          (componentPoints Q).card) =
        (∑ Q ∈ top, (componentPoints Q).card) +
          ∑ Q ∈ (Finset.univ.filter fun Q :
            JacobianExceptionalComponent equations ↦ Q ∉ top),
              (componentPoints Q).card := by
    have hfilterTop :
        (Finset.univ.filter fun Q :
          JacobianExceptionalComponent equations ↦ Q ∈ top) = top := by
      ext Q
      simp
    calc
      (∑ Q : JacobianExceptionalComponent equations,
          (componentPoints Q).card) =
          (∑ Q ∈ (Finset.univ.filter fun Q :
              JacobianExceptionalComponent equations ↦ Q ∈ top),
                (componentPoints Q).card) +
            ∑ Q ∈ (Finset.univ.filter fun Q :
              JacobianExceptionalComponent equations ↦ Q ∉ top),
                (componentPoints Q).card := by
                  symm
                  exact Finset.sum_filter_add_sum_filter_not
                    (Finset.univ :
                      Finset (JacobianExceptionalComponent equations))
                    (fun Q ↦ Q ∈ top)
                    (fun Q ↦ (componentPoints Q).card)
      _ = _ := by rw [hfilterTop]
  rw [hsplit] at hcover
  exact hcover.trans <| by
    calc
      (∑ Q ∈ top, (componentPoints Q).card) +
          ∑ Q ∈ (Finset.univ.filter fun Q :
            JacobianExceptionalComponent equations ↦ Q ∉ top),
              (componentPoints Q).card ≤
        (∑ Q ∈ top, (componentPoints Q).card) + K * T ^ 4 :=
          Nat.add_le_add_left hsumLow _
      _ = K * T ^ 4 +
          ∑ Q ∈ top, (componentPoints Q).card := Nat.add_comm _ _

end

end TranslatedDepthSeven
