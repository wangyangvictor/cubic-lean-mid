import TranslatedDepthSeven.StrictRankAtMostSixDegreeSplit
import TranslatedDepthSeven.RationalProjectiveConePila

/-!
# The geometrically integral high-degree part of the strict low-rank cell

The finite residual component list is split literally according to geometric
primality.  On the geometrically prime high-degree components, the exact
rational-to-real packet bridge and Pila's theorem give the required
`33/8 + ε` estimate.  The complement is left as an explicit finite sum for
the Galois-frontier argument; no estimate for it is assumed here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance strictRankAtMostSixGeometricPilaClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- The certified degree-at-least-eight residual components which remain
prime after every coefficient-field extension. -/
noncomputable def geometricallyPrimeHighDegreeJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (highDegreeTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      GeometricallyPrimeMvPolynomialIdeal Q.1

/-- The complementary high-degree residual components. -/
noncomputable def nonGeometricallyPrimeHighDegreeJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (highDegreeTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      ¬ GeometricallyPrimeMvPolynomialIdeal Q.1

/-- The sharper final Pila list: geometrically prime certified components
of projective degree at least three. -/
noncomputable def geometricallyPrimeDegreeAtLeastThreeJacobianExceptionalComponents
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) :
    Finset (JacobianExceptionalComponent equations) :=
  (degreeAtLeastThreeTopProjectiveJacobianExceptionalComponents
    equations hhomogeneous).filter fun Q ↦
      GeometricallyPrimeMvPolynomialIdeal Q.1

/-- The two displayed lists form an exact partition of the high-degree
residual sum. -/
theorem sum_highDegreeTopProjectiveJacobianExceptionalComponents_eq_geometric_add
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (weight : JacobianExceptionalComponent equations → ℕ) :
    (∑ Q ∈ highDegreeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous, weight Q) =
      (∑ Q ∈ geometricallyPrimeHighDegreeJacobianExceptionalComponents
          equations hhomogeneous, weight Q) +
      ∑ Q ∈ nonGeometricallyPrimeHighDegreeJacobianExceptionalComponents
          equations hhomogeneous, weight Q := by
  classical
  simpa only [geometricallyPrimeHighDegreeJacobianExceptionalComponents,
    nonGeometricallyPrimeHighDegreeJacobianExceptionalComponents] using
    (Finset.sum_filter_add_sum_filter_not
      (highDegreeTopProjectiveJacobianExceptionalComponents
        equations hhomogeneous)
      (fun Q ↦ GeometricallyPrimeMvPolynomialIdeal Q.1) weight).symm

/-- Pila bounds the sum over all geometrically prime high-degree residual
components, uniformly in the translated box and modulus.  The component
list is fixed before the varying parameters, so its finitely many degrees
and Pila constants are absorbed in one constant. -/
theorem exists_geometricallyPrimeHighDegree_componentSum_le_pila
    (hPila : Pila1995TheoremA)
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
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
        (∑ Q ∈ geometricallyPrimeHighDegreeJacobianExceptionalComponents
            componentEquations hhomogeneous,
          (((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1).card : ℝ)) ≤
          ((geometricallyPrimeHighDegreeJacobianExceptionalComponents
              componentEquations hhomogeneous).card : ℝ) * C *
            ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
              ((33 / 8 : ℝ) + ε) := by
  classical
  let components :=
    geometricallyPrimeHighDegreeJacobianExceptionalComponents
      componentEquations hhomogeneous
  have hdegree : ∀ Q : {Q // Q ∈ components},
      ∃ d : ℕ, HasProjectiveDimensionDegree Q.1.1 4 d := by
    intro Q
    have hQhigh := (Finset.mem_filter.mp Q.2).1
    exact (Finset.mem_filter.mp hQhigh).2.2
  choose d hd using hdegree
  have hdEight : ∀ Q : {Q // Q ∈ components}, 8 ≤ d Q := by
    intro Q
    exact
      degree_ge_eight_of_mem_highDegreeTopProjectiveJacobianExceptionalComponents
        (Finset.mem_filter.mp Q.2).1 (hd Q)
  have hsource : ∀ Q : {Q // Q ∈ components},
      ∃ c : ℝ, 0 < c ∧
        ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
          ((((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1.1).card : ℝ) ≤
            c * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
              ((33 / 8 : ℝ) + ε)) := by
    intro Q
    obtain ⟨c, hc, hbound⟩ :=
      pila1995_finiteSet_rationalProjectiveFourfold_packet_degreeAtLeastEight
        hPila 12 (d Q) ε hε
    refine ⟨c, hc, ?_⟩
    intro p x₀ CF
    have hQhigh := (Finset.mem_filter.mp Q.2).1
    have hQtop := (Finset.mem_filter.mp hQhigh).1
    have hQgeom := (Finset.mem_filter.mp Q.2).2
    apply hbound (d Q) p.m (hdEight Q) le_rfl p.hm Q.1.1
      (hqualification Q.1 hQtop).2.1 hQgeom (hd Q) x₀
      ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ)
    · exact_mod_cast (by
        have := one_le_surfaceTangentNaturalSide p
        omega : 1 < 2 * surfaceTangentNaturalSide p + 1)
    · intro z hz i
      have hzbase := (Finset.mem_filter.mp hz).1
      have hcoord := depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
        p x₀ integralEquations CF hzbase i
      have hcast : |(z i : ℝ)| ≤
          (2 * surfaceTangentNaturalSide p : ℕ) := by
        simpa only [Int.cast_abs, Nat.cast_ofNat, Nat.cast_mul,
          Nat.cast_natAbs] using (by exact_mod_cast hcoord :
            ((z i).natAbs : ℝ) ≤
              (2 * surfaceTangentNaturalSide p : ℕ))
      have hsucc : ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) <
          ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega :
          2 * surfaceTangentNaturalSide p <
            2 * surfaceTangentNaturalSide p + 1)
      exact hcast.trans_lt hsucc
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  choose c hc hcbound using hsource
  let C : ℝ := 1 + ∑ Q : {Q // Q ∈ components}, c Q
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ Q : {Q // Q ∈ components}, c Q :=
      Finset.sum_nonneg fun Q _ ↦ (hc Q).le
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro p x₀ CF
  have hterm (Q : {Q // Q ∈ components}) : c Q ≤ C := by
    have hle : c Q ≤ ∑ R : {R // R ∈ components}, c R := by
      exact Finset.single_le_sum
        (fun R _ ↦ (hc R).le) (Finset.mem_univ Q)
    dsimp only [C]
    linarith
  calc
    (∑ Q ∈ geometricallyPrimeHighDegreeJacobianExceptionalComponents
        componentEquations hhomogeneous,
      (((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
          affineIdealZeroLocus Q.1).card : ℝ)) ≤
        ∑ Q : {Q // Q ∈ components},
          C * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
            ((33 / 8 : ℝ) + ε) := by
      rw [← Finset.sum_attach]
      apply Finset.sum_le_sum
      intro Q _hQ
      exact (hcbound Q p x₀ CF).trans
        (mul_le_mul_of_nonneg_right (hterm Q) (by positivity))
    _ = ((components.card : ℝ) * C) *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((33 / 8 : ℝ) + ε) := by
      simp [mul_assoc]
    _ = ((geometricallyPrimeHighDegreeJacobianExceptionalComponents
          componentEquations hhomogeneous).card : ℝ) * C *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((33 / 8 : ℝ) + ε) := rfl

/-- The final, sharper Pila estimate on all geometrically prime components
of projective degree at least three. -/
theorem exists_geometricallyPrimeDegreeAtLeastThree_componentSum_le_pila
    (hPila : Pila1995TheoremA)
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
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
        (∑ Q ∈
            geometricallyPrimeDegreeAtLeastThreeJacobianExceptionalComponents
              componentEquations hhomogeneous,
          (((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1).card : ℝ)) ≤
          ((geometricallyPrimeDegreeAtLeastThreeJacobianExceptionalComponents
              componentEquations hhomogeneous).card : ℝ) * C *
            ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
              ((13 / 3 : ℝ) + ε) := by
  classical
  let components :=
    geometricallyPrimeDegreeAtLeastThreeJacobianExceptionalComponents
      componentEquations hhomogeneous
  have hdegree : ∀ Q : {Q // Q ∈ components},
      ∃ d : ℕ, HasProjectiveDimensionDegree Q.1.1 4 d := by
    intro Q
    have hQthree := (Finset.mem_filter.mp Q.2).1
    exact (Finset.mem_filter.mp hQthree).2.2
  choose d hd using hdegree
  have hdThree : ∀ Q : {Q // Q ∈ components}, 3 ≤ d Q := by
    intro Q
    exact degree_ge_three_of_mem_degreeAtLeastThreeTopProjective
      (Finset.mem_filter.mp Q.2).1 (hd Q)
  have hsource : ∀ Q : {Q // Q ∈ components},
      ∃ c : ℝ, 0 < c ∧
        ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
          ((((depthSevenNormalizedDisplacementFinset
              p x₀ integralEquations CF).filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus Q.1.1).card : ℝ) ≤
            c * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
              ((13 / 3 : ℝ) + ε)) := by
    intro Q
    obtain ⟨c, hc, hbound⟩ :=
      pila1995_finiteSet_rationalProjectiveFourfold_packet_degreeAtLeastThree
        hPila 12 (d Q) ε hε
    refine ⟨c, hc, ?_⟩
    intro p x₀ CF
    have hQthree := (Finset.mem_filter.mp Q.2).1
    have hQtop := (Finset.mem_filter.mp hQthree).1
    have hQgeom := (Finset.mem_filter.mp Q.2).2
    apply hbound (d Q) p.m (hdThree Q) le_rfl p.hm Q.1.1
      (hqualification Q.1 hQtop).2.1 hQgeom (hd Q) x₀
      ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ)
    · exact_mod_cast (by
        have := one_le_surfaceTangentNaturalSide p
        omega : 1 < 2 * surfaceTangentNaturalSide p + 1)
    · intro z hz i
      have hzbase := (Finset.mem_filter.mp hz).1
      have hcoord := depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
        p x₀ integralEquations CF hzbase i
      have hcast : |(z i : ℝ)| ≤
          (2 * surfaceTangentNaturalSide p : ℕ) := by
        simpa only [Int.cast_abs, Nat.cast_ofNat, Nat.cast_mul,
          Nat.cast_natAbs] using (by exact_mod_cast hcoord :
            ((z i).natAbs : ℝ) ≤
              (2 * surfaceTangentNaturalSide p : ℕ))
      have hsucc : ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) <
          ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega :
          2 * surfaceTangentNaturalSide p <
            2 * surfaceTangentNaturalSide p + 1)
      exact hcast.trans_lt hsucc
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  choose c hc hcbound using hsource
  let C : ℝ := 1 + ∑ Q : {Q // Q ∈ components}, c Q
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ Q : {Q // Q ∈ components}, c Q :=
      Finset.sum_nonneg fun Q _ ↦ (hc Q).le
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro p x₀ CF
  have hterm (Q : {Q // Q ∈ components}) : c Q ≤ C := by
    have hle : c Q ≤ ∑ R : {R // R ∈ components}, c R := by
      exact Finset.single_le_sum
        (fun R _ ↦ (hc R).le) (Finset.mem_univ Q)
    dsimp only [C]
    linarith
  calc
    (∑ Q ∈
        geometricallyPrimeDegreeAtLeastThreeJacobianExceptionalComponents
          componentEquations hhomogeneous,
      (((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
          affineIdealZeroLocus Q.1).card : ℝ)) ≤
        ∑ Q : {Q // Q ∈ components},
          C * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
            ((13 / 3 : ℝ) + ε) := by
      rw [← Finset.sum_attach]
      apply Finset.sum_le_sum
      intro Q _hQ
      exact (hcbound Q p x₀ CF).trans
        (mul_le_mul_of_nonneg_right (hterm Q) (by positivity))
    _ = ((components.card : ℝ) * C) *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((13 / 3 : ℝ) + ε) := by
      simp [mul_assoc]
    _ = ((geometricallyPrimeDegreeAtLeastThreeJacobianExceptionalComponents
          componentEquations hhomogeneous).card : ℝ) * C *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((13 / 3 : ℝ) + ε) := rfl

end

end TranslatedDepthSeven
