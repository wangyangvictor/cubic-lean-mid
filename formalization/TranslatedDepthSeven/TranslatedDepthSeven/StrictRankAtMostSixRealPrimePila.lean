import TranslatedDepthSeven.StrictRankAtMostSixPilaClosure

/-!
# A Qbar-to-real bridge for the strict low-rank Pila step

This file proves that the strict low-rank argument does not need the
predicate saying that a rational ideal remains prime after *every* field
extension.  The only non-algebraic coefficient field used by the printed
Pila theorem is `ℝ`, so a direct Qbar-to-real prime bridge suffices.

-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance strictRankAtMostSixRealPrimePilaClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- The affine Hilbert certificate used by Pila needs only primeness after
the particular coefficient extension to `ℝ`. -/
theorem rationalProjectiveCone_packet_hasAffineHilbertDimensionDegree_of_realPrime
    {N r d m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hprimeReal :
      (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).IsPrime)
    (hprojective : HasProjectiveDimensionDegree I r d)
    (x₀ : IntVector (N + 1)) :
    HasAffineHilbertDimensionDegree
      ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
        (affinePolynomialChangeAlgEquiv
          (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
          (by exact_mod_cast hm.ne'))) (r + 1) d := by
  let IReal : Ideal (MvPolynomial (Fin (N + 1)) ℝ) :=
    I.map (MvPolynomial.map (algebraMap ℚ ℝ))
  have hhomogeneousReal : IReal.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℝ) := by
    exact isHomogeneous_map_mvPolynomialMap
      (algebraMap ℚ ℝ) I hhomogeneous
  have hprojectiveReal : HasProjectiveHilbertDimensionDegree IReal r d := by
    exact real_hasProjectiveHilbertDimensionDegree_of_rational I hprojective
  apply
    (hasAffineHilbertDimensionDegree_map_affinePolynomialChange_iff
      IReal (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne') (r + 1) d).2
  exact
    hasAffineHilbertDimensionDegree_of_homogeneous_hasProjectiveHilbertDimensionDegree
      IReal hhomogeneousReal hprimeReal r d hprojectiveReal

/-- Degree-at-least-three Pila for a finite rational point set, assuming
only that the displayed rational ideal becomes prime over `ℝ`. -/
theorem pila1995_finiteSet_rationalProjectiveFourfold_packet_degreeAtLeastThree_of_realPrime
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ), 3 ≤ d → d ≤ D → ∀ (_hm : 0 < m),
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).IsPrime →
          HasProjectiveDimensionDegree I 4 d →
          ∀ (x₀ : IntVector (N + 1)) (B : ℝ), 1 < B →
            ∀ X : Finset (IntVector (N + 1)),
              (∀ z ∈ X, ∀ i, |(z i : ℝ)| < B) →
              (∀ z ∈ X,
                (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
                  affineIdealZeroLocus I) →
              (X.card : ℝ) ≤ C * B ^ ((13 / 3 : ℝ) + epsilon) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_affineDimensionAtMostFive_degreeAtLeastThree_boundedDegree
      hPila (N + 1) D epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro d m hd hdD hm I hhomogeneous hprimeReal hprojective
    x₀ B hB X hXbox hXzero
  let J : Ideal (MvPolynomial (Fin (N + 1)) ℝ) :=
    ((I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
      (affinePolynomialChangeAlgEquiv
        (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
        (by exact_mod_cast hm.ne')))
  have hsubset : X ⊆ pilaIntegralPoints J B := by
    intro z hz
    exact intPoint_mem_pilaIntegralPoints_realPacket
      hm I x₀ z B (hXbox z hz) (hXzero z hz)
  calc
    (X.card : ℝ) ≤ ((pilaIntegralPoints J B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ C * B ^ ((13 / 3 : ℝ) + epsilon) := by
      apply hbound 5 d (by omega) hd hdD J
      · exact
          rationalProjectiveCone_packet_hasAffineHilbertDimensionDegree_of_realPrime
            hm I hhomogeneous hprimeReal hprojective x₀
      · exact hB

/-- The precise replacement for
`exists_qbarPrimeDegreeAtLeastThree_componentSum_le_pila`: its bridge
hypothesis concludes real primeness directly, without asserting primeness
after every coefficient-field extension. -/
theorem exists_qbarPrimeDegreeAtLeastThree_componentSum_le_pila_of_realPrime
    (hPila : Pila1995TheoremA)
    (hQbarToReal :
      ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).IsPrime)
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
  classical
  let components :=
    qbarPrimeDegreeAtLeastThreeTopComponents
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
              ((13 / 3 : ℝ) + epsilon)) := by
    intro Q
    obtain ⟨c, hc, hbound⟩ :=
      pila1995_finiteSet_rationalProjectiveFourfold_packet_degreeAtLeastThree_of_realPrime
        hPila 12 (d Q) epsilon hepsilon
    refine ⟨c, hc, ?_⟩
    intro p x₀ CF
    have hQthree := (Finset.mem_filter.mp Q.2).1
    have hQtop := (Finset.mem_filter.mp hQthree).1
    have hQbar := (Finset.mem_filter.mp Q.2).2
    apply hbound (d Q) p.m (hdThree Q) le_rfl p.hm Q.1.1
      (hqualification Q.1 hQtop).2.1 (hQbarToReal 13 Q.1.1 hQbar)
      (hd Q) x₀
      ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ)
    · exact_mod_cast (by
        have := one_le_surfaceTangentNaturalSide p
        omega : 1 < 2 * surfaceTangentNaturalSide p + 1)
    · intro z hz i
      have hzbase := (Finset.mem_filter.mp hz).1
      have hcoord :=
        depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
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
    (∑ Q ∈ qbarPrimeDegreeAtLeastThreeTopComponents
        componentEquations hhomogeneous,
      (((depthSevenNormalizedDisplacementFinset
          p x₀ integralEquations CF).filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
          affineIdealZeroLocus Q.1).card : ℝ)) ≤
        ∑ Q : {Q // Q ∈ components},
          C * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
            ((13 / 3 : ℝ) + epsilon) := by
      rw [← Finset.sum_attach]
      apply Finset.sum_le_sum
      intro Q _hQ
      exact (hcbound Q p x₀ CF).trans
        (mul_le_mul_of_nonneg_right (hterm Q) (by positivity))
    _ = ((components.card : ℝ) * C) *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((13 / 3 : ℝ) + epsilon) := by
      simp [mul_assoc]
    _ = ((qbarPrimeDegreeAtLeastThreeTopComponents
          componentEquations hhomogeneous).card : ℝ) * C *
        ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
          ((13 / 3 : ℝ) + epsilon) := rfl

/-- Full strict low-rank endpoint with the all-fields geometric-primality
criterion replaced by the exact Qbar-to-real implication used above. -/
theorem exists_strictRankAtMostSix_card_le_thirteenThirds_of_qbarToReal
    (hPila : Pila1995TheoremA)
    (hHilbertSerre :
      ∀ (N r : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
        I.IsPrime →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        ¬ projectiveIrrelevantIdeal ℚ N ≤ I →
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) = r + 1 →
        ∃ d : ℕ, HasProjectiveDimensionDegree I r d)
    (hQbarToReal :
      ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).IsPrime)
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
  obtain ⟨componentEquations, hhomogeneous, _chart, K₀, hspan,
      _hdeterminant, hqualification, hbase⟩ :=
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
    exists_qbarPrimeDegreeAtLeastThree_componentSum_le_pila_of_realPrime
      hPila hQbarToReal equations componentEquations
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
