import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffective
import TranslatedDepthSeven.QuantitativePrefixRationalLineLedger

/-!
# Closing the rational-line remainder in the effective surface count

The degree-effective surface count leaves the literal union of rational
degree-one components.  Every active occurrence is a complete affine line
with primitive integral direction.  Consequently its direction height is
positive.  Specializing the high/low ledger at cutoff zero makes the low
catalogue empty and counts the entire rational-line union by the elementary
one-dimensional congruence estimate.

The final theorem inserts this count into the fixed-surface prefix assembly.
The terminal degrees may vary with height; their total occurrence mass is
bounded by the square of the current Bezout degree `d * L`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 14000000
set_option synthInstance.maxHeartbeats 700000

local instance effectiveSurfaceLineLedgerPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The rational projective line ledger at cutoff zero.  Since every active
line has primitive nonzero direction, there is no low-direction remainder. -/
theorem exists_quantitativePrefixPersistent_rationalLineCount
    {d : ℕ}
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ I)
    (u : IntVector 3) (m : ℕ) (hm : 0 < m)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (B : ℝ)
    (hbox : ∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
      |(integralAffineMap u z m i : ℝ)| ≤ B) :
    let J := fun o : {o // o ∈ active} ↦
      rationalAffineChartIntersectionIdeal I (terminalCut o.1)
    let Y := fun o : {o // o ∈ active} ↦
      quantitativePrefixPersistentAffineCell u m cell o.1
    ∃ (base direction : RationalLinearOccurrence J → IntVector 3)
      (parameter : RationalLinearOccurrence J → IntVector 3 → ℤ),
      (∀ o ∈ activeRationalLinearOccurrences J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑(rationalLinearOccurrencePoints J Y o) : Set (IntVector 3)) ∧
        (∀ z ∈ rationalLinearOccurrencePoints J Y o,
          z = fun i ↦ base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℚ ↦
            fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ∧
        Set.range (fun t : ℚ ↦
          fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ⊆
            affineIdealZeroLocus (J o.1)) ∧
      Fintype.card (RationalLinearOccurrence J) ≤
        ∑ o ∈ active, d * terminalDegree o ∧
      (quantitativePrefixPersistentRationalLinearPointUnion
          I active terminalCut u m cell).card ≤
        (∑ o ∈ active, d * terminalDegree o) +
        (∑ o ∈ active, d * terminalDegree o) *
          (1 + ⌈2 * B⌉₊ / m) := by
  classical
  dsimp only
  let J := fun o : {o // o ∈ active} ↦
    rationalAffineChartIntersectionIdeal I (terminalCut o.1)
  let Y := fun o : {o // o ∈ active} ↦
    quantitativePrefixPersistentAffineCell u m cell o.1
  obtain ⟨base, direction, parameter, hfull, hoccurrence, hledger⟩ :=
    exists_quantitativePrefixPersistent_rationalProjectiveLineLedger
      I hprime hhom hdegree active terminalDegree terminalCut hterminal
        u m hm cell B hbox 0
  have hlow : activeRationalLowProjectiveDirections J Y direction 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro q hq
    obtain ⟨o, ho, _hoq⟩ := Finset.mem_image.mp hq
    have hoData := Finset.mem_filter.mp ho
    obtain ⟨i, hi, hheight⟩ := (hfull o hoData.1).1.exists_natAbs_eq_directionHeight
    have hpos : 0 < directionHeight (direction o) := by
      rw [← hheight]
      exact Int.natAbs_pos.mpr hi
    omega
  have hlowUnion : activeRationalExactLowUnion J Y
      (activeRationalLowProjectiveDirections J Y direction 0)
      (rationalOccurrenceProjectiveDirection J direction) = ∅ := by
    simp [hlow, activeRationalExactLowUnion]
  refine ⟨base, direction, parameter, hfull, hoccurrence, ?_⟩
  rw [hlowUnion] at hledger
  simpa using hledger

/-- The closed natural-number cost of all rational line occurrences after
the terminal cutting degrees have been replaced by their uniform majorant. -/
def quantitativePrefixEffectiveLineOccurrenceMass
    (d b H Baux : ℕ) (η a : ℝ) : ℕ :=
  (d * (b + quantitativePrefixUniformBlockDegree H Baux η a)) ^ 2

/-- Close the rational line union in the effective global-edge assembly.
The only external counting input is the degree-effective affine curve bound;
all line counting and all degree-mass estimates are internal. -/
theorem exists_uniform_quantitativePrefixSurfaceCount_effective_closedLines
    (hCurve : CDHNV2025Corollary22) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b H Baux Bpoint : ℕ} {η a : ℝ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (F : MvPolynomial (Fin 4) ℤ)
        (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ) (hm : 0 < m)
        (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ)
        (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
        (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ)
        (z₀ : IntVector 3),
      z₀ ∈ X →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ v,
        ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
          (1 + (Baux : ℝ) ^ a /
            (PrimeSubsetPrefix.modulus v : ℝ))) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        ∀ ρ ∈ occupiedIntegralResidues
          (PrimeSubsetPrefix.modulus v) X,
          (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
            auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        ∀ z ∈ X, MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m z i : ℚ))
            (auxiliary v (integralResidueVector z)) = 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ i,
        (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
          (MvPolynomial.pderiv i
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      1 ≤ Bpoint →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ (Bpoint : ℝ)) →
      let root := PrimeSubsetPrefix.root P depth
      let G₀ := auxiliary root (integralResidueVector z₀)
      let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
        u m X allowed
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      ∃ (representative : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          IntVector 3)
        (terminalVertex : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          PrimeSubsetPrefix.Vertex P depth)
        (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
        (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          MvPolynomial (Fin 4) ℚ),
        (∀ o ∈ active, representative o ∈ cell o) ∧
        (∀ o ∈ active,
          terminalVertex o ∈ PrimeSubsetPrefix.survivingVertices P
            (allowed (representative o)) depth ∧
          (terminalVertex o).1.card = depth) ∧
        (∀ o,
          terminalDegree o = b + blockDegree (terminalVertex o) ∧
          terminalCut o = auxiliary (terminalVertex o)
            (integralResidueVector (representative o))) ∧
        active.card ≤ d * (b + blockDegree root) ∧
        let J := fun o : {o // o ∈ active} ↦
          rationalAffineChartIntersectionIdeal
            (finiteEquationIdeal sourceEquations) (terminalCut o.1)
        let Y := fun o : {o // o ∈ active} ↦
          quantitativePrefixPersistentAffineCell u m cell o.1
        ∃ (base direction : RationalLinearOccurrence J → IntVector 3)
          (parameter : RationalLinearOccurrence J → IntVector 3 → ℤ),
          (∀ o ∈ activeRationalLinearOccurrences J Y,
            PrimitiveDirection (direction o) ∧
            Set.InjOn (parameter o)
              (↑(rationalLinearOccurrencePoints J Y o) : Set (IntVector 3)) ∧
            (∀ z ∈ rationalLinearOccurrencePoints J Y o,
              z = fun i ↦ base o i + parameter o z * direction o i) ∧
            affineIdealZeroLocus o.2.1 =
              Set.range (fun t : ℚ ↦
                fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ∧
            Set.range (fun t : ℚ ↦
              fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ⊆
                affineIdealZeroLocus (J o.1)) ∧
          Fintype.card (RationalLinearOccurrence J) ≤
            quantitativePrefixEffectiveLineOccurrenceMass d b H Baux η a ∧
          (X.card : ℝ) ≤
            (((PrimeSubsetPrefix.directedEdges P depth).card *
              quantitativePrefixEdgeMajorant
                F P depth d b H Baux η a : ℕ) : ℝ) +
            ((quantitativePrefixEffectiveLineOccurrenceMass
                d b H Baux η a +
              quantitativePrefixEffectiveLineOccurrenceMass
                d b H Baux η a *
                (1 + ⌈2 * (Bpoint : ℝ)⌉₊ / m) : ℕ) : ℝ) +
            quantitativePrefixEffectiveCurveResidual
              C d b H Baux Bpoint η a := by
  classical
  obtain ⟨C, hC, hassembly⟩ :=
    exists_uniform_quantitativePrefixSurfaceCountAssembly_effective_globalEdgeBound
      hCurve
  refine ⟨C, hC, ?_⟩
  intro d b H Baux Bpoint η a sourceEquations hprime hgeometricPrime hhom
    hdegree F P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hP
    hPm hallowed hroom hblock hauxiliary hauxZero hsource hzero hsmooth
    hBpoint hbox
  dsimp only
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    u m X allowed
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  let L := b + quantitativePrefixUniformBlockDegree H Baux η a
  obtain ⟨representative, terminalVertex, terminalDegree, terminalCut,
      hrepresentative, hterminalVertex, hterminalDefs, hactiveCard, hcount⟩ :=
    hassembly sourceEquations hprime hgeometricPrime hhom hdegree F P depth
      u m hm X allowed blockDegree auxiliary z₀ hz₀ hP hPm hallowed hroom
      hblock hauxiliary hauxZero hsource hzero hsmooth hBpoint hbox
  have hrepresentativeX : ∀ o ∈ active, representative o ∈ X := by
    intro o ho
    have hmem := hrepresentative o ho
    exact (Finset.mem_filter.mp hmem).1
  have hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ finiteEquationIdeal sourceEquations := by
    intro o ho
    have hρ : integralResidueVector (representative o) ∈
        occupiedIntegralResidues
          (PrimeSubsetPrefix.modulus (terminalVertex o)) X := by
      rw [occupiedIntegralResidues_eq_image_integralResidueVector]
      exact Finset.mem_image.mpr ⟨representative o,
        hrepresentativeX o ho, rfl⟩
    have haux := hauxiliary (terminalVertex o)
      (integralResidueVector (representative o)) hρ
    rw [(hterminalDefs o).1, (hterminalDefs o).2]
    exact haux
  obtain ⟨base, direction, parameter, hfull, hoccurrence, hlineCount⟩ :=
    exists_quantitativePrefixPersistent_rationalLineCount
      (finiteEquationIdeal sourceEquations) hprime hhom hdegree active
        terminalDegree terminalCut hterminal u m hm cell (Bpoint : ℝ)
        (by
          intro o ho z hz i
          apply hbox z
          · change z ∈ cell o at hz
            exact (Finset.mem_filter.mp hz).1
          )
  have hdegreeCap : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      b + blockDegree v ≤ L := by
    intro v
    exact Nat.add_le_add_left
      (blockDegree_le_quantitativePrefixUniformBlockDegree
        hP blockDegree hblock v) b
  have hterminalDegree : ∀ o ∈ active, terminalDegree o ≤ L := by
    intro o _ho
    rw [(hterminalDefs o).1]
    exact hdegreeCap (terminalVertex o)
  have hdegreeSum : (∑ o ∈ active, d * terminalDegree o) ≤
      quantitativePrefixEffectiveLineOccurrenceMass d b H Baux η a := by
    have hsum : (∑ o ∈ active, d * terminalDegree o) ≤
        active.card * (d * L) := by
      calc
        (∑ o ∈ active, d * terminalDegree o) ≤
            ∑ _o ∈ active, d * L := by
          apply Finset.sum_le_sum
          intro o ho
          exact Nat.mul_le_mul_left d (hterminalDegree o ho)
        _ = active.card * (d * L) := by simp
    have hactive : active.card ≤ d * L :=
      hactiveCard.trans (Nat.mul_le_mul_left d (hdegreeCap root))
    rw [quantitativePrefixEffectiveLineOccurrenceMass, pow_two]
    exact hsum.trans (Nat.mul_le_mul_right (d * L) hactive)
  have hoccurrence' : Fintype.card (RationalLinearOccurrence
      (fun o : {o // o ∈ active} ↦
        rationalAffineChartIntersectionIdeal
          (finiteEquationIdeal sourceEquations) (terminalCut o.1))) ≤
      quantitativePrefixEffectiveLineOccurrenceMass d b H Baux η a :=
    hoccurrence.trans hdegreeSum
  have hlineCount' :
      (quantitativePrefixPersistentRationalLinearPointUnion
          (finiteEquationIdeal sourceEquations) active terminalCut
            u m cell).card ≤
        quantitativePrefixEffectiveLineOccurrenceMass d b H Baux η a +
        quantitativePrefixEffectiveLineOccurrenceMass d b H Baux η a *
          (1 + ⌈2 * (Bpoint : ℝ)⌉₊ / m) := by
    exact hlineCount.trans (Nat.add_le_add hdegreeSum
      (Nat.mul_le_mul_right _ hdegreeSum))
  have hlineCountReal :
      (((quantitativePrefixPersistentRationalLinearPointUnion
          (finiteEquationIdeal sourceEquations) active terminalCut
            u m cell).card : ℕ) : ℝ) ≤
        ((quantitativePrefixEffectiveLineOccurrenceMass d b H Baux η a +
          quantitativePrefixEffectiveLineOccurrenceMass d b H Baux η a *
            (1 + ⌈2 * (Bpoint : ℝ)⌉₊ / m) : ℕ) : ℝ) := by
    exact_mod_cast hlineCount'
  refine ⟨representative, terminalVertex, terminalDegree, terminalCut,
    hrepresentative, hterminalVertex, hterminalDefs, hactiveCard, ?_⟩
  dsimp only
  refine ⟨base, direction, parameter, hfull, hoccurrence', ?_⟩
  linarith

/-! ## Direct determinant-choice endpoint -/

/-- The closed conclusion produced by one quantitative prefix auxiliary
family.  This named predicate keeps the direct fixed-surface theorem
readable while retaining the literal line parametrizations and the fully
explicit edge, line, and nonlinear costs. -/
def QuantitativePrefixEffectiveClosedLineCertificate
    {d b H Baux Bpoint : ℕ} {η a : ℝ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (F : MvPolynomial (Fin 4) ℤ)
    (P : Finset ℕ) (depth : ℕ)
    (u : IntVector 3) (m : ℕ)
    (X : Finset (IntVector 3))
    (allowed : IntVector 3 → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (z₀ : IntVector 3) (C : ℝ) : Prop :=
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    u m X allowed
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  ∃ (representative : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      IntVector 3)
    (terminalVertex : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      PrimeSubsetPrefix.Vertex P depth)
    (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ),
    (∀ o ∈ active, representative o ∈ cell o) ∧
    (∀ o ∈ active,
      terminalVertex o ∈ PrimeSubsetPrefix.survivingVertices P
        (allowed (representative o)) depth ∧
      (terminalVertex o).1.card = depth) ∧
    (∀ o,
      terminalDegree o = b + blockDegree (terminalVertex o) ∧
      terminalCut o = auxiliary (terminalVertex o)
        (integralResidueVector (representative o))) ∧
    active.card ≤ d * (b + blockDegree root) ∧
    let J := fun o : {o // o ∈ active} ↦
      rationalAffineChartIntersectionIdeal
        (finiteEquationIdeal sourceEquations) (terminalCut o.1)
    let Y := fun o : {o // o ∈ active} ↦
      quantitativePrefixPersistentAffineCell u m cell o.1
    ∃ (base direction : RationalLinearOccurrence J → IntVector 3)
      (parameter : RationalLinearOccurrence J → IntVector 3 → ℤ),
      (∀ o ∈ activeRationalLinearOccurrences J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑(rationalLinearOccurrencePoints J Y o) : Set (IntVector 3)) ∧
        (∀ z ∈ rationalLinearOccurrencePoints J Y o,
          z = fun i ↦ base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℚ ↦
            fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ∧
        Set.range (fun t : ℚ ↦
          fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ⊆
            affineIdealZeroLocus (J o.1)) ∧
      Fintype.card (RationalLinearOccurrence J) ≤
        quantitativePrefixEffectiveLineOccurrenceMass d b H Baux η a ∧
      (X.card : ℝ) ≤
        (((PrimeSubsetPrefix.directedEdges P depth).card *
          quantitativePrefixEdgeMajorant
            F P depth d b H Baux η a : ℕ) : ℝ) +
        ((quantitativePrefixEffectiveLineOccurrenceMass
            d b H Baux η a +
          quantitativePrefixEffectiveLineOccurrenceMass
            d b H Baux η a *
            (1 + ⌈2 * (Bpoint : ℝ)⌉₊ / m) : ℕ) : ℝ) +
        quantitativePrefixEffectiveCurveResidual
          C d b H Baux Bpoint η a

/-- Predicate-form restatement of the closed uniform assembly, used by the
direct determinant-choice theorem below. -/
theorem exists_uniform_quantitativePrefixSurfaceCount_effective_closedLines_certificate
    (hCurve : CDHNV2025Corollary22) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b H Baux Bpoint : ℕ} {η a : ℝ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (F : MvPolynomial (Fin 4) ℤ)
        (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ) (hm : 0 < m)
        (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ)
        (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
        (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ)
        (z₀ : IntVector 3),
      z₀ ∈ X →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ v,
        ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
          (1 + (Baux : ℝ) ^ a /
            (PrimeSubsetPrefix.modulus v : ℝ))) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        ∀ ρ ∈ occupiedIntegralResidues
          (PrimeSubsetPrefix.modulus v) X,
          (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
            auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        ∀ z ∈ X, MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m z i : ℚ))
            (auxiliary v (integralResidueVector z)) = 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ i,
        (MvPolynomial.eval (fun j => u j + (m : ℤ) * z j)
          (MvPolynomial.pderiv i
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      1 ≤ Bpoint →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ (Bpoint : ℝ)) →
      QuantitativePrefixEffectiveClosedLineCertificate
        (d := d) (b := b) (H := H) (Baux := Baux) (Bpoint := Bpoint)
        (η := η) (a := a)
        sourceEquations F P depth u m X allowed blockDegree auxiliary z₀ C := by
  obtain ⟨C, hC, hclosed⟩ :=
    exists_uniform_quantitativePrefixSurfaceCount_effective_closedLines hCurve
  refine ⟨C, hC, ?_⟩
  intro d b H Baux Bpoint η a sourceEquations hprime hgeometricPrime hhom
    hdegree F P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hP
    hPm hallowed hroom hblock hauxiliary hauxZero hsource hzero hsmooth
    hBpoint hbox
  exact hclosed sourceEquations hprime hgeometricPrime hhom hdegree F P depth
    u m hm X allowed blockDegree auxiliary z₀ hz₀ hP hPm hallowed hroom
    hblock hauxiliary hauxZero hsource hzero hsmooth hBpoint hbox

/-- Direct fixed-surface endpoint: construct the determinant auxiliaries and
immediately close every rational degree-one component by the primitive-line
ledger.  No fixed terminal-degree cap and no line-counting hypothesis remain. -/
theorem exists_fixedSurface_quantitativePrefixSurfaceCount_effective_closedLines
    (hCurve : CDHNV2025Corollary22)
    {d : ℕ} (hd : 0 < d)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hchart : MvPolynomial.X 0 ∉ finiteEquationIdeal sourceEquations)
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (Kred : ℝ) (hKred : 1 ≤ Kred) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η)
    (ha : Real.sqrt Kred / Real.sqrt (d : ℝ) < a) :
    ∃ b D A H₀ : ℕ, ∃ Cdet Ccurve : ℝ,
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ Cdet ∧ 0 < Ccurve ∧
      ∀ (P : Finset ℕ) (depth H Baux Bpoint m Dex : ℕ)
        (u : IntVector 3) (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ) (z₀ : IntVector 3),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      H₀ ≤ H → 1 ≤ Baux →
      0 < Dex → Dex ≤ H ^ Aex → m * primeProduct P ∣ Dex →
      m ≠ 0 →
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            Kred * (p : ℝ) ^ 2) →
      (∀ z ∈ X, ∀ i,
        (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
      (∀ z ∈ X, ∀ i, (z i).natAbs ≤ Baux) →
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∃ v, MvPolynomial.eval
        (fun i => u i + (m : ℤ) * z i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ v,
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
          (MvPolynomial.pderiv v
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      1 ≤ Bpoint →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ (Bpoint : ℝ)) →
      ∃ blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ,
        ∃ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ,
        (∀ v : PrimeSubsetPrefix.Vertex P depth,
          0 < blockDegree v ∧
          ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ η *
            (1 + (Baux : ℝ) ^ a /
              (PrimeSubsetPrefix.modulus v : ℝ)) ∧
          (∀ ρ ∈ occupiedIntegralResidues
              (PrimeSubsetPrefix.modulus v) X,
            (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
              auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0) ∧
        QuantitativePrefixEffectiveClosedLineCertificate
          (d := d) (b := b) (H := H) (Baux := Baux) (Bpoint := Bpoint)
          (η := η) (a := a)
          sourceEquations F P depth u m X allowed blockDegree auxiliary z₀
            Ccurve := by
  classical
  obtain ⟨Ccurve, hCcurve, hassembly⟩ :=
    exists_uniform_quantitativePrefixSurfaceCount_effective_closedLines_certificate
      hCurve
  obtain ⟨b, D, A, H₀, Cdet, hD, hA, hH₀, hCdet, hchoice⟩ :=
    exists_fixedSurface_quantitative_prefixAuxiliaryChoice
      hd (finiteEquationIdeal sourceEquations) hprime hhom hchart hdegree
        F Kred hKred Aex η a hη ha
  refine ⟨b, D, A, H₀, Cdet, Ccurve,
    hD, hA, hH₀, hCdet, hCcurve, ?_⟩
  intro P depth H Baux Bpoint m Dex u X allowed z₀ hP hPm hH hBaux
    hDex hDexHeight hmPDex hm hz₀ hallowed hroom hpoints hheight hboxAux
    hzero hgradient hsmooth hsource hBpoint hboxPoint
  obtain ⟨blockDegree, auxiliary, hauxiliary⟩ :=
    hchoice P depth H Baux m Dex u X hP hPm hH hBaux hDex hDexHeight
      hmPDex hm hpoints hheight hboxAux hzero hgradient hsmooth
  have hcertificate := hassembly sourceEquations hprime hgeometricPrime hhom
    hdegree F P depth u m (Nat.pos_of_ne_zero hm) X allowed blockDegree
      auxiliary z₀ hz₀ hP hPm hallowed hroom
      (fun v ↦ (hauxiliary v).2.1)
      (fun v ↦ (hauxiliary v).2.2.1)
      (fun v ↦ (hauxiliary v).2.2.2) hsource hzero hsmooth
      hBpoint hboxPoint
  exact ⟨blockDegree, auxiliary, hauxiliary, hcertificate⟩

end

end TranslatedDepthSeven
