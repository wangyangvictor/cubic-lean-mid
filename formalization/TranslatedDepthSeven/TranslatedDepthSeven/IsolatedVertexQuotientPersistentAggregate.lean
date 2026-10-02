import TranslatedDepthSeven.IsolatedVertexQuotientPersistentPila

/-!
# The aggregate persistent isolated-vertex quotient contribution

The surviving modulus in the deleted-certificate reservoir is pointwise:
there is no reason for one modulus to survive at every rational point on a
fixed persistent curve.  This file therefore keeps the literal source
modulus.  A record consists of a modulus, one occupied residue, and one
retained curve from the static node list at that residue.  The record list
is a `Finset`, so identical triples are deduplicated; its union of point
cells is only used as a cover, so points surviving at several moduli cause
no hidden disjointness assumption.

The last theorem combines the uniform Galois/Pila dichotomy with the
five-dimensional occupied-residue estimate.  It is the actual aggregate
persistent branch, rather than a bound for one assumed cell.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000

local instance isolatedVertexQuotientPersistentAggregatePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Two small reusable bookkeeping lemmas -/

/-- The degree in a projective Hilbert certificate is unique. -/
theorem projectiveDegree_eq_of_hasProjectiveDimensionDegree
    {K : Type*} [Field K] {N r d e : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) K)}
    (hd : HasProjectiveDimensionDegree I r d)
    (he : HasProjectiveDimensionDegree I r e) :
    d = e := by
  rcases hd with ⟨_hdimd, _hdpos, P, _hPdegree, hPleading,
    kP, hP⟩
  rcases he with ⟨_hdime, _hepos, Q, _hQdegree, hQleading,
    kQ, hQ⟩
  let shift : ℕ := max kP kQ
  let values : ℕ → ℚ := fun n ↦ ((n + shift : ℕ) : ℚ)
  have hvaluesInjective : Function.Injective values := by
    intro a b hab
    have habNat : a + shift = b + shift := by
      change (((a + shift : ℕ) : ℚ)) = ((b + shift : ℕ) : ℚ) at hab
      exact_mod_cast hab
    omega
  have hinfinite : Set.Infinite (Set.range values) :=
    Set.infinite_range_of_injective hvaluesInjective
  have heval : Set.range values ⊆ {x | P.eval x = Q.eval x} := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    have hPk : kP ≤ n + shift := by
      dsimp only [shift]
      omega
    have hQk : kQ ≤ n + shift := by
      dsimp only [shift]
      omega
    calc
      P.eval (((n + shift : ℕ) : ℚ)) =
          (Module.finrank K
            (projectiveHilbertPiece K N I (n + shift)) : ℚ) :=
        (hP (n + shift) hPk).symm
      _ = Q.eval (((n + shift : ℕ) : ℚ)) := hQ (n + shift) hQk
  have hPQ : P = Q :=
    Polynomial.eq_of_infinite_eval_eq P Q (hinfinite.mono heval)
  have hleading : (d : ℚ) / r.factorial = (e : ℚ) / r.factorial := by
    rw [← hPleading, ← hQleading, hPQ]
  have hfactorial : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp [hfactorial] at hleading
  exact_mod_cast hleading

/-- Every regular quotient point has a denominator-compatible surviving
ambient modulus.  This is the pointwise source-modulus witness used below. -/
theorem exists_denominatorCompatibleSurvivingModulus_of_mem_regular
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H)
    {Ppool : Finset ℕ} {k : ℕ}
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k))
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations) :
    ∃ q : ReservoirModulus Ppool k,
      survivesTwoCertificates q ((p.m : ℤ) * model.denominator)
        (isolatedVertexQuotientSelectedCertificateValue
          U p sourceEquations CF hx₀ lowerEquations w) := by
  have hfixedNe : (p.m : ℤ) * model.denominator ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (Nat.ne_of_gt p.one_le_m)
    · exact model.denominator_ne_zero
  have hfixedSize :
      ((((p.m : ℤ) * model.denominator).natAbs : ℕ) : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations :=
    isolatedVertexQuotient_scale_mul_modelDenominator_height
      U p lowerEquations model hdenominator
  have hcertificateNe :=
    isolatedVertexQuotientSelectedCertificateValue_ne_zero
      U p sourceEquations CF hx₀ lowerEquations hw
  have hcertificateSize :=
    isolatedVertexQuotientSelectedCertificateValue_height
      U p sourceEquations CF hx₀ lowerEquations hw
  obtain ⟨q⟩ := hsurvival ((p.m : ℤ) * model.denominator)
    (isolatedVertexQuotientSelectedCertificateValue
      U p sourceEquations CF hx₀ lowerEquations w)
    hfixedNe hcertificateNe hfixedSize hcertificateSize
  exact ⟨certificateAllowedTwoModulusEmbedding hP
      ((p.m : ℤ) * model.denominator)
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w) q,
    certificateAllowedTwoModulusEmbedding_survives hP
      ((p.m : ℤ) * model.denominator)
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w) q⟩

/-! ## Literal source-modulus records -/

/-- One persistent record over a fixed source modulus. -/
structure IsolatedVertexQuotientPersistentSourceRecord (q : ℕ) where
  residue : Fin 12 → ZMod q
  component : Ideal (MvPolynomial (Fin 13) Qbar)

/-- Occupied persistent records over one source modulus.  Besides belonging
to the static node list, the retained curve is required to have a nonempty
literal persistent/surviving residue cell. -/
def occupiedIsolatedVertexQuotientPersistentSourceRecords
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    Finset (IsolatedVertexQuotientPersistentSourceRecord q.1) := by
  classical
  exact (occupiedIntegralResidues q.1
    (isolatedVertexQuotientPointFinset
      U p x₀ sourceEquations CF)).biUnion fun rho ↦
    ((isolatedVertexQuotientStaticNodeComponentsAtResidue
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q rho).filter fun Q ↦
      (isolatedVertexQuotientPersistentSurvivingResidueCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho).Nonempty).image fun Q ↦
        { residue := rho, component := Q }

@[simp]
theorem mem_occupiedIsolatedVertexQuotientPersistentSourceRecords_iff
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k)
    (record : IsolatedVertexQuotientPersistentSourceRecord q.1) :
    record ∈ occupiedIsolatedVertexQuotientPersistentSourceRecords
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q ↔
      record.residue ∈ occupiedIntegralResidues q.1
        (isolatedVertexQuotientPointFinset
          U p x₀ sourceEquations CF) ∧
      record.component ∈
        isolatedVertexQuotientStaticNodeComponentsAtResidue
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower q record.residue ∧
      (isolatedVertexQuotientPersistentSurvivingResidueCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower record.component q record.residue).Nonempty := by
  classical
  constructor
  · intro hrecord
    obtain ⟨rho, hrho, himage⟩ := Finset.mem_biUnion.mp hrecord
    obtain ⟨Q, hQfiltered, hEq⟩ := Finset.mem_image.mp himage
    obtain ⟨hQstatic, hQnonempty⟩ := Finset.mem_filter.mp hQfiltered
    cases hEq
    exact ⟨hrho, hQstatic, hQnonempty⟩
  · rintro ⟨hrho, hQstatic, hQnonempty⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨record.residue, hrho, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨record.component,
      Finset.mem_filter.mpr ⟨hQstatic, hQnonempty⟩, ?_⟩
    cases record
    rfl

/-- The literal persistent term in the denominator-compatible static cover,
with duplicates between labels removed by `biUnion`. -/
def isolatedVertexQuotientDenominatorCompatiblePersistentUnion
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1) : Finset (IntVector 12) :=
  (occurringIsolatedVertexQuotientDenominatorCompatibleLabels
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      Ppool k hqpos hqsf hqlower).biUnion fun o ↦
    isolatedVertexQuotientDenominatorCompatiblePersistentCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower o

/-- Every point in the aggregate persistent term belongs to a literal
source-modulus/residue/curve record cell. -/
theorem isolatedVertexQuotientDenominatorCompatiblePersistentUnion_subset_sourceRecordUnion
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k)) :
    isolatedVertexQuotientDenominatorCompatiblePersistentUnion
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          Ppool k hqpos hqsf hqlower ⊆
      (Finset.univ : Finset (ReservoirModulus Ppool k)).biUnion fun q ↦
        (occupiedIsolatedVertexQuotientPersistentSourceRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q).biUnion fun record ↦
          isolatedVertexQuotientPersistentSurvivingResidueCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower record.component q record.residue := by
  classical
  intro w hw
  obtain ⟨o, _ho, hwcell⟩ := Finset.mem_biUnion.mp hw
  have hwdata := Finset.mem_filter.mp hwcell
  obtain ⟨Q, hQ⟩ := Option.ne_none_iff_exists'.1 hwdata.2.1
  rw [hQ] at hwcell hwdata
  obtain ⟨q, hqSurvives⟩ :=
    exists_denominatorCompatibleSurvivingModulus_of_mem_regular
      U p sourceEquations CF hx₀ lowerEquations model hdenominator
        hP hsurvival hwdata.1
  let rho : Fin 12 → ZMod q.1 := integralResidueVector w
  have hwPoint := (mem_isolatedVertexRegularQuotientPointFinset_iff
    U p x₀ sourceEquations CF lowerEquations w).1 hwdata.1 |>.1
  have hlabel : isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower w q = some Q := hwdata.2.2 q hqSurvives
  have hstatic :=
    (isolatedVertexQuotientStaticComponentLabel_eq_some_staticNode_spec
      U p sourceEquations CF x₀ lowerEquations hquotient
        hqpos hqsf hqlower w q Q hlabel).1
  have hrho : rho ∈ occupiedIntegralResidues q.1
      (isolatedVertexQuotientPointFinset
        U p x₀ sourceEquations CF) :=
    Finset.mem_image.mpr ⟨w, hwPoint, rfl⟩
  have hwsource : w ∈
      isolatedVertexQuotientPersistentSurvivingResidueCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho :=
    (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower Q q rho w).2 ⟨hwcell, hqSurvives, rfl⟩
  let record : IsolatedVertexQuotientPersistentSourceRecord q.1 :=
    { residue := rho, component := Q }
  have hrecord : record ∈
      occupiedIsolatedVertexQuotientPersistentSourceRecords
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q := by
    apply (mem_occupiedIsolatedVertexQuotientPersistentSourceRecords_iff
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q record).2
    exact ⟨hrho, hstatic, ⟨w, hwsource⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_univ q, Finset.mem_biUnion.mpr ?_⟩
  exact ⟨record, hrecord, by simpa only [record] using hwsource⟩

/-- Cardinal form of the source-record cover. -/
theorem card_isolatedVertexQuotientDenominatorCompatiblePersistentUnion_le_sum_sourceRecordCells
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k)) :
    (isolatedVertexQuotientDenominatorCompatiblePersistentUnion
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        Ppool k hqpos hqsf hqlower).card ≤
      ∑ q : ReservoirModulus Ppool k,
        ∑ record ∈ occupiedIsolatedVertexQuotientPersistentSourceRecords
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower q,
          (isolatedVertexQuotientPersistentSurvivingResidueCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower record.component q record.residue).card := by
  let records := fun q : ReservoirModulus Ppool k ↦
    occupiedIsolatedVertexQuotientPersistentSourceRecords
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q
  let cell := fun (q : ReservoirModulus Ppool k)
      (record : IsolatedVertexQuotientPersistentSourceRecord q.1) ↦
    isolatedVertexQuotientPersistentSurvivingResidueCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower record.component q record.residue
  calc
    _ ≤ ((Finset.univ : Finset (ReservoirModulus Ppool k)).biUnion
          fun q ↦ (records q).biUnion fun record ↦ cell q record).card :=
      Finset.card_le_card
        (isolatedVertexQuotientDenominatorCompatiblePersistentUnion_subset_sourceRecordUnion
          U p sourceEquations CF hx₀ lowerEquations model hdenominator
            hquotient Ppool k hP hqpos hqsf hqlower hsurvival)
    _ ≤ ∑ q : ReservoirModulus Ppool k,
        ((records q).biUnion fun record ↦ cell q record).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ q : ReservoirModulus Ppool k,
        ∑ record ∈ records q, (cell q record).card := by
      apply Finset.sum_le_sum
      intro q _hq
      exact Finset.card_biUnion_le

/-! ## Record count and a uniform cell estimate -/

/-- At one modulus, there are at most `degree` retained curve records over
each occupied quotient residue. -/
theorem card_occupiedIsolatedVertexQuotientPersistentSourceRecords_le
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    (occupiedIsolatedVertexQuotientPersistentSourceRecords
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q).card ≤
      (occupiedIntegralResidues q.1
        (isolatedVertexQuotientPointFinset
          U p x₀ sourceEquations CF)).card * degree := by
  classical
  let residues := occupiedIntegralResidues q.1
    (isolatedVertexQuotientPointFinset
      U p x₀ sourceEquations CF)
  calc
    _ ≤ ∑ rho ∈ residues,
        (((isolatedVertexQuotientStaticNodeComponentsAtResidue
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower q rho).filter fun Q ↦
          (isolatedVertexQuotientPersistentSurvivingResidueCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower Q q rho).Nonempty).image fun Q ↦
                IsolatedVertexQuotientPersistentSourceRecord.mk rho Q).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ rho ∈ residues,
        (isolatedVertexQuotientStaticNodeComponentsAtResidue
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower q rho).card := by
      apply Finset.sum_le_sum
      intro rho _hrho
      exact Finset.card_image_le.trans (Finset.card_filter_le _ _)
    _ ≤ ∑ _rho ∈ residues, degree := by
      apply Finset.sum_le_sum
      intro rho _hrho
      exact card_isolatedVertexQuotientStaticNodeComponentsAtResidue_le_degree
        hMass U p sourceEquations CF x₀ lowerEquations hJprime
          hJhomogeneous degree hJHilbert hquotient hqpos hqsf hqlower q rho
    _ = residues.card * degree := by simp

/-- The record list is empty at a modulus which is not coprime to the fixed
affine scale times model denominator. -/
theorem card_occupiedIsolatedVertexQuotientPersistentSourceRecords_le_if_coprime
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    (occupiedIsolatedVertexQuotientPersistentSourceRecords
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q).card ≤
      if Nat.Coprime q.1 (((p.m : ℤ) * model.denominator).natAbs)
      then (occupiedIntegralResidues q.1
        (isolatedVertexQuotientPointFinset
          U p x₀ sourceEquations CF)).card * degree else 0 := by
  classical
  by_cases hcop : Nat.Coprime q.1
      (((p.m : ℤ) * model.denominator).natAbs)
  · rw [if_pos hcop]
    exact card_occupiedIsolatedVertexQuotientPersistentSourceRecords_le
      hMass U p sourceEquations CF hx₀ lowerEquations hJprime
        hJhomogeneous degree hJHilbert model hquotient
        hqpos hqsf hqlower q
  · rw [if_neg hcop]
    apply Nat.le_zero.mpr
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro record hrecord
    have hspec :=
      (mem_occupiedIsolatedVertexQuotientPersistentSourceRecords_iff
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q record).1 hrecord
    obtain ⟨w, hw⟩ := hspec.2.2
    have hsurvives :=
      (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower record.component q record.residue w).1 hw |>.2.1
    exact hcop hsurvives.1

/-- A single constant bounds every nonempty literal persistent record cell
whose static component degree is bounded by `degree`. -/
theorem exists_uniform_card_persistentSurvivingResidueCell_le_boundedDegree
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : Ideal (MvPolynomial (Fin 13) Qbar))
        (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1),
        (isolatedVertexQuotientPersistentSurvivingResidueCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower Q q rho).Nonempty →
        ((isolatedVertexQuotientPersistentSurvivingResidueCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower Q q rho).card : ℝ) ≤
          (degree : ℝ) ^ 2 + C *
            (2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 + 2) ^
              ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨C, hC, huniform⟩ :=
    exists_uniform_QbarProjectiveCurve_rescaled_dichotomy_constant
      hPila hBezout hConjugate degree ε hε
  refine ⟨C, hC, ?_⟩
  intro Q q rho hnonempty
  obtain ⟨base, hbase⟩ := hnonempty
  let S := isolatedVertexQuotientPersistentSurvivingResidueCell
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower Q q rho
  have hbaseData :=
    (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower Q q rho base).1 hbase
  have hbaseGeom :=
    mem_zeroLocus_and_retained_of_mem_persistentSurvivingResidueCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower hbase
  have hlabel : isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower base q = some Q :=
    (Finset.mem_filter.mp hbaseData.1).2.2 q hbaseData.2.1
  have hstatic :=
    (isolatedVertexQuotientStaticComponentLabel_eq_some_staticNode_spec
      U p sourceEquations CF x₀ lowerEquations hquotient
        hqpos hqsf hqlower base q Q hlabel).1
  have hstatic' : Q ∈
      isolatedVertexQuotientStaticNodeComponentsAtResidue
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower q rho := by
    simpa only [hbaseData.2.2] using hstatic
  obtain ⟨d, hQprojective, hddegree⟩ :=
    isolatedVertexQuotientStaticNodeComponent_retained_degree_le
      hMass U p sourceEquations CF x₀ lowerEquations hJprime
        hJhomogeneous degree hJHilbert hquotient hqpos hqsf hqlower
        q rho Q hstatic' hbaseGeom.2
  obtain ⟨s, e, hQintegral, hQprojectiveRetained, hs, he,
      _hnonradial⟩ := hbaseGeom.2
  subst s
  have hde : d = e :=
    projectiveDegree_eq_of_hasProjectiveDimensionDegree
      hQprojective hQprojectiveRetained
  have hd : 2 ≤ d := by omega
  let V : ℝ :=
    2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 + 2
  have hV : 1 < V := by
    dsimp only [V]
    have hqreal : (0 : ℝ) < q.1 := by exact_mod_cast hqpos q
    have hnonneg : 0 ≤
        2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 := by
      positivity
    linarith
  apply huniform (hqpos q) base Q d hQintegral.1 hQintegral.2
    hQprojective hd hddegree S hbase
  · intro z hz
    exact (mem_zeroLocus_and_retained_of_mem_persistentSurvivingResidueCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower hz).1
  · intro z hz
    have hzdata :=
      (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho z).1 hz
    have hzPacket : z ∈ integralResiduePacket S rho :=
      mem_integralResiduePacket_iff.mpr ⟨hz, hzdata.2.2⟩
    have hbasePacket : base ∈ integralResiduePacket S rho :=
      mem_integralResiduePacket_iff.mpr ⟨hbase, hbaseData.2.2⟩
    exact intVectorCongruent_of_mem_same_integralResiduePacket
      hzPacket hbasePacket
  · exact hV
  · intro z hz i
    have hzdata :=
      (mem_isolatedVertexQuotientPersistentSurvivingResidueCell_iff
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower Q q rho z).1 hz
    have hzPacket : z ∈ integralResiduePacket S rho :=
      mem_integralResiduePacket_iff.mpr ⟨hz, hzdata.2.2⟩
    have hbasePacket : base ∈ integralResiduePacket S rho :=
      mem_integralResiduePacket_iff.mpr ⟨hbase, hbaseData.2.2⟩
    have hcong : IntVectorCongruent q.1 z base :=
      intVectorCongruent_of_mem_same_integralResiduePacket
        hzPacket hbasePacket
    have hzRegular := (Finset.mem_filter.mp hzdata.1).1
    have hbRegular := (Finset.mem_filter.mp hbaseData.1).1
    have hzPoint := (mem_isolatedVertexRegularQuotientPointFinset_iff
      U p x₀ sourceEquations CF lowerEquations z).1 hzRegular |>.1
    have hbPoint := (mem_isolatedVertexRegularQuotientPointFinset_iff
      U p x₀ sourceEquations CF lowerEquations base).1 hbRegular |>.1
    have hzbox : ∀ j,
        |(z j : ℝ) - (0 : ℝ)| ≤
          (isolatedVertexTransformedNaturalSide U p : ℝ) := by
      intro j
      have hj := isolatedVertexQuotientPoint_coordinate_le
        U p x₀ sourceEquations CF hzPoint j
      have hjReal : ((z j).natAbs : ℝ) ≤
          (isolatedVertexTransformedNaturalSide U p : ℝ) := by
        exact_mod_cast hj
      simpa only [sub_zero, Nat.cast_natAbs, Int.cast_abs] using hjReal
    have hbasebox : ∀ j,
        |(base j : ℝ) - (0 : ℝ)| ≤
          (isolatedVertexTransformedNaturalSide U p : ℝ) := by
      intro j
      have hj := isolatedVertexQuotientPoint_coordinate_le
        U p x₀ sourceEquations CF hbPoint j
      have hjReal : ((base j).natAbs : ℝ) ≤
          (isolatedVertexTransformedNaturalSide U p : ℝ) := by
        exact_mod_cast hj
      simpa only [sub_zero, Nat.cast_natAbs, Int.cast_abs] using hjReal
    have hraw := congruenceDisplacementOrZero_coordinate_bound
      (hqpos q) base z hcong (center := (0 : RealVector 12))
        (R := (isolatedVertexTransformedNaturalSide U p : ℝ))
        hzbox hbasebox i
    linarith

/-! ## The actual aggregate bounds -/

/-- Source-modulus-sensitive aggregate persistent estimate.  The modulus
still appears in every Pila factor, while the record count is charged only
to the existing denominator-compatible occupied-residue sum. -/
theorem exists_uniform_isolatedVertexQuotient_persistentUnion_card_cast_le_sourceModulusSum
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ((isolatedVertexQuotientDenominatorCompatiblePersistentUnion
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          Ppool k hqpos hqsf hqlower).card : ℝ) ≤
        ∑ q : ReservoirModulus Ppool k,
          (if Nat.Coprime q.1
              (((p.m : ℤ) * model.denominator).natAbs)
            then ((occupiedIntegralResidues q.1
              (isolatedVertexQuotientPointFinset
                U p x₀ sourceEquations CF)).card : ℝ) else 0) *
          (degree : ℝ) *
          ((degree : ℝ) ^ 2 + C *
            (2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 + 2) ^
              ((1 / 2 : ℝ) + ε)) := by
  classical
  obtain ⟨C, hC, hcell⟩ :=
    exists_uniform_card_persistentSurvivingResidueCell_le_boundedDegree
      hMass hPila hBezout hConjugate U p sourceEquations CF hx₀
        lowerEquations hJprime hJhomogeneous degree hJHilbert model
        hquotient hqpos hqsf hqlower ε hε
  refine ⟨C, hC, ?_⟩
  have hcover :=
    card_isolatedVertexQuotientDenominatorCompatiblePersistentUnion_le_sum_sourceRecordCells
      U p sourceEquations CF hx₀ lowerEquations model hdenominator
        hquotient Ppool k hP hqpos hqsf hqlower hsurvival
  calc
    _ ≤ ((∑ q : ReservoirModulus Ppool k,
        ∑ record ∈ occupiedIsolatedVertexQuotientPersistentSourceRecords
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower q,
          (isolatedVertexQuotientPersistentSurvivingResidueCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower record.component q record.residue).card : ℕ) : ℝ) := by
      exact_mod_cast hcover
    _ = ∑ q : ReservoirModulus Ppool k,
        ∑ record ∈ occupiedIsolatedVertexQuotientPersistentSourceRecords
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower q,
          ((isolatedVertexQuotientPersistentSurvivingResidueCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower record.component q record.residue).card : ℝ) := by
      norm_num
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _hq
      let records := occupiedIsolatedVertexQuotientPersistentSourceRecords
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q
      let B : ℝ := (degree : ℝ) ^ 2 + C *
        (2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 + 2) ^
          ((1 / 2 : ℝ) + ε)
      have hB : 0 ≤ B := by
        dsimp only [B]
        positivity
      have hrecords : records.card ≤
          if Nat.Coprime q.1
              (((p.m : ℤ) * model.denominator).natAbs)
          then (occupiedIntegralResidues q.1
            (isolatedVertexQuotientPointFinset
              U p x₀ sourceEquations CF)).card * degree else 0 := by
        exact card_occupiedIsolatedVertexQuotientPersistentSourceRecords_le_if_coprime
          hMass U p sourceEquations CF hx₀ lowerEquations hJprime
            hJhomogeneous degree hJHilbert model hquotient
            hqpos hqsf hqlower q
      calc
        _ ≤ ∑ _record ∈ records, B := by
          apply Finset.sum_le_sum
          intro record hrecord
          exact hcell record.component q record.residue
            ((mem_occupiedIsolatedVertexQuotientPersistentSourceRecords_iff
              U p sourceEquations CF hx₀ lowerEquations model hquotient
                hqpos hqsf hqlower q record).1 hrecord).2.2
        _ = (records.card : ℝ) * B := by simp
        _ ≤ ((if Nat.Coprime q.1
              (((p.m : ℤ) * model.denominator).natAbs)
            then (occupiedIntegralResidues q.1
              (isolatedVertexQuotientPointFinset
                U p x₀ sourceEquations CF)).card * degree else 0 : ℕ) : ℝ) * B := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrecords) hB
        _ = (if Nat.Coprime q.1
              (((p.m : ℤ) * model.denominator).natAbs)
            then ((occupiedIntegralResidues q.1
              (isolatedVertexQuotientPointFinset
                U p x₀ sourceEquations CF)).card : ℝ) else 0) *
              (degree : ℝ) * B := by
          by_cases hcop : Nat.Coprime q.1
              (((p.m : ℤ) * model.denominator).natAbs)
          · simp only [if_pos hcop, Nat.cast_mul]
          · simp only [if_neg hcop, Nat.cast_zero, zero_mul]

/-- Occurrence-scale form of the complete persistent contribution.  The
preceding theorem retains every source modulus; here its divided side is
uniformly bounded by `3*T^(4/13)` and the node part of the exact
denominator-compatible occurrence estimate is applied. -/
theorem exists_uniform_isolatedVertexQuotient_persistentUnion_card_cast_le_scale
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hPila : Published.Pila1995TheoremARationalQbarPrime)
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    {M₀ δ C₀ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ) (hC₀ : 0 ≤ C₀)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ) (hP : ∀ l ∈ Ppool, l.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k))
    (hk : k ≤ reservoirDepth M₀ p.H)
    (h2k : 2 * k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) δ ≤ p.H)
    (hfamily : ((((modulusReservoir Ppool k).card +
      (modulusReservoirDirectedEdges Ppool k hP).card : ℕ) : ℝ) ≤
        2 * p.H ^ δ))
    (hupperNode : ∀ q : ReservoirModulus Ppool k,
      (q.1 : ℝ) ≤ C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ δ)
    (hupperEdge : ∀ q r : ReservoirModulus Ppool k,
      (modulusReservoirGraph Ppool k hP).Adj q r →
      (Nat.lcm q.1 r.1 : ℝ) ≤
        C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ((isolatedVertexQuotientDenominatorCompatiblePersistentUnion
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          Ppool k hqpos hqsf hqlower).card : ℝ) ≤
        (degree : ℝ) *
          ((degree : ℝ) ^ 2 + C *
            (3 * p.T ^ (4 / 13 : ℝ)) ^ ((1 / 2 : ℝ) + ε)) *
          (2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ (7 * δ)) := by
  classical
  obtain ⟨C, hC, hsource⟩ :=
    exists_uniform_isolatedVertexQuotient_persistentUnion_card_cast_le_sourceModulusSum
      hMass hPila hBezout hConjugate U p sourceEquations CF hx₀
        lowerEquations hJprime hJhomogeneous degree hJHilbert model
        hdenominator hquotient Ppool k hP hqpos hqsf hqlower hsurvival
        ε hε
  refine ⟨C, hC, hsource.trans ?_⟩
  let occurrence : ℝ := ∑ q : ReservoirModulus Ppool k,
    if Nat.Coprime q.1 (((p.m : ℤ) * model.denominator).natAbs)
    then ((occupiedIntegralResidues q.1
      (isolatedVertexQuotientPointFinset
        U p x₀ sourceEquations CF)).card : ℝ) else 0
  let common : ℝ := (degree : ℝ) ^ 2 + C *
    (3 * p.T ^ (4 / 13 : ℝ)) ^ ((1 / 2 : ℝ) + ε)
  have hcommon : 0 ≤ common := by
    dsimp only [common]
    have hbase : 0 ≤ 3 * p.T ^ (4 / 13 : ℝ) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg p.T_pos.le _)
    exact add_nonneg (sq_nonneg (degree : ℝ))
      (mul_nonneg hC.le (Real.rpow_nonneg hbase _))
  have hoccurrence : occurrence ≤
      2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ (7 * δ) := by
    have hfull :=
      isolatedVertexQuotient_node_edge_occupiedResidues_cast_le_scale
        hM₀ hδ hC₀ U p x₀ sourceEquations CF lowerEquations model
          hquotient Ppool k hP hqsf hk h2k hH hfamily
          hupperNode hupperEdge
    exact le_trans (le_add_of_nonneg_right
      (Finset.sum_nonneg fun _ _ ↦ by positivity)) hfull
  calc
    _ ≤ ∑ q : ReservoirModulus Ppool k,
        (if Nat.Coprime q.1
            (((p.m : ℤ) * model.denominator).natAbs)
          then ((occupiedIntegralResidues q.1
            (isolatedVertexQuotientPointFinset
              U p x₀ sourceEquations CF)).card : ℝ) else 0) *
          (degree : ℝ) * common := by
      apply Finset.sum_le_sum
      intro q _hq
      have hside0 := isolatedVertexQuotient_rescaledSide_le_two_rpow
        U p (hqlower q)
      have hone : (1 : ℝ) ≤ p.T ^ (4 / 13 : ℝ) :=
        Real.one_le_rpow p.one_le_T (by norm_num)
      have hside :
          2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 + 2 ≤
            3 * p.T ^ (4 / 13 : ℝ) := by
        linarith
      have hpow :
          (2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 + 2) ^
              ((1 / 2 : ℝ) + ε) ≤
            (3 * p.T ^ (4 / 13 : ℝ)) ^
              ((1 / 2 : ℝ) + ε) := by
        exact Real.rpow_le_rpow (by positivity) hside (by positivity)
      have hlocal : (degree : ℝ) ^ 2 + C *
          (2 * (isolatedVertexTransformedNaturalSide U p : ℝ) / q.1 + 2) ^
              ((1 / 2 : ℝ) + ε) ≤ common := by
        dsimp only [common]
        exact add_le_add (le_refl ((degree : ℝ) ^ 2))
          (mul_le_mul_of_nonneg_left hpow hC.le)
      exact mul_le_mul_of_nonneg_left hlocal
        (mul_nonneg (by positivity) (Nat.cast_nonneg degree))
    _ = (degree : ℝ) * common * occurrence := by
      simp only [occurrence]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ ≤ (degree : ℝ) * common *
        (2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ (7 * δ)) :=
      mul_le_mul_of_nonneg_left hoccurrence
        (mul_nonneg (Nat.cast_nonneg degree) hcommon)

end

end TranslatedDepthSeven
