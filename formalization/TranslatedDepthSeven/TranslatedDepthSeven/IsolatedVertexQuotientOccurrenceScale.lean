import TranslatedDepthSeven.FixedQuotientOccupiedResidueCRT
import TranslatedDepthSeven.IsolatedVertexQuotientReservoirSelection
import TranslatedDepthSeven.RankSevenRecordOccurrenceScale
import TranslatedDepthSeven.PrimitivePowerLaws

/-!
# The isolated-vertex quotient occurrence scale

For the literal twelve-variable quotient point set, this file proves the
record estimate preceding every component decomposition.  A fixed affine
fivefold residue model gives `H^δ q^5` occupied residue classes.  The
reservoir contains at most `2 H^δ` vertices and directed one-exchange
edges in total, while every vertex modulus and edge lcm is at most
`C T^(9/13) H^δ`.  Hence their combined occupied-residue mass is at most

`2 C^5 T^(45/13) H^(7δ)`.

No component count or integral-point estimate is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 1000000

local instance quotientOccurrencePropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Exact fifth-power calculation at the quotient reservoir scale. -/
theorem finite_sum_fifth_power_at_quotient_reservoir_scale
    {ι : Type} [Fintype ι]
    {H T C δ : ℝ}
    (hH : 0 < H) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hcard : (Fintype.card ι : ℝ) ≤ 2 * H ^ δ)
    (q : ι → ℝ) (hqnonneg : ∀ i, 0 ≤ q i)
    (hqupper : ∀ i, q i ≤ C * T ^ (9 / 13 : ℝ) * H ^ δ) :
    (∑ i : ι, H ^ δ * (q i) ^ 5) ≤
      2 * C ^ 5 * T ^ (45 / 13 : ℝ) * H ^ (7 * δ) := by
  have hHpow : 0 ≤ H ^ δ := Real.rpow_nonneg hH.le δ
  have hbase : 0 ≤ C * T ^ (9 / 13 : ℝ) * H ^ δ := by positivity
  calc
    (∑ i : ι, H ^ δ * (q i) ^ 5) ≤
        ∑ _i : ι, H ^ δ *
          (C * T ^ (9 / 13 : ℝ) * H ^ δ) ^ 5 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hqnonneg i) (hqupper i) 5) hHpow
    _ = (Fintype.card ι : ℝ) *
        (H ^ δ * (C * T ^ (9 / 13 : ℝ) * H ^ δ) ^ 5) := by
      simp
    _ ≤ (2 * H ^ δ) *
        (H ^ δ * (C * T ^ (9 / 13 : ℝ) * H ^ δ) ^ 5) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * C ^ 5 * T ^ (45 / 13 : ℝ) * H ^ (7 * δ) := by
      rw [mul_pow, mul_pow]
      rw [← Real.rpow_mul_natCast hT (9 / 13 : ℝ) 5]
      rw [← Real.rpow_mul_natCast hH.le δ 5]
      rw [show (9 / 13 : ℝ) * (5 : ℕ) = 45 / 13 by norm_num]
      rw [show δ * (5 : ℕ) = 5 * δ by ring]
      rw [show 7 * δ = δ + δ + 5 * δ by ring,
        Real.rpow_add hH, Real.rpow_add hH]
      ring

/-- Combined vertex-and-directed-edge version of the same calculation. -/
theorem finite_two_sum_fifth_power_at_quotient_reservoir_scale
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {H T C δ : ℝ}
    (hH : 0 < H) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hcard : ((Fintype.card ι + Fintype.card κ : ℕ) : ℝ) ≤
      2 * H ^ δ)
    (q : ι → ℝ) (r : κ → ℝ)
    (hqnonneg : ∀ i, 0 ≤ q i) (hrnonneg : ∀ j, 0 ≤ r j)
    (hqupper : ∀ i, q i ≤ C * T ^ (9 / 13 : ℝ) * H ^ δ)
    (hrupper : ∀ j, r j ≤ C * T ^ (9 / 13 : ℝ) * H ^ δ) :
    (∑ i : ι, H ^ δ * (q i) ^ 5) +
        (∑ j : κ, H ^ δ * (r j) ^ 5) ≤
      2 * C ^ 5 * T ^ (45 / 13 : ℝ) * H ^ (7 * δ) := by
  let s : ι ⊕ κ → ℝ := Sum.elim q r
  have hcardSum : (Fintype.card (ι ⊕ κ) : ℝ) ≤ 2 * H ^ δ := by
    simpa only [Fintype.card_sum, Nat.cast_add] using hcard
  have hsnonneg : ∀ x, 0 ≤ s x := by
    rintro (i | j)
    · exact hqnonneg i
    · exact hrnonneg j
  have hsupper : ∀ x, s x ≤ C * T ^ (9 / 13 : ℝ) * H ^ δ := by
    rintro (i | j)
    · exact hqupper i
    · exact hrupper j
  have h := finite_sum_fifth_power_at_quotient_reservoir_scale
    hH hT hC hcardSum s hsnonneg hsupper
  simpa only [Fintype.sum_sum_type, s, Sum.elim_inl, Sum.elim_inr] using h

/-- The fixed-model occupied-residue estimate for an arbitrary literal
square-free modulus on the quotient point set. -/
theorem card_isolatedVertexQuotient_occupiedResidues_squarefree_cast_le
    {M₀ δ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (integralAffineTransformEquationFinset
          (dropFirstIntVector (U.pointEquiv x₀)) p.m lowerEquations))
    (q : ℕ) (hq : Squarefree q)
    (hcop : Nat.Coprime q
      (((p.m : ℤ) * model.denominator).natAbs))
    (hfactorCard : q.primeFactors.card ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) δ ≤ p.H) :
    ((occupiedIntegralResidues q
      (isolatedVertexQuotientPointFinset
        U p x₀ sourceEquations CF)).card : ℝ) ≤
      p.H ^ δ * (q : ℝ) ^ 5 := by
  let Z := isolatedVertexQuotientPointFinset
    U p x₀ sourceEquations CF
  let b := dropFirstIntVector (U.pointEquiv x₀)
  have hzero : ∀ w ∈ Z, ∀ g ∈ lowerEquations,
      MvPolynomial.eval (integralAffineMap b w p.m) g = 0 := by
    intro w hw g hg
    have hwZero : IntegralCommonZero
        (integralAffineTransformEquationFinset b p.m lowerEquations) w :=
      (mem_integralCommonZeroInBox_iff _ w).mp
        (hquotient (by simpa only [Z] using hw)) |>.2
    exact (integralCommonZero_transform_iff b w p.m lowerEquations).mp
      hwZero g hg
  let P := q.primeFactors
  have hprime : ∀ l ∈ P, l.Prime := by
    intro l hl
    exact (Nat.mem_primeFactors.mp hl).1
  obtain ⟨hgoodm, hgoodden⟩ :=
    primeFactors_good_of_coprime_scale_denominator
      p q model.denominator hcop
  have hbound := card_quotientOccupiedResidues_cast_le_rpow_mul
    hM₀ hδ lowerEquations model Z b p.m hzero P hprime
      hgoodm hgoodden hfactorCard hH
  have hproduct : primeProduct P = q := by
    simpa only [P, primeProduct] using Nat.prod_primeFactors_of_squarefree hq
  calc
    ((occupiedIntegralResidues q Z).card : ℝ) =
        ((occupiedIntegralResidues (∏ l : P, (l : ℕ)) Z).card : ℝ) := by
      congr 1
      apply card_occupiedIntegralResidues_congr_modulus
      rw [primeSubtype_prod_eq_primeProduct, hproduct]
    _ ≤ p.H ^ δ * (primeProduct P : ℝ) ^ 5 := hbound
    _ = p.H ^ δ * (q : ℝ) ^ 5 := by rw [hproduct]

/-- Literal quotient analogue of the manuscript's record estimate.  The
`if` clauses are exactly the restrictions to moduli, respectively lcms,
coprime to the affine scale and fixed model denominator. -/
theorem isolatedVertexQuotient_node_edge_occupiedResidues_cast_le_scale
    {M₀ δ C₀ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ)
    (hC₀ : 0 ≤ C₀)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (integralAffineTransformEquationFinset
          (dropFirstIntVector (U.pointEquiv x₀)) p.m lowerEquations))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ l ∈ P, l.Prime)
    (hmoduli : ∀ q : ReservoirModulus P k, Squarefree q.1)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (h2k : 2 * k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) δ ≤ p.H)
    (hfamily : ((((modulusReservoir P k).card +
      (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
        2 * p.H ^ δ))
    (hupperNode : ∀ q : ReservoirModulus P k,
      (q.1 : ℝ) ≤ C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ δ)
    (hupperEdge : ∀ q r : ReservoirModulus P k,
      (modulusReservoirGraph P k hP).Adj q r →
      (Nat.lcm q.1 r.1 : ℝ) ≤
        C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ δ) :
    (∑ q : ReservoirModulus P k,
        if Nat.Coprime q.1 (((p.m : ℤ) * model.denominator).natAbs)
        then ((occupiedIntegralResidues q.1
          (isolatedVertexQuotientPointFinset
            U p x₀ sourceEquations CF)).card : ℝ) else 0) +
      (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        if Nat.Coprime (Nat.lcm qr.1.1.1 qr.1.2.1)
            (((p.m : ℤ) * model.denominator).natAbs)
        then ((occupiedIntegralResidues
          (Nat.lcm qr.1.1.1 qr.1.2.1)
          (isolatedVertexQuotientPointFinset
            U p x₀ sourceEquations CF)).card : ℝ) else 0) ≤
      2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ (7 * δ) := by
  let Z := isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF
  let D := (((p.m : ℤ) * model.denominator).natAbs)
  let edgeType := ↑(modulusReservoirDirectedEdges P k hP)
  have hcardTypes :
      ((Fintype.card (ReservoirModulus P k) + Fintype.card edgeType : ℕ) : ℝ) ≤
        2 * p.H ^ δ := by
    calc
      ((Fintype.card (ReservoirModulus P k) + Fintype.card edgeType : ℕ) : ℝ) =
          (((modulusReservoir P k).card +
            (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) := by
        congr 2
        · rw [card_reservoirModulus hP k,
            card_modulusReservoir_of_primes hP k]
        · simp only [edgeType, Fintype.card_coe]
      _ ≤ 2 * p.H ^ δ := hfamily
  have hnode : ∀ q : ReservoirModulus P k,
      (if Nat.Coprime q.1 D
        then ((occupiedIntegralResidues q.1 Z).card : ℝ) else 0) ≤
        p.H ^ δ * (q.1 : ℝ) ^ 5 := by
    intro q
    by_cases hcop : Nat.Coprime q.1 D
    · rw [if_pos hcop]
      exact card_isolatedVertexQuotient_occupiedResidues_squarefree_cast_le
        hM₀ hδ U p x₀ sourceEquations CF lowerEquations model
          hquotient q.1 (hmoduli q) (by simpa only [D] using hcop)
          ((primeFactors_spec_of_mem_modulusReservoir hP q.2).2.1.symm ▸ hk) hH
    · rw [if_neg hcop]
      exact mul_nonneg (Real.rpow_nonneg p.H_pos.le δ)
        (pow_nonneg (Nat.cast_nonneg q.1) 5)
  have hedge : ∀ qr : edgeType,
      (if Nat.Coprime (Nat.lcm qr.1.1.1 qr.1.2.1) D
        then ((occupiedIntegralResidues
          (Nat.lcm qr.1.1.1 qr.1.2.1) Z).card : ℝ) else 0) ≤
        p.H ^ δ * (Nat.lcm qr.1.1.1 qr.1.2.1 : ℝ) ^ 5 := by
    intro qr
    by_cases hcop : Nat.Coprime (Nat.lcm qr.1.1.1 qr.1.2.1) D
    · rw [if_pos hcop]
      exact card_isolatedVertexQuotient_occupiedResidues_squarefree_cast_le
        hM₀ hδ U p x₀ sourceEquations CF lowerEquations model
          hquotient (Nat.lcm qr.1.1.1 qr.1.2.1)
          (squarefree_lcm_of_squarefree (hmoduli qr.1.1) (hmoduli qr.1.2))
          (by simpa only [D] using hcop)
          ((card_primeFactors_lcm_reservoir_le_two_mul hP
            qr.1.1 qr.1.2).trans h2k) hH
    · rw [if_neg hcop]
      exact mul_nonneg (Real.rpow_nonneg p.H_pos.le δ)
        (pow_nonneg
          (Nat.cast_nonneg (Nat.lcm qr.1.1.1 qr.1.2.1)) 5)
  calc
    (∑ q : ReservoirModulus P k,
        if Nat.Coprime q.1 (((p.m : ℤ) * model.denominator).natAbs)
        then ((occupiedIntegralResidues q.1
          (isolatedVertexQuotientPointFinset
            U p x₀ sourceEquations CF)).card : ℝ) else 0) +
      (∑ qr : edgeType,
        if Nat.Coprime (Nat.lcm qr.1.1.1 qr.1.2.1)
            (((p.m : ℤ) * model.denominator).natAbs)
        then ((occupiedIntegralResidues
          (Nat.lcm qr.1.1.1 qr.1.2.1)
          (isolatedVertexQuotientPointFinset
            U p x₀ sourceEquations CF)).card : ℝ) else 0) ≤
        (∑ q : ReservoirModulus P k, p.H ^ δ * (q.1 : ℝ) ^ 5) +
          (∑ qr : edgeType,
            p.H ^ δ * (Nat.lcm qr.1.1.1 qr.1.2.1 : ℝ) ^ 5) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro q _hq
        simpa only [Z, D] using hnode q
      · apply Finset.sum_le_sum
        intro qr _hqr
        simpa only [Z, D] using hedge qr
    _ ≤ 2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ (7 * δ) := by
      apply finite_two_sum_fifth_power_at_quotient_reservoir_scale
        p.H_pos p.T_pos.le hC₀ hcardTypes
          (fun q : ReservoirModulus P k ↦ (q.1 : ℝ))
          (fun qr : edgeType ↦ (Nat.lcm qr.1.1.1 qr.1.2.1 : ℝ))
          (fun q ↦ Nat.cast_nonneg q.1)
          (fun qr ↦ Nat.cast_nonneg (Nat.lcm qr.1.1.1 qr.1.2.1))
          hupperNode
      intro qr
      exact hupperEdge qr.1.1 qr.1.2 (Finset.mem_filter.mp qr.2).2

/-- If the reservoir loss is run with `δ = ε/7`, the occurrence bound
has exactly one factor `H^ε`. -/
theorem isolatedVertexQuotient_node_edge_occupiedResidues_cast_le_epsilon
    {M₀ ε C₀ : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (hC₀ : 0 ≤ C₀)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (integralAffineTransformEquationFinset
          (dropFirstIntVector (U.pointEquiv x₀)) p.m lowerEquations))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ l ∈ P, l.Prime)
    (hmoduli : ∀ q : ReservoirModulus P k, Squarefree q.1)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (h2k : 2 * k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) (ε / 7) ≤ p.H)
    (hfamily : ((((modulusReservoir P k).card +
      (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
        2 * p.H ^ (ε / 7)))
    (hupperNode : ∀ q : ReservoirModulus P k,
      (q.1 : ℝ) ≤ C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ (ε / 7))
    (hupperEdge : ∀ q r : ReservoirModulus P k,
      (modulusReservoirGraph P k hP).Adj q r →
      (Nat.lcm q.1 r.1 : ℝ) ≤
        C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ (ε / 7)) :
    (∑ q : ReservoirModulus P k,
        if Nat.Coprime q.1 (((p.m : ℤ) * model.denominator).natAbs)
        then ((occupiedIntegralResidues q.1
          (isolatedVertexQuotientPointFinset
            U p x₀ sourceEquations CF)).card : ℝ) else 0) +
      (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        if Nat.Coprime (Nat.lcm qr.1.1.1 qr.1.2.1)
            (((p.m : ℤ) * model.denominator).natAbs)
        then ((occupiedIntegralResidues
          (Nat.lcm qr.1.1.1 qr.1.2.1)
          (isolatedVertexQuotientPointFinset
            U p x₀ sourceEquations CF)).card : ℝ) else 0) ≤
      2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ ε := by
  have h := isolatedVertexQuotient_node_edge_occupiedResidues_cast_le_scale
    hM₀ (show 0 < ε / 7 by positivity) hC₀ U p x₀ sourceEquations CF
      lowerEquations model hquotient P k hP hmoduli hk h2k hH
      hfamily hupperNode hupperEdge
  simpa only [show 7 * (ε / 7) = ε by ring] using h

/-- One explicit constant dominating both the vertex-modulus and edge-lcm
upper constants supplied by the canonical quotient reservoir. -/
def isolatedVertexQuotientOccurrenceModulusConstant
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (η : ℝ) : ℝ :=
  let E := (isolatedVertexQuotientCertificateExponent U lowerEquations : ℝ)
  let A := manuscriptPrimeIntervalCoefficient E (9 / 13)
  let C := (isolatedVertexQuotientReservoirConstant U : ℝ)
  max ((4 * A * (η / 3)⁻¹) * C)
    ((16 * A ^ 2 * ((η / 3)⁻¹) ^ 2) * C)

/-- Canonical form of the quotient record estimate.  For every positive
`ε`, the literal `T^(9/13)` reservoir gives the restricted vertex and
directed-edge occupied-residue sum at scale `T^(45/13) H^ε`.

The fixed model is the only geometric datum.  In particular, no quotient
node component list and no estimate for integral points is assumed. -/
theorem eventually_exists_canonical_isolatedVertexQuotient_occurrence_bound
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℝ in Filter.atTop, ∀ (p : Parameters), p.H = H →
      ∀ (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
        (x₀ : IntVector 13),
      isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF ⊆
        integralCommonZeroInBox
          (M := isolatedVertexTransformedNaturalSide U p)
          (integralAffineTransformEquationFinset
            (dropFirstIntVector (U.pointEquiv x₀)) p.m lowerEquations) →
      ∃ (P : Finset ℕ) (k : ℕ) (hP : ∀ l ∈ P, l.Prime),
        P = manuscriptPrimePoolAt
          (isolatedVertexQuotientCertificateExponent
            U lowerEquations : ℝ) (9 / 13) H ∧
        k = manuscriptCrossingAt
          (isolatedVertexQuotientCertificateExponent
            U lowerEquations : ℝ) (9 / 13)
          (isolatedVertexQuotientReservoirConstant U : ℝ) H p.T ∧
        (∑ q : ReservoirModulus P k,
            if Nat.Coprime q.1
                (((p.m : ℤ) * model.denominator).natAbs)
            then ((occupiedIntegralResidues q.1
              (isolatedVertexQuotientPointFinset
                U p x₀ sourceEquations CF)).card : ℝ) else 0) +
          (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
            if Nat.Coprime (Nat.lcm qr.1.1.1 qr.1.2.1)
                (((p.m : ℤ) * model.denominator).natAbs)
            then ((occupiedIntegralResidues
              (Nat.lcm qr.1.1.1 qr.1.2.1)
              (isolatedVertexQuotientPointFinset
                U p x₀ sourceEquations CF)).card : ℝ) else 0) ≤
          2 * (isolatedVertexQuotientOccurrenceModulusConstant
              U lowerEquations (ε / 7)) ^ 5 *
            p.T ^ (45 / 13 : ℝ) * H ^ ε := by
  let η : ℝ := ε / 7
  let E : ℝ := isolatedVertexQuotientCertificateExponent U lowerEquations
  let C : ℝ := isolatedVertexQuotientReservoirConstant U
  let B : ℝ := manuscriptPoolDepthCoefficient E (9 / 13)
  let M₀ : ℝ := 2 * B + 1
  let C₀ : ℝ := isolatedVertexQuotientOccurrenceModulusConstant
    U lowerEquations η
  have hη : 0 < η := by dsimp only [η]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hC : 1 < C := by
    dsimp only [C]
    exact_mod_cast one_lt_isolatedVertexQuotientReservoirConstant U
  have hB : 0 ≤ B := by
    change 0 ≤ manuscriptPoolDepthCoefficient E (9 / 13)
    unfold manuscriptPoolDepthCoefficient
    nlinarith
  have hM₀ : 0 ≤ M₀ := by dsimp only [M₀]; positivity
  have hroom : B + B < M₀ := by dsimp only [M₀]; linarith
  have hApos : 0 < manuscriptPrimeIntervalCoefficient E (9 / 13) := by
    change 0 < manuscriptPrimeIntervalCoefficient E (9 / 13)
    unfold manuscriptPrimeIntervalCoefficient manuscriptPoolDepthCoefficient
    nlinarith
  have hC₀ : 0 ≤ C₀ := by
    change 0 ≤ max
      ((4 * manuscriptPrimeIntervalCoefficient E (9 / 13) * (η / 3)⁻¹) * C)
      ((16 * (manuscriptPrimeIntervalCoefficient E (9 / 13)) ^ 2 *
        ((η / 3)⁻¹) ^ 2) * C)
    have hinv : 0 ≤ (η / 3)⁻¹ := (inv_pos.mpr (by positivity)).le
    have hfirst : 0 ≤
        ((4 * manuscriptPrimeIntervalCoefficient E (9 / 13) * (η / 3)⁻¹) * C) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hApos.le) hinv)
        (zero_le_one.trans hC.le)
    exact hfirst.trans (le_max_left _ _)
  filter_upwards [eventually_exists_manuscriptModulusReservoir
      (A := E) (a := (9 / 13 : ℝ)) (Cres := C)
        hE (by norm_num) (by norm_num) hC hη,
    eventually_reservoirDepth_add_le hB hB hroom,
    Filter.eventually_ge_atTop
      (reservoirSubpowerThreshold M₀ (model.localConstant : ℝ) η)]
      with H hreservoir hdepthRoom hlocal
  intro p hpH sourceEquations CF x₀ hquotient
  have hTH : p.T ≤ H := by rw [← hpH]; exact p.T_le_H
  obtain ⟨P, k, hP, hPcanonical, hkcanonical, hPcard,
      _hPinterval, hkP, hmoduli, _hconnected, hfamily, hlcm,
      _hcertOne, _hcertTwo⟩ :=
    hreservoir p.T p.one_le_T hTH
  have h2k : 2 * k ≤ reservoirDepth M₀ p.H := by
    have hkTwo : 2 * k ≤ P.card + P.card := by omega
    calc
      2 * k ≤ P.card + P.card := hkTwo
      _ = reservoirDepth B H + reservoirDepth B H := by
        rw [hPcard]
      _ ≤ reservoirDepth M₀ H := hdepthRoom
      _ = reservoirDepth M₀ p.H := by rw [hpH]
  have hk : k ≤ reservoirDepth M₀ p.H := by omega
  have hlocal' : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) η ≤ p.H := by
    rwa [hpH]
  have hnodeConstant :
      (4 * manuscriptPrimeIntervalCoefficient E (9 / 13) * (η / 3)⁻¹) * C ≤ C₀ := by
    exact le_max_left _ _
  have hedgeConstant :
      (16 * (manuscriptPrimeIntervalCoefficient E (9 / 13)) ^ 2 *
        ((η / 3)⁻¹) ^ 2) * C ≤ C₀ := by
    exact le_max_right _ _
  have hupperNode : ∀ q : ReservoirModulus P k,
      (q.1 : ℝ) ≤ C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ η := by
    intro q
    have hq := (hmoduli q).2.2
    have hpowT : 0 ≤ p.T ^ (9 / 13 : ℝ) :=
      Real.rpow_nonneg p.T_pos.le _
    have hpowH : 0 ≤ p.H ^ η := Real.rpow_nonneg p.H_pos.le _
    calc
      (q.1 : ℝ) ≤
          (4 * manuscriptPrimeIntervalCoefficient E (9 / 13) * (η / 3)⁻¹) *
            C * p.T ^ (9 / 13 : ℝ) * p.H ^ η := by
        simpa only [E, C, η, hpH] using hq
      _ ≤ C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ η := by
        gcongr
  have hupperEdge : ∀ q r : ReservoirModulus P k,
      (modulusReservoirGraph P k hP).Adj q r →
      (Nat.lcm q.1 r.1 : ℝ) ≤
        C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ η := by
    intro q r hqr
    have hr := (hlcm q r hqr).2
    have hpowT : 0 ≤ p.T ^ (9 / 13 : ℝ) :=
      Real.rpow_nonneg p.T_pos.le _
    have hpowH : 0 ≤ p.H ^ η := Real.rpow_nonneg p.H_pos.le _
    calc
      (Nat.lcm q.1 r.1 : ℝ) ≤
          (16 * (manuscriptPrimeIntervalCoefficient E (9 / 13)) ^ 2 *
            ((η / 3)⁻¹) ^ 2) * C *
              p.T ^ (9 / 13 : ℝ) * p.H ^ η := by
        simpa only [E, C, η, hpH] using hr
      _ ≤ C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ η := by
        gcongr
  refine ⟨P, k, hP, ?_, ?_, ?_⟩
  · simpa only [E] using hPcanonical
  · simpa only [E, C] using hkcanonical
  have hbound :=
    isolatedVertexQuotient_node_edge_occupiedResidues_cast_le_epsilon
      hM₀ hε hC₀ U p x₀ sourceEquations CF lowerEquations model
        hquotient P k hP (fun q ↦ (hmoduli q).1) hk h2k hlocal'
        (by simpa only [η, hpH] using hfamily)
        (by simpa only [η] using hupperNode)
        (by simpa only [η] using hupperEdge)
  simpa only [C₀, η, hpH] using hbound

end

end TranslatedDepthSeven
