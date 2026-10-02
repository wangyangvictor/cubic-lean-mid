import TranslatedDepthSeven.DepthSevenOccupiedTangentPackets
import TranslatedDepthSeven.RankSevenRecordCardinality

/-!
# Occupied residue bounds for surviving rank-seven moduli

The fixed-cone CRT estimate is stated for a prime product and for the whole
normalized displacement set.  A rank-seven record instead carries a literal
reservoir modulus and a Jacobian-chart subset.  The lemmas below make this
specialization explicit: the prime set is the modulus's actual
`Nat.primeFactors`, and certificate survival supplies the required
coprimality with the affine scale and the fixed denominator.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

local instance occupiedResiduePropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Occupied residue classes are monotone in the underlying finite point
set. -/
theorem occupiedIntegralResidues_mono
    {N q : ℕ} {X Y : Finset (IntVector N)} (hXY : X ⊆ Y) :
    occupiedIntegralResidues q X ⊆ occupiedIntegralResidues q Y := by
  intro rho hrho
  obtain ⟨z, hzX, hzr⟩ := mem_occupiedIntegralResidues_iff.mp hrho
  exact mem_occupiedIntegralResidues_iff.mpr ⟨z, hXY hzX, hzr⟩

/-- Every rank-seven Jacobian chart is a subset of the normalized
displacement set. -/
theorem depthSevenNormalizedJacobianChartCell_subset
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations) :
    depthSevenNormalizedJacobianChartCell p x₀ equations CF C ⊆
      depthSevenNormalizedDisplacementFinset p x₀ equations CF := by
  intro z hz
  exact (mem_depthSevenNormalizedJacobianChartCell_iff
    p x₀ equations CF C z).mp hz |>.1

/-- The least common multiple of two square-free natural numbers is
square-free.  This elementary lemma is included because the edge records are
indexed by the literal lcm rather than by an abstract prime set. -/
theorem squarefree_lcm_of_squarefree {m n : ℕ}
    (hm : Squarefree m) (hn : Squarefree n) :
    Squarefree (Nat.lcm m n) := by
  let g := Nat.gcd m n
  let s := n / g
  have hgDvdN : g ∣ n := Nat.gcd_dvd_right m n
  have hgDvdM : g ∣ m := Nat.gcd_dvd_left m n
  have hsDvdN : s ∣ n := by
    refine ⟨g, ?_⟩
    exact (Nat.div_mul_cancel hgDvdN).symm
  have hsSquarefree : Squarefree s := hn.squarefree_of_dvd hsDvdN
  have hcop : Nat.Coprime m s := by
    have h := Nat.coprime_div_gcd_of_squarefree hn hm.ne_zero
    rw [Nat.gcd_comm] at h
    exact h.symm
  have hnDvd : n ∣ m * s := by
    calc
      n = s * g := (Nat.div_mul_cancel hgDvdN).symm
      _ ∣ s * m := Nat.mul_dvd_mul_left s hgDvdM
      _ = m * s := Nat.mul_comm s m
  have heq : Nat.lcm m n = m * s := by
    apply Nat.lcm_eq_iff.mpr
    refine ⟨dvd_mul_right m s, hnDvd, ?_⟩
    intro c hmc hnc
    exact hcop.mul_dvd_of_dvd_of_dvd hmc (hsDvdN.trans hnc)
  rw [heq]
  exact (Nat.squarefree_mul hcop).mpr ⟨hm, hsSquarefree⟩

/-- Prime factors of the lcm of two reservoir moduli lie in the union of
the two literal factor sets.  Consequently their number is at most `2*k`. -/
theorem card_primeFactors_lcm_reservoir_le_two_mul
    {P : Finset ℕ} {k : ℕ} (hP : ∀ s ∈ P, s.Prime)
    (q r : ReservoirModulus P k) :
    (Nat.lcm q.1 r.1).primeFactors.card ≤ 2 * k := by
  have hqSpec := primeFactors_spec_of_mem_modulusReservoir hP q.2
  have hrSpec := primeFactors_spec_of_mem_modulusReservoir hP r.2
  have hqPrime : ∀ s ∈ q.1.primeFactors, s.Prime := by
    intro s hs
    exact (Nat.mem_primeFactors.mp hs).1
  have hrPrime : ∀ s ∈ r.1.primeFactors, s.Prime := by
    intro s hs
    exact (Nat.mem_primeFactors.mp hs).1
  have hqNe : q.1 ≠ 0 := by
    rw [← hqSpec.2.2]
    exact primeProduct_ne_zero hqPrime
  have hrNe : r.1 ≠ 0 := by
    rw [← hrSpec.2.2]
    exact primeProduct_ne_zero hrPrime
  have hsubset : (Nat.lcm q.1 r.1).primeFactors ⊆
      q.1.primeFactors ∪ r.1.primeFactors := by
    intro s hs
    have hsData := Nat.mem_primeFactors.mp hs
    rcases hsData.1.dvd_or_dvd_of_dvd_lcm hsData.2.1 with hsq | hsr
    · exact Finset.mem_union_left _
        (Nat.mem_primeFactors.mpr ⟨hsData.1, hsq, hqNe⟩)
    · exact Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hsData.1, hsr, hrNe⟩)
  calc
    (Nat.lcm q.1 r.1).primeFactors.card ≤
        (q.1.primeFactors ∪ r.1.primeFactors).card :=
      Finset.card_le_card hsubset
    _ ≤ q.1.primeFactors.card + r.1.primeFactors.card :=
      Finset.card_union_le _ _
    _ = 2 * k := by rw [hqSpec.2.1, hrSpec.2.1]; omega

/-- The fixed-cone CRT bound for an arbitrary literal square-free modulus.
This is the form needed for an edge lcm. -/
theorem card_depthSevenNormalizedChart_occupiedResidues_squarefree_cast_le
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (q : ℕ) (hq : Squarefree q)
    (hgoodm : ∀ s ∈ q.primeFactors, ¬ s ∣ p.m)
    (hgoodden : ∀ s ∈ q.primeFactors,
      ¬ s ∣ model.denominator.natAbs)
    (hfactorCard : q.primeFactors.card ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) ε ≤ p.H) :
    ((occupiedIntegralResidues q
      (depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C)).card : ℝ) ≤
      p.H ^ ε * (q : ℝ) ^ 6 := by
  have hprime : ∀ s ∈ q.primeFactors, s.Prime := by
    intro s hs
    exact (Nat.mem_primeFactors.mp hs).1
  have hfull :=
    card_depthSevenNormalized_occupiedResidues_primeProduct_cast_le
      hM₀ hε p x₀ equations CF model q.primeFactors hprime
        hgoodm hgoodden hfactorCard hH
  have hsubset :
      occupiedIntegralResidues q
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C) ⊆
        occupiedIntegralResidues q
          (depthSevenNormalizedDisplacementFinset
            p x₀ equations CF) :=
    occupiedIntegralResidues_mono
      (depthSevenNormalizedJacobianChartCell_subset
        p x₀ equations CF C)
  have hcard :
      ((occupiedIntegralResidues q
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C)).card : ℝ) ≤
      ((occupiedIntegralResidues q
        (depthSevenNormalizedDisplacementFinset
          p x₀ equations CF)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hproduct : primeProduct q.primeFactors = q := by
    simpa only [primeProduct] using Nat.prod_primeFactors_of_squarefree hq
  rw [hproduct] at hfull
  exact hcard.trans hfull

/-- The fixed-cone CRT bound on a literal reservoir modulus.  The hypotheses
refer only to its actual prime factors. -/
theorem card_depthSevenNormalizedChart_occupiedResidues_reservoirModulus_cast_le
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    {P : Finset ℕ} {k : ℕ} (hP : ∀ s ∈ P, s.Prime)
    (q : ReservoirModulus P k)
    (hgoodm : ∀ s ∈ q.1.primeFactors, ¬ s ∣ p.m)
    (hgoodden : ∀ s ∈ q.1.primeFactors,
      ¬ s ∣ model.denominator.natAbs)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) ε ≤ p.H) :
    ((occupiedIntegralResidues q.1
      (depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C)).card : ℝ) ≤
      p.H ^ ε * (q.1 : ℝ) ^ 6 := by
  have hfactor := primeFactors_spec_of_mem_modulusReservoir hP q.2
  have hprime : ∀ s ∈ q.1.primeFactors, s.Prime := by
    intro s hs
    exact (Nat.mem_primeFactors.mp hs).1
  have hfactorCard : q.1.primeFactors.card ≤ reservoirDepth M₀ p.H := by
    rw [hfactor.2.1]
    exact hk
  have hfull :=
    card_depthSevenNormalized_occupiedResidues_primeProduct_cast_le
      hM₀ hε p x₀ equations CF model q.1.primeFactors hprime
        hgoodm hgoodden hfactorCard hH
  have hsubset :
      occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C) ⊆
        occupiedIntegralResidues q.1
          (depthSevenNormalizedDisplacementFinset
            p x₀ equations CF) :=
    occupiedIntegralResidues_mono
      (depthSevenNormalizedJacobianChartCell_subset
        p x₀ equations CF C)
  have hcard :
      ((occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell
          p x₀ equations CF C)).card : ℝ) ≤
      ((occupiedIntegralResidues q.1
        (depthSevenNormalizedDisplacementFinset
          p x₀ equations CF)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  rw [hfactor.2.2] at hfull
  exact hcard.trans hfull

/-- Coprimality of a natural modulus with the product of the affine scale
and a fixed denominator implies the two primewise nondivisibility
conditions needed by the CRT estimate. -/
theorem primeFactors_good_of_coprime_scale_denominator
    (p : Parameters) (q : ℕ) (denominator : ℤ)
    (hc : Nat.Coprime q
      (((p.m : ℤ) * denominator).natAbs)) :
    (∀ s ∈ q.primeFactors, ¬ s ∣ p.m) ∧
      (∀ s ∈ q.primeFactors, ¬ s ∣ denominator.natAbs) := by
  constructor
  · intro s hs hsm
    have hsDvd : s ∣ q := Nat.dvd_of_mem_primeFactors hs
    have hsCoprime : Nat.Coprime s
        (((p.m : ℤ) * denominator).natAbs) :=
      Nat.Coprime.of_dvd_left hsDvd hc
    have hsPrime : s.Prime := (Nat.mem_primeFactors.mp hs).1
    apply (hsPrime.coprime_iff_not_dvd.mp hsCoprime)
    simpa [Int.natAbs_mul] using
      (dvd_mul_of_dvd_left hsm denominator.natAbs)
  · intro s hs hsden
    have hsDvd : s ∣ q := Nat.dvd_of_mem_primeFactors hs
    have hsCoprime : Nat.Coprime s
        (((p.m : ℤ) * denominator).natAbs) :=
      Nat.Coprime.of_dvd_left hsDvd hc
    have hsPrime : s.Prime := (Nat.mem_primeFactors.mp hs).1
    apply (hsPrime.coprime_iff_not_dvd.mp hsCoprime)
    simpa [Int.natAbs_mul] using
      (dvd_mul_of_dvd_right hsden p.m)

/-- Reservoir-modulus wrapper around the preceding literal natural-number
statement. -/
theorem reservoir_primeFactors_good_of_coprime_scale_denominator
    (p : Parameters) {P : Finset ℕ} {k : ℕ}
    (_hP : ∀ s ∈ P, s.Prime) (q : ReservoirModulus P k)
    (denominator : ℤ)
    (hc : Nat.Coprime q.1
      (((p.m : ℤ) * denominator).natAbs)) :
    (∀ s ∈ q.1.primeFactors, ¬ s ∣ p.m) ∧
      (∀ s ∈ q.1.primeFactors, ¬ s ∣ denominator.natAbs) :=
  primeFactors_good_of_coprime_scale_denominator p q.1 denominator hc

/-- Final surviving-record form: the first half of
`survivesTwoCertificates` alone supplies all primewise hypotheses for the
fixed-cone CRT bound. -/
theorem card_depthSevenNormalizedChart_occupiedResidues_of_survives_cast_le
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    {P : Finset ℕ} {k : ℕ} (hP : ∀ s ∈ P, s.Prime)
    (q : ReservoirModulus P k) (E : ℤ)
    (hsurvives : survivesTwoCertificates q
      ((p.m : ℤ) * model.denominator) E)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) ε ≤ p.H) :
    ((occupiedIntegralResidues q.1
      (depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C)).card : ℝ) ≤
      p.H ^ ε * (q.1 : ℝ) ^ 6 := by
  obtain ⟨hgoodm, hgoodden⟩ :=
    reservoir_primeFactors_good_of_coprime_scale_denominator
      p hP q model.denominator hsurvives.1
  exact
    card_depthSevenNormalizedChart_occupiedResidues_reservoirModulus_cast_le
      hM₀ hε p x₀ equations CF C model hP q hgoodm hgoodden hk hH

/-- A surviving non-surface node family has the expected `q^6` occurrence
mass.  If the family is nonempty, one of its literal witnesses certifies that
the modulus is coprime to the fixed affine-scale denominator; if it is empty,
the assertion is immediate. -/
theorem card_occupiedRankSevenSurvivingNonSurfaceNodeRecords_cast_le
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (D : ℕ)
    (hcomponents : ∀ rho ∈ occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenNonSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) ε ≤ p.H) :
    ((occupiedRankSevenSurvivingNonSurfaceNodeRecords
      p x₀ equations CF C model.denominator P k hP hlower q).card : ℝ) ≤
      p.H ^ ε * (q.1 : ℝ) ^ 6 * D := by
  classical
  let records := occupiedRankSevenSurvivingNonSurfaceNodeRecords
    p x₀ equations CF C model.denominator P k hP hlower q
  by_cases hrecords : records.Nonempty
  · obtain ⟨record, hrecord⟩ := hrecords
    obtain ⟨z, hz, hsurvives⟩ :=
      survivingNonSurfaceNodeRecord_has_certificateWitness
        p x₀ equations CF C model.denominator P k hP hlower q
          record hrecord
    have hresidue :=
      card_depthSevenNormalizedChart_occupiedResidues_of_survives_cast_le
        hM₀ hε p x₀ equations CF C model hP q
          (MvPolynomial.eval (integralAffineMap x₀ z p.m)
            C.determinant) hsurvives hk hH
    have hrecordsNat :=
      card_occupiedRankSevenSurvivingNonSurfaceNodeRecords_le_card_mul
        p x₀ equations CF C model.denominator P k hP hlower q D
          hcomponents
    have hrecordsReal : (records.card : ℝ) ≤
        ((occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).card : ℝ) * D := by
      exact_mod_cast hrecordsNat
    exact hrecordsReal.trans
      (mul_le_mul_of_nonneg_right hresidue (Nat.cast_nonneg D))
  · have hempty : records = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrecords
    rw [show (occupiedRankSevenSurvivingNonSurfaceNodeRecords
      p x₀ equations CF C model.denominator P k hP hlower q).card = 0 by
        simpa only [records] using congrArg Finset.card hempty]
    simpa only [Nat.cast_zero] using
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg p.H_pos.le ε)
          (pow_nonneg (Nat.cast_nonneg q.1) 6))
      (Nat.cast_nonneg D))

/-- A surviving unequal-surface edge family has the expected
`lcm(q,r)^6` occurrence mass.  The witness carried by a nonempty record
certifies both endpoint moduli; their lcm is therefore coprime to the same
fixed certificate. -/
theorem card_occupiedRankSevenSurvivingSurfaceEdgeRecords_cast_le
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k)
    (hqSquare : Squarefree q.1) (hrSquare : Squarefree r.1)
    (D : ℕ)
    (hleft : ∀ rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
        (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).card ≤ D)
    (hright : ∀ rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C),
      (rankSevenSurfaceNodeComponents p x₀ equations CF C r.1
        (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).card ≤ D)
    (hfactorDepth : (Nat.lcm q.1 r.1).primeFactors.card ≤
      reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) ε ≤ p.H) :
    ((occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF C model.denominator P k hP hlower q r).card : ℝ) ≤
      p.H ^ ε * (Nat.lcm q.1 r.1 : ℝ) ^ 6 * (D * D) := by
  classical
  let records := occupiedRankSevenSurvivingSurfaceEdgeRecords
    p x₀ equations CF C model.denominator P k hP hlower q r
  by_cases hrecords : records.Nonempty
  · obtain ⟨record, hrecord⟩ := hrecords
    obtain ⟨z, hz, hqSurvives, hrSurvives⟩ :=
      survivingSurfaceEdgeRecord_has_certificateWitness
        p x₀ equations CF C model.denominator P k hP hlower q r
          record hrecord
    have hproductCoprime : Nat.Coprime (q.1 * r.1)
        (((p.m : ℤ) * model.denominator).natAbs) :=
      hqSurvives.1.mul_left hrSurvives.1
    have hlcmCoprime : Nat.Coprime (Nat.lcm q.1 r.1)
        (((p.m : ℤ) * model.denominator).natAbs) :=
      Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul q.1 r.1) hproductCoprime
    obtain ⟨hgoodm, hgoodden⟩ :=
      primeFactors_good_of_coprime_scale_denominator
        p (Nat.lcm q.1 r.1) model.denominator hlcmCoprime
    have hresidue :=
      card_depthSevenNormalizedChart_occupiedResidues_squarefree_cast_le
        hM₀ hε p x₀ equations CF C model (Nat.lcm q.1 r.1)
          (squarefree_lcm_of_squarefree hqSquare hrSquare)
          hgoodm hgoodden hfactorDepth hH
    have hrecordsNat :=
      card_occupiedRankSevenSurvivingSurfaceEdgeRecords_le_card_mul_sq
        p x₀ equations CF C model.denominator P k hP hlower q r D
          hleft hright
    have hrecordsReal : (records.card : ℝ) ≤
        ((occupiedIntegralResidues (Nat.lcm q.1 r.1)
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF C)).card : ℝ) * (D * D) := by
      exact_mod_cast hrecordsNat
    exact hrecordsReal.trans
      (mul_le_mul_of_nonneg_right hresidue
        (mul_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg D)))
  · have hempty : records = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrecords
    rw [show (occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF C model.denominator P k hP hlower q r).card = 0 by
        simpa only [records] using congrArg Finset.card hempty]
    simpa only [Nat.cast_zero] using
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg p.H_pos.le ε)
          (pow_nonneg (Nat.cast_nonneg (Nat.lcm q.1 r.1)) 6))
        (mul_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg D)))

end

end TranslatedDepthSeven
