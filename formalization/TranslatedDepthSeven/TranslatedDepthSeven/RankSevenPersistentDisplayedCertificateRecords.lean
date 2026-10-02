import TranslatedDepthSeven.RankSevenPersistentMultiplicityOneRecordCover
import TranslatedDepthSeven.ThreeCertificateReservoirSelection

/-!
# Persistent records from one displayed local certificate

The fixed-fibre and relative constructions naturally supply one displayed
clearing polynomial on each marked Jacobian patch.  This file turns that
literal certificate directly into persistent records.  It avoids choosing a
second colon-ideal menu: the mark type is `Fin 1`, its sole polynomial is the
displayed clearing polynomial, and every point has mark zero.

No geometric or counting estimate occurs in the statement.  The only size
hypotheses are the two exact certificate bounds required by the reservoir.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance rankSevenDisplayedCertificatePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 5000000

/-- The one-element menu attached to a displayed clearing polynomial. -/
def displayedCertificateOneMarkMenu
    (u : MvPolynomial (Fin 13) ℤ) :
    Fin 1 → MvPolynomial (Fin 13) ℤ := fun _ ↦ u

/-- The unique mark assigned to every integral point. -/
def displayedCertificateOneMarkOf : IntVector 13 → Fin 1 := fun _ ↦ 0

/-- A displayed multiplicity-one certificate of admitted height gives the
literal record assignment consumed by the persistent Salberger aggregate. -/
theorem exists_persistentRecords_of_displayedCertificate
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hdenominator : denominator ≠ 0)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (hX : X ⊆ rankSevenPersistentSurfaceCell
      p x₀ equations CF C denominator P k hP hlower I)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (clearing : MvPolynomial (Fin 13) ℤ)
    (H A : ℝ)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤ H ^ A → (E₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P E₁ E₂) k))
    (hfixedChartSize : ∀ z ∈ X,
      (((((p.m : ℤ) * denominator) *
        MvPolynomial.eval (integralAffineMap x₀ z p.m)
          C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ A)
    (hcertificate : ∀ z ∈ X,
      let Δ := integralSelectedJacobianChartCertificate
        localEquations selectedVar clearing z
      Δ ≠ 0 ∧
        ∀ (s : ℕ) (hs : s.Prime), ¬s ∣ Δ.natAbs →
          HasHilbertSamuelMultiplicityAt hs
            (projectiveSpecialFiberIdeal I)
            (fun j ↦ (integralAffineProjectivePoint z j : ZMod s)) 2 1)
    (hcertificateSize : ∀ z ∈ X,
      ((integralSelectedJacobianChartCertificate
        localEquations selectedVar clearing z).natAbs : ℝ) ≤ H ^ A) :
    (∀ z ∈ X,
      ∃ record : RankSevenPersistentRecord P k 1,
        record ∈ occupiedRankSevenPersistentRecords
          p x₀ equations CF C P k 1 ∧
        record.component = I ∧
        record.mark = displayedCertificateOneMarkOf z ∧
        (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
          record.residue ∧
        z ∈ rankSevenPersistentRecordPointCell
          p x₀ equations CF C displayedCertificateOneMarkOf record ∧
        survivesTwoCertificates record.modulus
          ((p.m : ℤ) * denominator)
          (MvPolynomial.eval
            (integralAffineMap x₀ z p.m) C.determinant) ∧
        Nat.Coprime record.modulus.1
          (integralSelectedJacobianChartCertificate
            localEquations selectedVar
              (displayedCertificateOneMarkMenu clearing
                (displayedCertificateOneMarkOf z)) z).natAbs ∧
        rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower
            z record.modulus = some I ∧
        ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
          HasHilbertSamuelMultiplicityAt
            ((Nat.mem_primeFactors.mp hs).1)
            (projectiveSpecialFiberIdeal I)
            (rankSevenPersistentRecordPrimePoint record s hs) 2 1) ∧
      X.card ≤ ∑ record ∈
          occupiedRankSevenPersistentMultiplicityOneRecords
            p x₀ equations CF C denominator P k hP hlower X 1
              localEquations selectedVar
              (displayedCertificateOneMarkMenu clearing)
              displayedCertificateOneMarkOf,
        (rankSevenPersistentRecordPointCell
          p x₀ equations CF C displayedCertificateOneMarkOf record).card := by
  classical
  have hrecords : ∀ z ∈ X,
      ∃ record : RankSevenPersistentRecord P k 1,
        record ∈ occupiedRankSevenPersistentRecords
          p x₀ equations CF C P k 1 ∧
        record.component = I ∧
        record.mark = displayedCertificateOneMarkOf z ∧
        (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
          record.residue ∧
        z ∈ rankSevenPersistentRecordPointCell
          p x₀ equations CF C displayedCertificateOneMarkOf record ∧
        survivesTwoCertificates record.modulus
          ((p.m : ℤ) * denominator)
          (MvPolynomial.eval
            (integralAffineMap x₀ z p.m) C.determinant) ∧
        Nat.Coprime record.modulus.1
          (integralSelectedJacobianChartCertificate
            localEquations selectedVar
              (displayedCertificateOneMarkMenu clearing
                (displayedCertificateOneMarkOf z)) z).natAbs ∧
        rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower
            z record.modulus = some I ∧
        ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
          HasHilbertSamuelMultiplicityAt
            ((Nat.mem_primeFactors.mp hs).1)
            (projectiveSpecialFiberIdeal I)
            (rankSevenPersistentRecordPrimePoint record s hs) 2 1 := by
    intro z hz
    let Δ : ℤ := integralSelectedJacobianChartCertificate
      localEquations selectedVar clearing z
    have hfixedNe : (p.m : ℤ) * denominator ≠ 0 := by
      have hm : (p.m : ℤ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt p.one_le_m)
      exact mul_ne_zero hm hdenominator
    have hzPersistent := hX hz
    have hzChart := (mem_rankSevenPersistentSurfaceCell_iff
      p x₀ equations CF C denominator P k hP hlower I z).1
        hzPersistent |>.1
    have hdetNe : MvPolynomial.eval
        (integralAffineMap x₀ z p.m) C.determinant ≠ 0 :=
      eval_chart_determinant_ne_zero_of_mem_normalizedChartCell
        p x₀ equations CF C hzChart
    have hΔNe : Δ ≠ 0 := (hcertificate z hz).1
    obtain ⟨q, hqSurvives, hqCoprimeΔ⟩ :=
      exists_reservoirModulus_avoiding_three_certificates_of_bounds
        hP hsurvival ((p.m : ℤ) * denominator)
          (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant)
          Δ hfixedNe hdetNe hΔNe (hfixedChartSize z hz)
          (hcertificateSize z hz)
    have hlabel := (mem_rankSevenPersistentSurfaceCell_iff
      p x₀ equations CF C denominator P k hP hlower I z).1 hzPersistent |>.2
        q hqSurvives
    obtain ⟨hselectedComponent, d, hdegree⟩ :=
      (rankSevenStaticSurfaceLabel_eq_some_iff p x₀ equations CF C
        denominator P k hP hlower z q I).1 hlabel
    have hcomponent : I ∈ rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1) :=
      rankSevenStaticSelectedSurfaceComponent_mem_nodeComponents
        p x₀ equations CF C denominator P k hP hlower z q I d
          hselectedComponent hdegree
    have hzI : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus I := by
      have hle := (selectedFiniteEquationComponent_spec
        (rankSevenStaticSourceSectionEquations p x₀ equations CF C
          denominator P k hP hlower q z)
        (fun i ↦ (integralAffineChartVector z i : ℚ))
        hselectedComponent).2
      exact fun f hf ↦ RingHom.mem_ker.mp (hle hf)
    let record : RankSevenPersistentRecord P k 1 :=
      { modulus := q
        residue := integralResidueVector z
        component := I
        mark := displayedCertificateOneMarkOf z }
    have hoccupied : record.residue ∈ occupiedIntegralResidues
        record.modulus.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) :=
      mem_occupiedIntegralResidues_iff.mpr ⟨z, hzChart, rfl⟩
    have hrecord : record ∈ occupiedRankSevenPersistentRecords
        p x₀ equations CF C P k 1 :=
      (mem_occupiedRankSevenPersistentRecords_iff
        p x₀ equations CF C P k 1 record).2 ⟨hoccupied, hcomponent⟩
    have hzRecord : z ∈ rankSevenPersistentRecordPointCell
        p x₀ equations CF C displayedCertificateOneMarkOf record :=
      (mem_rankSevenPersistentRecordPointCell_iff
        p x₀ equations CF C displayedCertificateOneMarkOf record z).2
          ⟨hzChart, rfl, hzI, rfl⟩
    refine ⟨record, hrecord, rfl, rfl, rfl, hzRecord, hqSurvives, ?_,
      hlabel, ?_⟩
    · simpa only [displayedCertificateOneMarkMenu, Δ] using hqCoprimeΔ
    · intro s hs
      have hsPrime : s.Prime := (Nat.mem_primeFactors.mp hs).1
      have hsDvd : s ∣ record.modulus.1 := Nat.dvd_of_mem_primeFactors hs
      have hsCoprimeΔ : Nat.Coprime s Δ.natAbs :=
        Nat.Coprime.of_dvd_left hsDvd hqCoprimeΔ
      have hmult := (hcertificate z hz).2 s hsPrime
        (hsPrime.coprime_iff_not_dvd.mp hsCoprimeΔ)
      rw [rankSevenPersistentRecordPrimePoint_eq_integralPoint
        p x₀ equations CF C displayedCertificateOneMarkOf record z hzRecord
          s hs]
      exact hmult
  refine ⟨hrecords, ?_⟩
  exact card_finitePointSet_le_sum_persistentMultiplicityOneRecordCells
    p x₀ equations CF C denominator P k 1 hP hlower I X hX
      localEquations selectedVar (displayedCertificateOneMarkMenu clearing)
      displayedCertificateOneMarkOf hrecords

end

end TranslatedDepthSeven
