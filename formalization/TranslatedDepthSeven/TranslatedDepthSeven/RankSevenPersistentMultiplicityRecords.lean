import TranslatedDepthSeven.RankSevenPersistentRecords
import TranslatedDepthSeven.FinitePrincipalOpenMultiplicityMenu
import TranslatedDepthSeven.ThreeCertificateReservoirSelection

/-!
# Persistent rank-seven surfaces: literal multiplicity-one records

This file performs the application-specific step which comes after the
static vertex--edge--persistent partition.  Fix one projective surface
component and one integral local complete-intersection presentation of an
open part of that component.  The finitely generated colon ideal gives a
finite, point-independent list of principal-open polynomials.  At every
point covered by the presentation, one member of that list gives a literal
nonzero integer certificate.

After multiplying the two integers already used in the rank-seven partition,
one application of the two-certificate reservoir clause selects a modulus
whose every prime factor is a multiplicity-one prime for the fixed surface.
The resulting modulus, residue, component, and menu index are retained in
an actual `RankSevenPersistentRecord`.

No component count, degree estimate, rational-point estimate, or packaged
geometric majorant is assumed here.  The two height premises are displayed
separately: the product of the old scale and chart certificates, and the new
local multiplicity certificate.  The former is supplied by
`scale_denominator_chartDeterminant_product_natAbs_le_heightPower`; uniform
control of the latter is the precise effective task left to the relative
algebraic-geometric construction.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance rankSevenPersistentMultiplicityPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

set_option maxHeartbeats 4000000

/-- The points carrying the fixed nonempty surface label `I` at every
modulus which survives the two certificates used in the static partition. -/
def rankSevenPersistentSurfaceCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ)) :
    Finset (IntVector 13) :=
  (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).filter
    fun z ↦ ∀ q : ReservoirModulus P k,
      survivesTwoCertificates q ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) →
      rankSevenStaticSurfaceLabel
        p x₀ equations CF C denominator P k hP hlower z q = some I

@[simp]
theorem mem_rankSevenPersistentSurfaceCell_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ)) (z : IntVector 13) :
    z ∈ rankSevenPersistentSurfaceCell
        p x₀ equations CF C denominator P k hP hlower I ↔
      z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C ∧
      ∀ q : ReservoirModulus P k,
        survivesTwoCertificates q ((p.m : ℤ) * denominator)
          (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) →
        rankSevenStaticSurfaceLabel
          p x₀ equations CF C denominator P k hP hlower z q = some I := by
  classical
  simp [rankSevenPersistentSurfaceCell]

/-- The projective point modulo a prime factor of a persistent record's
modulus, obtained by reducing the record's displayed residue vector. -/
def rankSevenPersistentRecordPrimePoint
    {P : Finset ℕ} {k markCount : ℕ}
    (record : RankSevenPersistentRecord P k markCount)
    (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors) :
    Fin 14 → ZMod s :=
  Fin.cases 1 fun i ↦
    ZMod.castHom (Nat.dvd_of_mem_primeFactors hs) (ZMod s)
      (record.residue i)

/-- Every integral point in a record reduces to the record's literal
projective point at each prime factor of its modulus. -/
theorem rankSevenPersistentRecordPrimePoint_eq_integralPoint
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k markCount : ℕ}
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (z : IntVector 13)
    (hz : z ∈ rankSevenPersistentRecordPointCell
      p x₀ equations CF C markOf record)
    (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors) :
    rankSevenPersistentRecordPrimePoint record s hs =
      fun i ↦ (integralAffineProjectivePoint z i : ZMod s) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [rankSevenPersistentRecordPrimePoint]
  · have hresidue := (mem_rankSevenPersistentRecordPointCell_iff
      p x₀ equations CF C markOf record z).mp hz |>.2.1
    have hreduce := congrArg
      (reduceResidueVector (Nat.dvd_of_mem_primeFactors hs)) hresidue
    have hj := congrFun hreduce j
    simpa [rankSevenPersistentRecordPrimePoint, reduceResidueVector,
      integralResidueVector] using hj.symm

/-! ## Affine-chart evaluation -/

/-- The literal dehomogenization map evaluates at `z` as the original
projective polynomial evaluates at `(1,z)`. -/
theorem eval_rationalDehomogenizeAtZeroHom
    {N : ℕ} (z : Fin N → ℤ)
    (f : MvPolynomial (Fin (N + 1)) ℚ) :
    MvPolynomial.eval (fun i ↦ (z i : ℚ))
        (rationalDehomogenizeAtZeroHom f) =
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) f := by
  let lhs : MvPolynomial (Fin (N + 1)) ℚ →+* ℚ :=
    (MvPolynomial.eval (fun i ↦ (z i : ℚ))).comp
      rationalDehomogenizeAtZeroHom
  let rhs : MvPolynomial (Fin (N + 1)) ℚ →+* ℚ :=
    MvPolynomial.eval fun i ↦ (integralAffineChartVector z i : ℚ)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs, rationalDehomogenizeAtZeroHom]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [lhs, rhs, rationalDehomogenizeAtZeroHom]
      · simp [lhs, rhs, rationalDehomogenizeAtZeroHom]
  exact RingHom.congr_fun hhom f

/-- A projective point `(1,z)` on `I` gives the exact affine-chart
vanishing hypothesis used by the integral specialization theorem. -/
theorem dehomogenized_point_of_projective_affineChart_point
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (z : Fin N → ℤ)
    (hz : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
      affineIdealZeroLocus I) :
    ∀ f ∈ Ideal.map rationalDehomogenizeAtZeroHom I,
      MvPolynomial.eval (fun i ↦ (z i : ℚ)) f = 0 := by
  have hle : Ideal.map rationalDehomogenizeAtZeroHom I ≤
      RingHom.ker (MvPolynomial.eval (fun i ↦ (z i : ℚ))) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker,
      eval_rationalDehomogenizeAtZeroHom]
    exact hz f hf
  intro f hf
  exact RingHom.mem_ker.mp (hle hf)

/-! ## Persistent records supplied by one local presentation -/

/-- One fixed integral local presentation of a persistent projective
surface gives a finite principal-open menu.  Once the displayed combined
certificates have the height admitted by the manuscript reservoir, every
point is assigned to an actual finite record whose modulus has
multiplicity one at all of its prime factors.

The local equality and nonzero Jacobian minor are required only on `X`.
In applications finitely many such sets, one for each local presentation,
cover the smooth part of the fixed surface; the complementary singular
locus is lower-dimensional. -/
theorem exists_finite_persistentSurface_multiplicityOne_records
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
    (hinitial : ∀ z ∈ X,
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P ((p.m : ℤ) * denominator)
          (MvPolynomial.eval
            (integralAffineMap x₀ z p.m) C.determinant)) k))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (hselected : Function.Injective selectedVar)
    (hIJ : Ideal.span (Set.range localEquations) ≤
      Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I))
    (hatPoint : ∀ z ∈ X,
      Ideal.map
          (algebraMap (MvPolynomial (Fin 13) ℚ)
            (Localization.AtPrime
              (RingHom.ker
                (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
          (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
            (Ideal.span (Set.range localEquations))) =
        Ideal.map
          (algebraMap (MvPolynomial (Fin 13) ℚ)
            (Localization.AtPrime
              (RingHom.ker
                (MvPolynomial.eval (fun i ↦ (z i : ℚ))))))
          (Ideal.map rationalDehomogenizeAtZeroHom I))
    (hminor : ∀ z ∈ X,
      MvPolynomial.eval z
        (selectedJacobianDeterminant localEquations selectedVar) ≠ 0)
    (H A : ℝ)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤ H ^ A → (E₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P E₁ E₂) k))
    (hfixedChartSize : ∀ z ∈ X,
      (((((p.m : ℤ) * denominator) *
        MvPolynomial.eval (integralAffineMap x₀ z p.m)
          C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ A) :
    ∃ (markCount : ℕ)
      (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
      (markOf : IntVector 13 → Fin markCount),
      0 < markCount ∧
      (∀ i, ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
          (projectiveIntegralClosureIdeal I),
        menu i * f ∈ Ideal.span (Set.range localEquations)) ∧
      (∀ z ∈ X,
        MvPolynomial.eval z (menu (markOf z)) ≠ 0 ∧
        let Δ := integralSelectedJacobianChartCertificate
          localEquations selectedVar (menu (markOf z)) z
        Δ ≠ 0 ∧
          (∀ (s : ℕ) (hs : s.Prime), ¬s ∣ Δ.natAbs →
            HasHilbertSamuelMultiplicityAt hs
              (projectiveSpecialFiberIdeal I)
              (fun i ↦ (integralAffineProjectivePoint z i : ZMod s)) 2 1) ∧
          ∀ Y : ℕ, (∀ j, (z j).natAbs ≤ Y) →
            Δ.natAbs ≤
              ((menu (markOf z)).support.card *
                  mvPolynomialCoefficientNatAbsMax (menu (markOf z)) *
                  max 1 Y ^ (menu (markOf z)).totalDegree) *
                ((selectedJacobianDeterminant
                    localEquations selectedVar).support.card *
                  mvPolynomialCoefficientNatAbsMax
                    (selectedJacobianDeterminant localEquations selectedVar) *
                  max 1 Y ^
                    (selectedJacobianDeterminant
                      localEquations selectedVar).totalDegree)) ∧
      ((∀ z ∈ X,
          ((integralSelectedJacobianChartCertificate
            localEquations selectedVar (menu (markOf z)) z).natAbs : ℝ) ≤
              H ^ A) →
        (∀ z ∈ X,
          ∃ record : RankSevenPersistentRecord P k markCount,
            record ∈ occupiedRankSevenPersistentRecords
              p x₀ equations CF C P k markCount ∧
            record.component = I ∧
            record.mark = markOf z ∧
            (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
              record.residue ∧
            z ∈ rankSevenPersistentRecordPointCell
              p x₀ equations CF C markOf record ∧
            survivesTwoCertificates record.modulus
              ((p.m : ℤ) * denominator)
              (MvPolynomial.eval
                (integralAffineMap x₀ z p.m) C.determinant) ∧
            Nat.Coprime record.modulus.1
              (integralSelectedJacobianChartCertificate
                localEquations selectedVar (menu (markOf z)) z).natAbs ∧
            rankSevenStaticSurfaceLabel
              p x₀ equations CF C denominator P k hP hlower
                z record.modulus = some I ∧
            ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
              HasHilbertSamuelMultiplicityAt
                ((Nat.mem_primeFactors.mp hs).1)
                (projectiveSpecialFiberIdeal I)
                (rankSevenPersistentRecordPrimePoint record s hs) 2 1) ∧
        X.card ≤ ∑ record ∈ occupiedRankSevenPersistentRecords
            p x₀ equations CF C P k markCount,
          (rankSevenPersistentRecordPointCell
            p x₀ equations CF C markOf record).card) := by
  classical
  have hpoint : ∀ z ∈ X,
      ∀ f ∈ Ideal.map rationalDehomogenizeAtZeroHom I,
        MvPolynomial.eval (fun i ↦ (z i : ℚ)) f = 0 := by
    intro z hz
    obtain ⟨qAllowed⟩ := hinitial z hz
    let q : ReservoirModulus P k :=
      certificateAllowedTwoModulusEmbedding hP
        ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant)
        qAllowed
    have hqSurvives : survivesTwoCertificates q
        ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) :=
      certificateAllowedTwoModulusEmbedding_survives hP
        ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant)
        qAllowed
    have hlabel := (mem_rankSevenPersistentSurfaceCell_iff
      p x₀ equations CF C denominator P k hP hlower I z).mp (hX hz) |>.2
      q hqSurvives
    obtain ⟨hselectedComponent, _d, _hdegree⟩ :=
      (rankSevenStaticSurfaceLabel_eq_some_iff
        p x₀ equations CF C denominator P k hP hlower z q I).mp hlabel
    have hzI : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus I := by
      have hle := (selectedFiniteEquationComponent_spec
        (rankSevenStaticSourceSectionEquations
          p x₀ equations CF C denominator P k hP hlower q z)
        (fun i ↦ (integralAffineChartVector z i : ℚ))
        hselectedComponent).2
      exact fun f hf ↦ RingHom.mem_ker.mp (hle hf)
    exact dehomogenized_point_of_projective_affineChart_point I z hzI
  obtain ⟨n, rawMenu, hrawClear, hrawCover⟩ :=
    exists_finite_projectiveSurface_multiplicityOne_menu
      (N := 13) (by norm_num) I localEquations selectedVar hselected hIJ
  let markCount := n + 1
  let menu : Fin markCount → MvPolynomial (Fin 13) ℤ :=
    Fin.cases 0 rawMenu
  have hmenuClear : ∀ i, ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
      (projectiveIntegralClosureIdeal I),
      menu i * f ∈ Ideal.span (Set.range localEquations) := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · intro f hf
      simp [menu]
    · intro f hf
      simpa [menu] using hrawClear j f hf
  have hchoice : ∀ z ∈ X, ∃ i : Fin markCount,
      MvPolynomial.eval z (menu i) ≠ 0 ∧
      let Δ := integralSelectedJacobianChartCertificate
        localEquations selectedVar (menu i) z
      Δ ≠ 0 ∧
        (∀ (s : ℕ) (hs : s.Prime), ¬s ∣ Δ.natAbs →
          HasHilbertSamuelMultiplicityAt hs
            (projectiveSpecialFiberIdeal I)
            (fun j ↦ (integralAffineProjectivePoint z j : ZMod s)) 2 1) ∧
        ∀ Y : ℕ, (∀ j, (z j).natAbs ≤ Y) →
          Δ.natAbs ≤
            ((menu i).support.card *
                mvPolynomialCoefficientNatAbsMax (menu i) *
                max 1 Y ^ (menu i).totalDegree) *
              ((selectedJacobianDeterminant
                  localEquations selectedVar).support.card *
                mvPolynomialCoefficientNatAbsMax
                  (selectedJacobianDeterminant localEquations selectedVar) *
                max 1 Y ^
                  (selectedJacobianDeterminant
                    localEquations selectedVar).totalDegree) := by
    intro z hz
    obtain ⟨i, hi, hiRest⟩ := hrawCover z (hpoint z hz)
      (hatPoint z hz) (hminor z hz)
    refine ⟨i.succ, ?_, ?_⟩
    · simpa [menu] using hi
    · simpa [menu] using hiRest
  let markOf : IntVector 13 → Fin markCount := fun z ↦
    if hz : z ∈ X then Classical.choose (hchoice z hz) else 0
  have hmarkSpec : ∀ z ∈ X,
      MvPolynomial.eval z (menu (markOf z)) ≠ 0 ∧
      let Δ := integralSelectedJacobianChartCertificate
        localEquations selectedVar (menu (markOf z)) z
      Δ ≠ 0 ∧
        (∀ (s : ℕ) (hs : s.Prime), ¬s ∣ Δ.natAbs →
          HasHilbertSamuelMultiplicityAt hs
            (projectiveSpecialFiberIdeal I)
            (fun j ↦ (integralAffineProjectivePoint z j : ZMod s)) 2 1) ∧
        ∀ Y : ℕ, (∀ j, (z j).natAbs ≤ Y) →
          Δ.natAbs ≤
            ((menu (markOf z)).support.card *
                mvPolynomialCoefficientNatAbsMax (menu (markOf z)) *
                max 1 Y ^ (menu (markOf z)).totalDegree) *
              ((selectedJacobianDeterminant
                  localEquations selectedVar).support.card *
                mvPolynomialCoefficientNatAbsMax
                  (selectedJacobianDeterminant localEquations selectedVar) *
                max 1 Y ^
                  (selectedJacobianDeterminant
                    localEquations selectedVar).totalDegree) := by
    intro z hz
    simpa only [markOf, dif_pos hz] using
      Classical.choose_spec (hchoice z hz)
  refine ⟨markCount, menu, markOf, by simp [markCount], hmenuClear,
    hmarkSpec, ?_⟩
  intro hlocalCertificateSize
  have hrecords : ∀ z ∈ X,
      ∃ record : RankSevenPersistentRecord P k markCount,
        record ∈ occupiedRankSevenPersistentRecords
          p x₀ equations CF C P k markCount ∧
        record.component = I ∧
        record.mark = markOf z ∧
        (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
          record.residue ∧
        z ∈ rankSevenPersistentRecordPointCell
          p x₀ equations CF C markOf record ∧
        survivesTwoCertificates record.modulus
          ((p.m : ℤ) * denominator)
          (MvPolynomial.eval
            (integralAffineMap x₀ z p.m) C.determinant) ∧
        Nat.Coprime record.modulus.1
          (integralSelectedJacobianChartCertificate
            localEquations selectedVar (menu (markOf z)) z).natAbs ∧
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
      localEquations selectedVar (menu (markOf z)) z
    have hfixedNe : (p.m : ℤ) * denominator ≠ 0 := by
      have hm : (p.m : ℤ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt p.one_le_m)
      exact mul_ne_zero hm hdenominator
    have hdetNe : MvPolynomial.eval
        (integralAffineMap x₀ z p.m) C.determinant ≠ 0 :=
      eval_chart_determinant_ne_zero_of_mem_normalizedChartCell
        p x₀ equations CF C
          ((mem_rankSevenPersistentSurfaceCell_iff
            p x₀ equations CF C denominator P k hP hlower I z).mp
              (hX hz)).1
    have hΔNe : Δ ≠ 0 := (hmarkSpec z hz).2.1
    obtain ⟨q, hqSurvives, hqCoprimeΔ⟩ :=
      exists_reservoirModulus_avoiding_three_certificates_of_bounds
        hP hsurvival ((p.m : ℤ) * denominator)
          (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant)
          Δ hfixedNe hdetNe hΔNe (hfixedChartSize z hz)
          (hlocalCertificateSize z hz)
    have hqSurvives' : survivesTwoCertificates q
        ((p.m : ℤ) * denominator)
        (MvPolynomial.eval (integralAffineMap x₀ z p.m) C.determinant) :=
      hqSurvives
    have hlabel := (mem_rankSevenPersistentSurfaceCell_iff
      p x₀ equations CF C denominator P k hP hlower I z).mp (hX hz) |>.2
      q hqSurvives'
    obtain ⟨hselectedComponent, d, hdegree⟩ :=
      (rankSevenStaticSurfaceLabel_eq_some_iff
        p x₀ equations CF C denominator P k hP hlower z q I).mp hlabel
    have hcomponent : I ∈ rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1) :=
      rankSevenStaticSelectedSurfaceComponent_mem_nodeComponents
        p x₀ equations CF C denominator P k hP hlower z q I d
          hselectedComponent hdegree
    have hzI : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus I := by
      have hle := (selectedFiniteEquationComponent_spec
        (rankSevenStaticSourceSectionEquations
          p x₀ equations CF C denominator P k hP hlower q z)
        (fun i ↦ (integralAffineChartVector z i : ℚ))
        hselectedComponent).2
      exact fun f hf ↦ RingHom.mem_ker.mp (hle hf)
    let record : RankSevenPersistentRecord P k markCount :=
      { modulus := q
        residue := integralResidueVector z
        component := I
        mark := markOf z }
    have hoccupied : record.residue ∈ occupiedIntegralResidues
        record.modulus.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) :=
      mem_occupiedIntegralResidues_iff.mpr ⟨z,
        ((mem_rankSevenPersistentSurfaceCell_iff
          p x₀ equations CF C denominator P k hP hlower I z).mp
            (hX hz)).1, rfl⟩
    have hrecord : record ∈ occupiedRankSevenPersistentRecords
        p x₀ equations CF C P k markCount :=
      (mem_occupiedRankSevenPersistentRecords_iff
        p x₀ equations CF C P k markCount record).2
          ⟨hoccupied, hcomponent⟩
    have hzRecord : z ∈ rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record :=
      (mem_rankSevenPersistentRecordPointCell_iff
        p x₀ equations CF C markOf record z).2
        ⟨((mem_rankSevenPersistentSurfaceCell_iff
          p x₀ equations CF C denominator P k hP hlower I z).mp
            (hX hz)).1, rfl, hzI, rfl⟩
    refine ⟨record, hrecord, rfl, rfl, rfl, hzRecord, hqSurvives',
      hqCoprimeΔ, hlabel, ?_⟩
    intro s hs
    have hsPrime : s.Prime := (Nat.mem_primeFactors.mp hs).1
    have hsDvd : s ∣ record.modulus.1 := Nat.dvd_of_mem_primeFactors hs
    have hsCoprimeΔ : Nat.Coprime s Δ.natAbs :=
      Nat.Coprime.of_dvd_left hsDvd hqCoprimeΔ
    have hmult := (hmarkSpec z hz).2.2.1 s hsPrime
      ((hsPrime.coprime_iff_not_dvd.mp hsCoprimeΔ))
    rw [rankSevenPersistentRecordPrimePoint_eq_integralPoint
      p x₀ equations CF C markOf record z hzRecord s hs]
    exact hmult
  refine ⟨hrecords, ?_⟩
  calc
    X.card ≤
        ((occupiedRankSevenPersistentRecords
          p x₀ equations CF C P k markCount).biUnion fun record ↦
            rankSevenPersistentRecordPointCell
              p x₀ equations CF C markOf record).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨record, hrecord, _hcomponent, _hmark, _hresidue,
          hzRecord, _⟩ :=
        hrecords z hz
      exact Finset.mem_biUnion.mpr ⟨record, hrecord, hzRecord⟩
    _ ≤ ∑ record ∈ occupiedRankSevenPersistentRecords
          p x₀ equations CF C P k markCount,
        (rankSevenPersistentRecordPointCell
          p x₀ equations CF C markOf record).card :=
      Finset.card_biUnion_le

end

end TranslatedDepthSeven
