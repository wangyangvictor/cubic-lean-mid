import CubicTenVariables.RankSevenRecordFreshDeterminantPrimePool
import CubicTenVariables.FixedIntegralSurfaceCanonicalReservoirTwoCap

/-!
# Uniform exceptional factors and prime caps for good record cells

The exceptional integer for the determinant theorem can be chosen before
partitioning into smooth-prime classes.  In fact the record modulus times
its entire fresh prime product is exactly the original pool product.  Thus
one fixed surface exceptional integer times that pool product works for
every record and every smooth-prime class.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace TranslatedDepthSeven

open MvPolynomial Published Filter
open HessianTheorem11
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The used and unused record primes partition the original prime pool.
In particular their product does not depend on the chosen record. -/
theorem recordModulus_mul_primeProduct_fresh_eq_pool
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount) :
    record.modulus.1 * primeProduct (recordFreshDeterminantPrimePool record) =
      primeProduct Ppool := by
  have hspec := recordModulus_primeFactors_spec hPpool record
  rw [← hspec.2.2, mul_comm]
  exact Finset.prod_sdiff hspec.1

/-- A canonical exceptional integer, shared by all records and all classes. -/
def goodRecordPoolExceptional (Ppool : Finset ℕ) (Dsurface : ℕ) : ℕ :=
  Dsurface * primeProduct Ppool

theorem goodRecordPoolExceptional_pos
    {Ppool : Finset ℕ} (hPpool : ∀ p ∈ Ppool, p.Prime)
    {Dsurface : ℕ} (hDsurface : 0 < Dsurface) :
    0 < goodRecordPoolExceptional Ppool Dsurface := by
  exact Nat.mul_pos hDsurface (Nat.pos_of_ne_zero (primeProduct_ne_zero hPpool))

theorem surface_dvd_goodRecordPoolExceptional
    (Ppool : Finset ℕ) (Dsurface : ℕ) :
    Dsurface ∣ goodRecordPoolExceptional Ppool Dsurface :=
  dvd_mul_right _ _

/-- This discharges the determinant theorem's `m * primeProduct Aclass`
divisibility hypothesis simultaneously for every class. -/
theorem recordModulus_mul_primeProduct_dvd_goodRecordPoolExceptional
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    {Aclass : Finset ℕ}
    (hAclass : Aclass ⊆ recordFreshDeterminantPrimePool record)
    (Dsurface : ℕ) :
    record.modulus.1 * primeProduct Aclass ∣
      goodRecordPoolExceptional Ppool Dsurface := by
  have hdiv : primeProduct Aclass ∣
      primeProduct (recordFreshDeterminantPrimePool record) :=
    Finset.prod_dvd_prod_of_subset _ _ id hAclass
  have hfull := mul_dvd_mul_left record.modulus.1 hdiv
  rw [recordModulus_mul_primeProduct_fresh_eq_pool hPpool record] at hfull
  exact hfull.trans (dvd_mul_left _ _)

/-- Any polynomial bound for the entire pool product gives a bound for the
canonical exceptional integer; the surface factor costs only one power of
height once the height exceeds that fixed factor. -/
theorem goodRecordPoolExceptional_le_pow
    {Ppool : Finset ℕ} {Dsurface H Apool : ℕ}
    (hDsurface : Dsurface ≤ H)
    (hpool : primeProduct Ppool ≤ H ^ Apool) :
    goodRecordPoolExceptional Ppool Dsurface ≤ H ^ (Apool + 1) := by
  calc
    Dsurface * primeProduct Ppool ≤ H * H ^ Apool :=
      Nat.mul_le_mul hDsurface hpool
    _ = H ^ (Apool + 1) := by rw [pow_succ, mul_comm]

/-- The whole-pool product admits a literal cap without any prime input. -/
theorem primeProduct_le_primeCap_pow_card (Ppool : Finset ℕ) :
    primeProduct Ppool ≤ PrimeSubsetPrefix.primeCap Ppool ^ Ppool.card :=
  Finset.prod_le_pow_card Ppool id _ (fun _ hp => PrimeSubsetPrefix.le_primeCap hp)

/-- Every fresh reservoir modulus inherits the sharp original reservoir
upper bound, retaining the manuscript-scale exponent. -/
theorem recordFresh_modulusReservoir_le_ceil
    {Ppool : Finset ℕ} {poolDepth markCount detDepth : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    {U : ℝ}
    (hupper : ∀ q : ReservoirModulus Ppool detDepth, (q.1 : ℝ) ≤ U) :
    ∀ q ∈ modulusReservoir (recordFreshDeterminantPrimePool record) detDepth,
      q ≤ ⌈U⌉₊ := by
  intro q hq
  have hqPool := mem_modulusReservoir_of_subset
    (recordFreshDeterminantPrimePool_subset record) hq
  exact_mod_cast (hupper ⟨q, hqPool⟩).trans (Nat.le_ceil U)

/-- The simple intrinsic cap needs no numerical hypothesis. -/
theorem recordFresh_modulusReservoir_le_primeCap_pow
    {Ppool : Finset ℕ} {poolDepth markCount detDepth : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount) :
    ∀ q ∈ modulusReservoir (recordFreshDeterminantPrimePool record) detDepth,
      q ≤ PrimeSubsetPrefix.primeCap Ppool ^ detDepth := by
  intro q hq
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  have hspec := Finset.mem_powersetCard.mp hs
  rw [← hspec.2]
  exact Finset.prod_le_pow_card s id _ (fun p hp =>
    PrimeSubsetPrefix.le_primeCap
      (recordFreshDeterminantPrimePool_subset record (hspec.1 hp)))

theorem recordFresh_prime_le_primeCap
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount) :
    ∀ p ∈ recordFreshDeterminantPrimePool record,
      p ≤ PrimeSubsetPrefix.primeCap Ppool := by
  intro p hp
  exact PrimeSubsetPrefix.le_primeCap
    (recordFreshDeterminantPrimePool_subset record hp)

/-- The canonical interval cap restricts to fresh record primes. -/
theorem recordFresh_prime_le_canonicalInterval
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    {A a H : ℝ}
    (hinterval : ∀ p ∈ Ppool,
      p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H)⌋₊) :
    ∀ p ∈ recordFreshDeterminantPrimePool record,
      p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H)⌋₊ := by
  intro p hp
  exact hinterval p (recordFreshDeterminantPrimePool_subset record hp)

/-- Point-count exclusions transfer to the uniform canonical exceptional
integer without a class-dependent point-count premise. -/
theorem surface_prime_count_goodRecordPoolExceptional
    {F : MvPolynomial (Fin 4) ℤ} {Kred : ℝ}
    {Ppool : Finset ℕ} {Dsurface : ℕ}
    (hcount : ∀ p : ℕ, p.Prime → ¬ p ∣ Dsurface →
      (Nat.card (SurfaceReductionZeroPoint p
        (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
          Kred * (p : ℝ) ^ 2) :
    ∀ p : ℕ, p.Prime → ¬ p ∣ goodRecordPoolExceptional Ppool Dsurface →
      (Nat.card (SurfaceReductionZeroPoint p
        (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
          Kred * (p : ℝ) ^ 2 := by
  intro p hp havoid
  exact hcount p hp (fun hdiv => havoid
    (hdiv.trans (surface_dvd_goodRecordPoolExceptional Ppool Dsurface)))

/-- The complete pool, with logarithmic prime cap and logarithmic depth,
has polynomial product size.  This is a bound for all available primes,
not just one fixed-cardinality reservoir modulus. -/
theorem logarithmicPrimeCap_pow_reservoirDepth_le_rpow
    {M C H : ℝ} (hM : 0 ≤ M) (hC : 1 ≤ C)
    (hH : 1 < H)
    (hloglog : 1 ≤ Real.log (Real.log H))
    (hlogC : Real.log (2 * C) ≤ Real.log (Real.log H)) :
    (⌊2 * (C * Real.log H)⌋₊ : ℝ) ^ reservoirDepth M H ≤
      H ^ (2 * (M + 1)) := by
  let L : ℝ := Real.log H
  let ell : ℝ := Real.log L
  let B : ℝ := 2 * (C * L)
  have hL : 0 < L := Real.log_pos hH
  have hell : 0 < ell := lt_of_lt_of_le zero_lt_one hloglog
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hB : 0 < B := by dsimp [B]; positivity
  have hBfloor : (⌊2 * (C * Real.log H)⌋₊ : ℝ) ≤ B :=
    Nat.floor_le hB.le
  have hlogB : Real.log B ≤ 2 * ell := by
    have hmul : B = (2 * C) * L := by dsimp [B]; ring
    rw [hmul, Real.log_mul (by positivity) hL.ne']
    dsimp [ell, L] at *
    linarith
  have hratio : 0 ≤ M * L / ell := by positivity
  have hdepth : (reservoirDepth M H : ℝ) ≤ (M + 1) * L / ell := by
    have hceil : (reservoirDepth M H : ℝ) ≤ M * L / ell + 1 :=
      (Nat.ceil_lt_add_one hratio).le
    have hone : 1 ≤ L / ell :=
      (le_div_iff₀ hell).mpr (by simpa using Real.log_le_self hL.le)
    calc
      (reservoirDepth M H : ℝ) ≤ M * L / ell + 1 := hceil
      _ ≤ M * L / ell + L / ell := add_le_add_right hone _
      _ = (M + 1) * L / ell := by ring
  have hexponent : Real.log B * (reservoirDepth M H : ℝ) ≤
      Real.log H * (2 * (M + 1)) := by
    calc
      Real.log B * (reservoirDepth M H : ℝ) ≤
          (2 * ell) * (reservoirDepth M H : ℝ) :=
        mul_le_mul_of_nonneg_right hlogB (Nat.cast_nonneg _)
      _ ≤ (2 * ell) * ((M + 1) * L / ell) := by gcongr
      _ = Real.log H * (2 * (M + 1)) := by dsimp [L]; field_simp
  calc
    (⌊2 * (C * Real.log H)⌋₊ : ℝ) ^ reservoirDepth M H ≤
        B ^ reservoirDepth M H := pow_le_pow_left₀ (Nat.cast_nonneg _) hBfloor _
    _ ≤ H ^ (2 * (M + 1)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hB,
        Real.rpow_def_of_pos (zero_lt_one.trans hH)]
      exact Real.exp_le_exp.mpr hexponent

/-- Explicit sufficient height for the two logarithmic comparisons above. -/
theorem logarithmicPrimeCap_pow_reservoirDepth_le_rpow_of_threshold
    {M C H : ℝ} (hM : 0 ≤ M) (hC : 1 ≤ C)
    (hH : max (Real.exp (Real.exp 1)) (Real.exp (2 * C)) ≤ H) :
    (⌊2 * (C * Real.log H)⌋₊ : ℝ) ^ reservoirDepth M H ≤
      H ^ (2 * (M + 1)) := by
  have hexp : Real.exp (Real.exp 1) ≤ H := (le_max_left _ _).trans hH
  have hHone : 1 < H :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hexp
  have hHpos : 0 < H := zero_lt_one.trans hHone
  have hlogHpos : 0 < Real.log H := Real.log_pos hHone
  have hexpLog : Real.exp 1 ≤ Real.log H :=
    (Real.le_log_iff_exp_le hHpos).mpr hexp
  have hloglog : 1 ≤ Real.log (Real.log H) :=
    (Real.le_log_iff_exp_le hlogHpos).mpr hexpLog
  have hCLog : 2 * C ≤ Real.log H :=
    (Real.le_log_iff_exp_le hHpos).mpr ((le_max_right _ _).trans hH)
  have hlogC : Real.log (2 * C) ≤ Real.log (Real.log H) :=
    Real.log_le_log (by positivity) hCLog
  exact logarithmicPrimeCap_pow_reservoirDepth_le_rpow hM hC
    hHone hloglog hlogC

/-- Polynomial product bound from the two literal published pool bounds. -/
theorem primeProduct_le_rpow_of_logarithmic_pool
    {Ppool : Finset ℕ} {M C H : ℝ} (hM : 0 ≤ M) (hC : 1 ≤ C)
    (hH : max (Real.exp (Real.exp 1)) (Real.exp (2 * C)) ≤ H)
    (hcard : Ppool.card = reservoirDepth M H)
    (hinterval : ∀ p ∈ Ppool, p ≤ ⌊2 * (C * Real.log H)⌋₊) :
    (primeProduct Ppool : ℝ) ≤ H ^ (2 * (M + 1)) := by
  have hprod : primeProduct Ppool ≤
      ⌊2 * (C * Real.log H)⌋₊ ^ Ppool.card :=
    Finset.prod_le_pow_card Ppool id _ hinterval
  have hcast : (primeProduct Ppool : ℝ) ≤
      (⌊2 * (C * Real.log H)⌋₊ : ℝ) ^ reservoirDepth M H := by
    rw [← hcard]
    exact_mod_cast hprod
  exact hcast.trans
    (logarithmicPrimeCap_pow_reservoirDepth_le_rpow_of_threshold hM hC hH)

/-- The complete canonical pool has a fixed polynomial height exponent.
This removes a whole-pool product estimate from later exceptional-integer
constructions. -/
theorem eventually_primeProduct_manuscriptPrimePoolAt_le_rpow
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1) :
    ∀ᶠ H : ℝ in atTop,
      (primeProduct (manuscriptPrimePoolAt A a H) : ℝ) ≤
        H ^ (2 * (manuscriptPoolDepthCoefficient A a + 1)) := by
  have hM : 0 ≤ manuscriptPoolDepthCoefficient A a := by
    dsimp [manuscriptPoolDepthCoefficient]; positivity
  have hC : 1 ≤ manuscriptPrimeIntervalCoefficient A a := by
    dsimp [manuscriptPrimeIntervalCoefficient, manuscriptPoolDepthCoefficient]
    nlinarith
  filter_upwards [eventually_card_manuscriptPrimePoolAt hA ha haOne,
    eventually_manuscriptPrimePoolAt_le_upperEndpoint hA ha haOne,
    eventually_ge_atTop (max (Real.exp (Real.exp 1))
      (Real.exp (2 * manuscriptPrimeIntervalCoefficient A a)))]
    with H hcard hinterval hH
  exact primeProduct_le_rpow_of_logarithmic_pool hM hC hH hcard hinterval

/-- Natural height version, with one fixed natural exponent independent of
the record, determinant class, and height. -/
theorem eventually_primeProduct_manuscriptPrimePoolAt_le_nat_pow
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1) :
    ∀ᶠ H : ℕ in atTop,
      primeProduct (manuscriptPrimePoolAt A a (H : ℝ)) ≤
        H ^ ⌈2 * (manuscriptPoolDepthCoefficient A a + 1)⌉₊ := by
  have hreal := eventually_primeProduct_manuscriptPrimePoolAt_le_rpow hA ha haOne
  have hnat : ∀ᶠ H : ℕ in atTop,
      (primeProduct (manuscriptPrimePoolAt A a (H : ℝ)) : ℝ) ≤
        (H : ℝ) ^ (2 * (manuscriptPoolDepthCoefficient A a + 1)) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop (1 : ℕ)] with H hprod hH
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hpower := Real.rpow_le_rpow_of_exponent_le hHreal
    (Nat.le_ceil (2 * (manuscriptPoolDepthCoefficient A a + 1)))
  have hbound := hprod.trans hpower
  rw [Real.rpow_natCast] at hbound
  exact_mod_cast hbound

/-- The fixed surface exceptional factor costs one additional height power,
and the chosen exceptional integer is uniform over every class and record. -/
theorem eventually_goodRecordPoolExceptional_le_nat_pow
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1)
    (Dsurface : ℕ) :
    ∀ᶠ H : ℕ in atTop,
      goodRecordPoolExceptional (manuscriptPrimePoolAt A a (H : ℝ)) Dsurface ≤
        H ^ (⌈2 * (manuscriptPoolDepthCoefficient A a + 1)⌉₊ + 1) := by
  filter_upwards [eventually_primeProduct_manuscriptPrimePoolAt_le_nat_pow
    hA ha haOne, eventually_ge_atTop Dsurface] with H hpool hD
  exact goodRecordPoolExceptional_le_pow hD hpool

/-- The original pool's prime cap bounds every fixed-depth fresh product. -/
theorem recordFresh_modulusReservoir_le_pow_of_primeCap
    {Ppool : Finset ℕ} {poolDepth markCount detDepth Rprime : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    (hcap : ∀ p ∈ Ppool, p ≤ Rprime) :
    ∀ q ∈ modulusReservoir (recordFreshDeterminantPrimePool record) detDepth,
      q ≤ Rprime ^ detDepth := by
  intro q hq
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  have hspec := Finset.mem_powersetCard.mp hs
  rw [← hspec.2]
  exact Finset.prod_le_pow_card s id _ (fun p hp =>
    hcap p (recordFreshDeterminantPrimePool_subset record (hspec.1 hp)))

/-- Primality of the canonical pool holds even below the asymptotic
threshold: its totalizing fallback is the empty set. -/
theorem prime_of_mem_manuscriptPrimePoolAt
    {A a H : ℝ} {p : ℕ} (hp : p ∈ manuscriptPrimePoolAt A a H) :
    p.Prime := by
  dsimp only [manuscriptPrimePoolAt] at hp
  split at hp
  · exact prime_of_mem_comparablePrimePool hp
  · simp only [Finset.notMem_empty] at hp

/-- The fixed-surface point-count theorem and elementary logarithmic-pool
bounds supply a single exceptional integer and all prime arithmetic needed
for every persistent record and every fresh smooth-prime class.  The only
point-count inputs are the existing explicit integrality-openness and
plane-curve Weil statements; there is no class-dependent exceptional factor
or point-count hypothesis.

The generic intrinsic modulus cap below is available without a reservoir
upper-bound premise.  When the sharper manuscript-scale reservoir upper
bound is available, `recordFresh_modulusReservoir_le_ceil` preserves it. -/
theorem exists_canonical_goodRecordPrimeBounds
    (integralityOpen : CubicTenVariables.Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : CubicTenVariables.Literature.AffinePlaneCurveWeil)
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4)
      GeometricField ⧸
        Ideal.span {map (Int.castRingHom
          GeometricField) F}))
    (Kred : ℝ) (hKred : 1 < Kred)
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1) :
    ∃ Dsurface : ℕ, 0 < Dsurface ∧
      ∀ᶠ H : ℕ in atTop,
        let Ppool := manuscriptPrimePoolAt A a (H : ℝ)
        let Dex := goodRecordPoolExceptional Ppool Dsurface
        let Rprime := ⌊2 * (manuscriptPrimeIntervalCoefficient A a *
          Real.log (H : ℝ))⌋₊
        0 < Dex ∧
        Dex ≤ H ^ (⌈2 * (manuscriptPoolDepthCoefficient A a + 1)⌉₊ + 1) ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ Dex →
          (Nat.card (SurfaceReductionZeroPoint p
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
              Kred * (p : ℝ) ^ 2) ∧
        (∀ p ∈ Ppool, p ≤ Rprime) ∧
        (∀ (poolDepth markCount detDepth : ℕ)
            (record : RankSevenPersistentRecord Ppool poolDepth markCount),
          (∀ Aclass ⊆ recordFreshDeterminantPrimePool record,
            record.modulus.1 * primeProduct Aclass ∣ Dex) ∧
          (∀ q ∈ modulusReservoir (recordFreshDeterminantPrimePool record)
              detDepth, q ≤ Rprime ^ detDepth)) := by
  obtain ⟨Dsurface, hDsurface, hcount⟩ :=
    exists_fixed_integral_surface_prime_count integralityOpen curveWeil hd
      F hF0 hF hgeom Kred hKred
  refine ⟨Dsurface, hDsurface, ?_⟩
  have hcap : ∀ᶠ H : ℕ in atTop,
      ∀ p ∈ manuscriptPrimePoolAt A a (H : ℝ),
        p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient A a *
          Real.log (H : ℝ))⌋₊ :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_manuscriptPrimePoolAt_le_upperEndpoint hA ha haOne)
  filter_upwards [eventually_goodRecordPoolExceptional_le_nat_pow
    hA ha haOne Dsurface, hcap] with H hheight hcapH
  dsimp only
  have hPpool : ∀ p ∈ manuscriptPrimePoolAt A a (H : ℝ), p.Prime :=
    fun _ hp => prime_of_mem_manuscriptPrimePoolAt hp
  refine ⟨goodRecordPoolExceptional_pos hPpool hDsurface, hheight,
    surface_prime_count_goodRecordPoolExceptional hcount, hcapH, ?_⟩
  intro poolDepth markCount detDepth record
  exact ⟨fun _ hclass =>
    recordModulus_mul_primeProduct_dvd_goodRecordPoolExceptional hPpool
      record hclass Dsurface,
    recordFresh_modulusReservoir_le_pow_of_primeCap record hcapH⟩

end TranslatedDepthSeven
