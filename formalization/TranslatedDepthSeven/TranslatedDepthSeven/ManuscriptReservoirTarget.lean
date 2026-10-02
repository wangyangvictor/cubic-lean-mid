import TranslatedDepthSeven.ComparableCrossing
import TranslatedDepthSeven.ReservoirSubpower

/-!
# The manuscript target and the size of the resulting moduli

This file isolates the real target occurring in the square-free reservoir
lemma.  It contains no prime-supply theorem and no smooth-specialization
certificate.  Its finite input is simply a set of primes in one dyadic
interval.  The crossing cardinality is defined at the common integral lower
endpoint, and the ensuing modulus and adjacent least common multiple are
bounded without any asymptotic notation.
-/

namespace TranslatedDepthSeven

open Filter
open scoped Topology

noncomputable section

/-- The integral target corresponding to `Cres * T ^ a`. -/
def manuscriptReservoirTarget (Cres T a : ℝ) : ℕ :=
  ⌈Cres * T ^ a⌉₊

/-- The common integral lower endpoint of the primes in
`(C * log H, 2 * C * log H]`. -/
def manuscriptReservoirLower (C H : ℝ) : ℕ :=
  ⌊C * Real.log H⌋₊ + 1

/-- The least cardinality whose lower-endpoint product reaches the real
manuscript target. -/
def manuscriptReservoirCrossing (C Cres H T a : ℝ)
    (hscale : 1 ≤ C * Real.log H) : ℕ :=
  comparableCrossing (manuscriptReservoirLower C H)
    (manuscriptReservoirTarget Cres T a)
    (by simpa only [manuscriptReservoirLower] using
      two_le_floor_add_one hscale)

theorem manuscriptReservoirTarget_cast_lower (Cres T a : ℝ) :
    Cres * T ^ a ≤ (manuscriptReservoirTarget Cres T a : ℝ) := by
  exact Nat.le_ceil _

theorem manuscriptReservoirTarget_cast_lt_add_one
    {Cres T a : ℝ} (hCres : 0 ≤ Cres) (hT : 0 ≤ T) :
    (manuscriptReservoirTarget Cres T a : ℝ) < Cres * T ^ a + 1 := by
  exact Nat.ceil_lt_add_one (mul_nonneg hCres (Real.rpow_nonneg hT a))

theorem one_lt_manuscriptReservoirTarget
    {Cres T a : ℝ} (hCres : 1 < Cres) (hT : 1 ≤ T) (ha : 0 ≤ a) :
    1 < manuscriptReservoirTarget Cres T a := by
  have hpow : 1 ≤ T ^ a := Real.one_le_rpow hT ha
  have hreal : 1 < Cres * T ^ a :=
    lt_of_lt_of_le hCres (by
      simpa using mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hCres.le))
  have hceil : (1 : ℝ) < (manuscriptReservoirTarget Cres T a : ℝ) :=
    hreal.trans_le (manuscriptReservoirTarget_cast_lower Cres T a)
  exact_mod_cast hceil

theorem manuscriptReservoirTarget_cast_le_two_mul
    {Cres T a : ℝ} (hCres : 1 ≤ Cres) (hT : 1 ≤ T) (ha : 0 ≤ a) :
    (manuscriptReservoirTarget Cres T a : ℝ) ≤ 2 * Cres * T ^ a := by
  have hpow : 1 ≤ T ^ a := Real.one_le_rpow hT ha
  have hone : 1 ≤ Cres * T ^ a := by nlinarith
  exact (manuscriptReservoirTarget_cast_lt_add_one (zero_le_one.trans hCres)
    (zero_le_one.trans hT)).le.trans (by nlinarith)

theorem manuscriptReservoirLower_cast_le
    {C H : ℝ} (hscale : 1 ≤ C * Real.log H) :
    (manuscriptReservoirLower C H : ℝ) ≤ 2 * C * Real.log H := by
  have hx0 : 0 ≤ C * Real.log H := zero_le_one.trans hscale
  have hfloor : ((⌊C * Real.log H⌋₊ : ℕ) : ℝ) ≤ C * Real.log H :=
    Nat.floor_le hx0
  dsimp only [manuscriptReservoirLower]
  push_cast
  nlinarith

/-- Exact endpoint bounds for a modulus formed from any `k` integers in the
dyadic interval.  Primality is irrelevant for this product estimate. -/
theorem manuscript_crossing_primeProduct_bounds
    {C Cres H T a : ℝ} (hscale : 1 ≤ C * Real.log H)
    (hCres : 1 < Cres) (hT : 1 ≤ T) (ha : 0 ≤ a)
    {M : ℕ} {s : Finset ℕ}
    (hinterval : ∀ p ∈ s,
      ⌊C * Real.log H⌋₊ < p ∧ p ≤ ⌊2 * (C * Real.log H)⌋₊)
    (hcard : s.card = manuscriptReservoirCrossing C Cres H T a hscale)
    (hkM : manuscriptReservoirCrossing C Cres H T a hscale ≤ M) :
    manuscriptReservoirTarget Cres T a ≤ primeProduct s ∧
      primeProduct s <
        manuscriptReservoirTarget Cres T a *
          manuscriptReservoirLower C H * 2 ^ M := by
  let L := manuscriptReservoirLower C H
  let Q := manuscriptReservoirTarget Cres T a
  let k := manuscriptReservoirCrossing C Cres H T a hscale
  have hL : 2 ≤ L := by
    simpa only [L, manuscriptReservoirLower] using two_le_floor_add_one hscale
  have hx0 : 0 ≤ C * Real.log H := zero_le_one.trans hscale
  have hU : ⌊2 * (C * Real.log H)⌋₊ ≤ 2 * L := by
    simpa only [L, manuscriptReservoirLower] using
      floor_two_mul_le_two_mul_floor_add_one hx0
  have hbounds : L ^ s.card ≤ primeProduct s ∧
      primeProduct s ≤ (2 * L) ^ s.card := by
    constructor
    · simpa [primeProduct] using Finset.prod_le_prod
        (fun _ _ ↦ Nat.zero_le L)
        (fun p hp ↦ by
          have hp' := (hinterval p hp).1
          simpa only [L, manuscriptReservoirLower] using hp')
    · exact Finset.prod_le_pow_card s id (2 * L) fun p hp ↦
        (hinterval p hp).2.trans hU
  have hspec : Q ≤ L ^ k := by
    simpa only [Q, L, k, manuscriptReservoirCrossing] using
      comparableCrossing_spec L Q hL
  have hQ : 1 < Q := by
    simpa only [Q] using one_lt_manuscriptReservoirTarget hCres hT ha
  have hover : L ^ k < Q * L :=
    comparableCrossing_power_lt_overshoot hQ
  constructor
  · exact hspec.trans (by simpa only [hcard] using hbounds.1)
  · calc
      primeProduct s ≤ (2 * L) ^ s.card := hbounds.2
      _ = 2 ^ k * L ^ k := by rw [hcard, mul_pow]
      _ < 2 ^ k * (Q * L) :=
        Nat.mul_lt_mul_of_pos_left hover (pow_pos (by omega) _)
      _ ≤ 2 ^ M * (Q * L) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hkM)
      _ = Q * L * 2 ^ M := by ring

/-- Exact endpoint bounds for the least common multiple attached to a
one-prime exchange. -/
theorem manuscript_crossing_oneExchange_lcm_bounds
    {C Cres H T a : ℝ} (hscale : 1 ≤ C * Real.log H)
    (hCres : 1 < Cres) (hT : 1 ≤ T) (ha : 0 ≤ a)
    {M : ℕ} {s t : Finset ℕ}
    (hprimeInterval : ∀ p ∈ s ∪ t,
      p.Prime ∧ ⌊C * Real.log H⌋₊ < p ∧
        p ≤ ⌊2 * (C * Real.log H)⌋₊)
    (hcard : s.card = manuscriptReservoirCrossing C Cres H T a hscale)
    (hkM : manuscriptReservoirCrossing C Cres H T a hscale ≤ M)
    (hex : OneExchange s t) :
    manuscriptReservoirTarget Cres T a ≤
        Nat.lcm (primeProduct s) (primeProduct t) ∧
      Nat.lcm (primeProduct s) (primeProduct t) <
        2 * manuscriptReservoirTarget Cres T a *
          manuscriptReservoirLower C H ^ 2 * 2 ^ M := by
  let u := s ∪ t
  let L := manuscriptReservoirLower C H
  let Q := manuscriptReservoirTarget Cres T a
  let k := manuscriptReservoirCrossing C Cres H T a hscale
  have hprime : ∀ p ∈ u, p.Prime := fun p hp ↦ (hprimeInterval p hp).1
  have hlcm : Nat.lcm (primeProduct s) (primeProduct t) = primeProduct u := by
    exact lcm_primeProducts hprime Finset.subset_union_left Finset.subset_union_right
  have hUnionCard : u.card = k + 1 := by
    simpa only [u, hcard] using card_union_eq_succ_of_oneExchange hex
  have hL : 2 ≤ L := by
    simpa only [L, manuscriptReservoirLower] using two_le_floor_add_one hscale
  have hx0 : 0 ≤ C * Real.log H := zero_le_one.trans hscale
  have hU : ⌊2 * (C * Real.log H)⌋₊ ≤ 2 * L := by
    simpa only [L, manuscriptReservoirLower] using
      floor_two_mul_le_two_mul_floor_add_one hx0
  have hUpper : primeProduct u ≤ (2 * L) ^ u.card := by
    exact Finset.prod_le_pow_card u id (2 * L) fun p hp ↦
      (hprimeInterval p hp).2.2.trans hU
  have hQ : 1 < Q := by
    simpa only [Q] using one_lt_manuscriptReservoirTarget hCres hT ha
  have hover : L ^ k < Q * L :=
    comparableCrossing_power_lt_overshoot hQ
  have hmod := manuscript_crossing_primeProduct_bounds hscale hCres hT ha
    (s := s) (M := M)
    (fun p hp ↦ ⟨(hprimeInterval p (Finset.mem_union_left t hp)).2.1,
      (hprimeInterval p (Finset.mem_union_left t hp)).2.2⟩)
    hcard hkM
  constructor
  · have hdiv : primeProduct s ∣ Nat.lcm (primeProduct s) (primeProduct t) :=
      Nat.dvd_lcm_left _ _
    exact hmod.1.trans (Nat.le_of_dvd (by
      rw [hlcm]
      exact Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)) hdiv)
  · rw [hlcm]
    calc
      primeProduct u ≤ (2 * L) ^ u.card := hUpper
      _ = 2 ^ (k + 1) * (L ^ k * L) := by
        simp only [hUnionCard, mul_pow, pow_succ]
        ring
      _ < 2 ^ (k + 1) * ((Q * L) * L) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_right hover (by omega))
          (pow_pos (by omega) _)
      _ ≤ 2 ^ (M + 1) * ((Q * L) * L) :=
        Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hkM 1))
      _ = 2 * Q * L ^ 2 * 2 ^ M := by rw [pow_succ]; ring

/-- The exact finite modulus estimate after casting to the manuscript's real
parameters.  The only analytic input is the already proved subpower estimate
for `2 ^ reservoirDepth`. -/
theorem manuscript_crossing_primeProduct_real_bounds
    {C Cres M0 H T a δ : ℝ} (hscale : 1 ≤ C * Real.log H)
    (hCres : 1 < Cres) (hT : 1 ≤ T) (ha : 0 ≤ a)
    (hM0 : 0 ≤ M0) (hδ : 0 < δ)
    (hthreshold : reservoirSubpowerThreshold M0 2 δ ≤ H)
    {s : Finset ℕ}
    (hinterval : ∀ p ∈ s,
      ⌊C * Real.log H⌋₊ < p ∧ p ≤ ⌊2 * (C * Real.log H)⌋₊)
    (hcard : s.card = manuscriptReservoirCrossing C Cres H T a hscale)
    (hdepth : manuscriptReservoirCrossing C Cres H T a hscale ≤
      reservoirDepth M0 H) :
    Cres * T ^ a ≤ (primeProduct s : ℝ) ∧
      (primeProduct s : ℝ) ≤
        4 * C * Cres * T ^ a * Real.log H * H ^ δ := by
  have hnat := manuscript_crossing_primeProduct_bounds hscale hCres hT ha
    (M := reservoirDepth M0 H) hinterval hcard hdepth
  have hnatCast : (primeProduct s : ℝ) ≤
      (manuscriptReservoirTarget Cres T a : ℝ) *
        (manuscriptReservoirLower C H : ℝ) *
          (2 : ℝ) ^ reservoirDepth M0 H := by
    exact_mod_cast hnat.2.le
  have htarget := manuscriptReservoirTarget_cast_le_two_mul hCres.le hT ha
  have hlower := manuscriptReservoirLower_cast_le hscale
  have hsub : (2 : ℝ) ^ reservoirDepth M0 H ≤ H ^ δ :=
    reservoirBase_pow_depth_le_rpow hM0 (by norm_num) hδ hthreshold
  have htargetNonneg : 0 ≤ 2 * Cres * T ^ a := by positivity
  have hlowerNonneg : 0 ≤ 2 * C * Real.log H := by nlinarith
  constructor
  · exact (manuscriptReservoirTarget_cast_lower Cres T a).trans <| by
      exact_mod_cast hnat.1
  · calc
      (primeProduct s : ℝ) ≤
          (manuscriptReservoirTarget Cres T a : ℝ) *
            (manuscriptReservoirLower C H : ℝ) *
              (2 : ℝ) ^ reservoirDepth M0 H := hnatCast
      _ ≤ (2 * Cres * T ^ a) * (2 * C * Real.log H) * H ^ δ := by
        gcongr
      _ = 4 * C * Cres * T ^ a * Real.log H * H ^ δ := by ring

/-- Real endpoint bounds for an adjacent least common multiple. -/
theorem manuscript_crossing_oneExchange_lcm_real_bounds
    {C Cres M0 H T a δ : ℝ} (hscale : 1 ≤ C * Real.log H)
    (hCres : 1 < Cres) (hT : 1 ≤ T) (ha : 0 ≤ a)
    (hM0 : 0 ≤ M0) (hδ : 0 < δ)
    (hthreshold : reservoirSubpowerThreshold M0 2 δ ≤ H)
    {s t : Finset ℕ}
    (hprimeInterval : ∀ p ∈ s ∪ t,
      p.Prime ∧ ⌊C * Real.log H⌋₊ < p ∧
        p ≤ ⌊2 * (C * Real.log H)⌋₊)
    (hcard : s.card = manuscriptReservoirCrossing C Cres H T a hscale)
    (hdepth : manuscriptReservoirCrossing C Cres H T a hscale ≤
      reservoirDepth M0 H)
    (hex : OneExchange s t) :
    Cres * T ^ a ≤
        (Nat.lcm (primeProduct s) (primeProduct t) : ℝ) ∧
      (Nat.lcm (primeProduct s) (primeProduct t) : ℝ) ≤
        16 * C ^ 2 * Cres * T ^ a * (Real.log H) ^ 2 * H ^ δ := by
  have hnat := manuscript_crossing_oneExchange_lcm_bounds hscale hCres hT ha
    (M := reservoirDepth M0 H) hprimeInterval hcard hdepth hex
  have hnatCast : (Nat.lcm (primeProduct s) (primeProduct t) : ℝ) ≤
      2 * (manuscriptReservoirTarget Cres T a : ℝ) *
        (manuscriptReservoirLower C H : ℝ) ^ 2 *
          (2 : ℝ) ^ reservoirDepth M0 H := by
    exact_mod_cast hnat.2.le
  have htarget := manuscriptReservoirTarget_cast_le_two_mul hCres.le hT ha
  have hlower := manuscriptReservoirLower_cast_le hscale
  have hsub : (2 : ℝ) ^ reservoirDepth M0 H ≤ H ^ δ :=
    reservoirBase_pow_depth_le_rpow hM0 (by norm_num) hδ hthreshold
  have htargetNonneg : 0 ≤ 2 * Cres * T ^ a := by positivity
  have hlowerNonneg : 0 ≤ 2 * C * Real.log H := by nlinarith
  constructor
  · exact (manuscriptReservoirTarget_cast_lower Cres T a).trans <| by
      exact_mod_cast hnat.1
  · calc
      (Nat.lcm (primeProduct s) (primeProduct t) : ℝ) ≤
          2 * (manuscriptReservoirTarget Cres T a : ℝ) *
            (manuscriptReservoirLower C H : ℝ) ^ 2 *
              (2 : ℝ) ^ reservoirDepth M0 H := hnatCast
      _ ≤ 2 * (2 * Cres * T ^ a) *
          (2 * C * Real.log H) ^ 2 * H ^ δ := by
        gcongr
      _ = 16 * C ^ 2 * Cres * T ^ a * (Real.log H) ^ 2 * H ^ δ := by
        ring

/-- One logarithmic factor and one `H ^ δ` factor cost at most two copies
of `δ` in the exponent. -/
theorem log_mul_rpow_le_inv_mul_rpow_two
    {H δ : ℝ} (hH : 1 ≤ H) (hδ : 0 < δ) :
    Real.log H * H ^ δ ≤ δ⁻¹ * H ^ (2 * δ) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hlog := Real.log_le_rpow_div hH0 hδ
  calc
    Real.log H * H ^ δ ≤ (H ^ δ / δ) * H ^ δ :=
      mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hH0 δ)
    _ = δ⁻¹ * H ^ (2 * δ) := by
      rw [show 2 * δ = δ + δ by ring, Real.rpow_add hHpos]
      ring

/-- Two logarithmic factors and one `H ^ δ` factor cost three copies of
`δ` in the exponent. -/
theorem log_sq_mul_rpow_le_inv_sq_mul_rpow_three
    {H δ : ℝ} (hH : 1 ≤ H) (hδ : 0 < δ) :
    (Real.log H) ^ 2 * H ^ δ ≤ (δ⁻¹) ^ 2 * H ^ (3 * δ) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hlogNonneg : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlog := Real.log_le_rpow_div hH0 hδ
  have hlogSq : (Real.log H) ^ 2 ≤ (H ^ δ / δ) ^ 2 := by
    gcongr
  calc
    (Real.log H) ^ 2 * H ^ δ ≤ (H ^ δ / δ) ^ 2 * H ^ δ :=
      mul_le_mul_of_nonneg_right hlogSq (Real.rpow_nonneg hH0 δ)
    _ = (δ⁻¹) ^ 2 * H ^ (3 * δ) := by
      rw [show 3 * δ = (δ + δ) + δ by ring,
        Real.rpow_add hHpos, Real.rpow_add hHpos]
      ring

/-- The two elementary large-height conditions used below hold
simultaneously.  This is the complete asymptotic content needed for the
target-size estimates; prime supply is deliberately absent. -/
theorem eventually_manuscriptReservoir_scale_and_threshold
    {C M0 ε : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ H : ℝ in atTop,
      1 ≤ C * Real.log H ∧
        reservoirSubpowerThreshold M0 2 (ε / 3) ≤ H := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hscale : Tendsto (fun H : ℝ ↦ C * Real.log H) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hCpos
  filter_upwards [hscale.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (reservoirSubpowerThreshold M0 2 (ε / 3))]
      with H hscaleH hthresholdH
  exact ⟨hscaleH, hthresholdH⟩

/-- Final `H ^ ε` modulus bound, with a completely explicit implied
constant.  The relation `T ≤ H` is used to obtain `H ≥ 1`, exactly as in
the manuscript's two-parameter range. -/
theorem manuscript_crossing_primeProduct_le_rpow
    {C Cres M0 H T a ε : ℝ} (hC : 1 ≤ C)
    (hscale : 1 ≤ C * Real.log H) (hCres : 1 < Cres)
    (hT : 1 ≤ T) (hTH : T ≤ H) (ha : 0 ≤ a)
    (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (hthreshold : reservoirSubpowerThreshold M0 2 (ε / 3) ≤ H)
    {s : Finset ℕ}
    (hinterval : ∀ p ∈ s,
      ⌊C * Real.log H⌋₊ < p ∧ p ≤ ⌊2 * (C * Real.log H)⌋₊)
    (hcard : s.card = manuscriptReservoirCrossing C Cres H T a hscale)
    (hdepth : manuscriptReservoirCrossing C Cres H T a hscale ≤
      reservoirDepth M0 H) :
    Cres * T ^ a ≤ (primeProduct s : ℝ) ∧
      (primeProduct s : ℝ) ≤
        (4 * C * (ε / 3)⁻¹) * Cres * T ^ a * H ^ ε := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hH : 1 ≤ H := hT.trans hTH
  have hraw := manuscript_crossing_primeProduct_real_bounds hscale hCres hT ha
    hM0 hδ (by simpa only [δ] using hthreshold) hinterval hcard hdepth
  have hlog := log_mul_rpow_le_inv_mul_rpow_two hH hδ
  have hpow : H ^ (2 * δ) ≤ H ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hH (by dsimp [δ]; linarith)
  have hcoefficient : 0 ≤ 4 * C * Cres * T ^ a := by positivity
  constructor
  · exact hraw.1
  · calc
      (primeProduct s : ℝ) ≤
          4 * C * Cres * T ^ a * Real.log H * H ^ δ := hraw.2
      _ = (4 * C * Cres * T ^ a) * (Real.log H * H ^ δ) := by ring
      _ ≤ (4 * C * Cres * T ^ a) * (δ⁻¹ * H ^ (2 * δ)) :=
        mul_le_mul_of_nonneg_left hlog hcoefficient
      _ ≤ (4 * C * Cres * T ^ a) * (δ⁻¹ * H ^ ε) := by
        gcongr
      _ = (4 * C * (ε / 3)⁻¹) * Cres * T ^ a * H ^ ε := by
        simp only [δ]
        ring

/-- Final `H ^ ε` bound for adjacent least common multiples. -/
theorem manuscript_crossing_oneExchange_lcm_le_rpow
    {C Cres M0 H T a ε : ℝ} (hC : 1 ≤ C)
    (hscale : 1 ≤ C * Real.log H) (hCres : 1 < Cres)
    (hT : 1 ≤ T) (hTH : T ≤ H) (ha : 0 ≤ a)
    (hM0 : 0 ≤ M0) (hε : 0 < ε)
    (hthreshold : reservoirSubpowerThreshold M0 2 (ε / 3) ≤ H)
    {s t : Finset ℕ}
    (hprimeInterval : ∀ p ∈ s ∪ t,
      p.Prime ∧ ⌊C * Real.log H⌋₊ < p ∧
        p ≤ ⌊2 * (C * Real.log H)⌋₊)
    (hcard : s.card = manuscriptReservoirCrossing C Cres H T a hscale)
    (hdepth : manuscriptReservoirCrossing C Cres H T a hscale ≤
      reservoirDepth M0 H)
    (hex : OneExchange s t) :
    Cres * T ^ a ≤
        (Nat.lcm (primeProduct s) (primeProduct t) : ℝ) ∧
      (Nat.lcm (primeProduct s) (primeProduct t) : ℝ) ≤
        (16 * C ^ 2 * ((ε / 3)⁻¹) ^ 2) *
          Cres * T ^ a * H ^ ε := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hH : 1 ≤ H := hT.trans hTH
  have hraw := manuscript_crossing_oneExchange_lcm_real_bounds
    hscale hCres hT ha hM0 hδ (by simpa only [δ] using hthreshold)
      hprimeInterval hcard hdepth hex
  have hlog := log_sq_mul_rpow_le_inv_sq_mul_rpow_three hH hδ
  have hthree : 3 * δ = ε := by dsimp [δ]; ring
  have hcoefficient : 0 ≤ 16 * C ^ 2 * Cres * T ^ a := by positivity
  constructor
  · exact hraw.1
  · calc
      (Nat.lcm (primeProduct s) (primeProduct t) : ℝ) ≤
          16 * C ^ 2 * Cres * T ^ a * (Real.log H) ^ 2 * H ^ δ := hraw.2
      _ = (16 * C ^ 2 * Cres * T ^ a) *
          ((Real.log H) ^ 2 * H ^ δ) := by ring
      _ ≤ (16 * C ^ 2 * Cres * T ^ a) *
          ((δ⁻¹) ^ 2 * H ^ (3 * δ)) :=
        mul_le_mul_of_nonneg_left hlog hcoefficient
      _ = (16 * C ^ 2 * ((ε / 3)⁻¹) ^ 2) *
          Cres * T ^ a * H ^ ε := by
        rw [hthree]
        simp only [δ]
        ring

end

end TranslatedDepthSeven
