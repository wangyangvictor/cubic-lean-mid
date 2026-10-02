import TranslatedDepthSeven.ComparablePrimePool

/-!
# The minimal crossing cardinality for comparable primes

All primes in the PNT reservoir lie in one interval `(x,2x]`.  Consequently
the crossing cardinality can be defined using only the common lower endpoint.
This file proves the exact finite inequalities which later turn the crossing
moduli and adjacent least common multiples into `Q * H^epsilon` bounds.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- If `2 <= L`, some power of `L` exceeds every natural target. -/
theorem exists_power_ge_of_two_le {L : ℕ} (hL : 2 ≤ L) (Q : ℕ) :
    ∃ k, Q ≤ L ^ k := by
  refine ⟨Q, self_le_two_pow Q |>.trans ?_⟩
  exact pow_le_pow_left' hL Q

/-- The least `k` for which the common lower endpoint `L` has `L^k >= Q`. -/
def comparableCrossing (L Q : ℕ) (hL : 2 ≤ L) : ℕ :=
  Nat.find (exists_power_ge_of_two_le hL Q)

theorem comparableCrossing_spec (L Q : ℕ) (hL : 2 ≤ L) :
    Q ≤ L ^ comparableCrossing L Q hL :=
  Nat.find_spec (exists_power_ge_of_two_le hL Q)

theorem comparableCrossing_minimal {L Q j : ℕ} {hL : 2 ≤ L}
    (hj : j < comparableCrossing L Q hL) : L ^ j < Q := by
  have hnot := Nat.find_min (exists_power_ge_of_two_le hL Q) hj
  omega

theorem comparableCrossing_le {L Q K : ℕ} {hL : 2 ≤ L}
    (hQK : Q ≤ L ^ K) : comparableCrossing L Q hL ≤ K :=
  Nat.find_min' (exists_power_ge_of_two_le hL Q) hQK

theorem comparableCrossing_pos {L Q : ℕ} {hL : 2 ≤ L}
    (hQ : 1 < Q) : 0 < comparableCrossing L Q hL := by
  by_contra hk
  have hs := comparableCrossing_spec L Q hL
  have hk0 : comparableCrossing L Q hL = 0 := Nat.eq_zero_of_not_pos hk
  rw [hk0, pow_zero] at hs
  omega

/-- Minimality bounds the lower-endpoint power by one final factor of `L`. -/
theorem comparableCrossing_power_lt_overshoot {L Q : ℕ} {hL : 2 ≤ L}
    (hQ : 1 < Q) :
    L ^ comparableCrossing L Q hL < Q * L := by
  let k := comparableCrossing L Q hL
  have hk : 0 < k := comparableCrossing_pos hQ
  have hprev : L ^ (k - 1) < Q := by
    apply comparableCrossing_minimal
    omega
  calc
    L ^ k = L ^ (k - 1) * L := by
      nth_rw 1 [← Nat.sub_add_cancel hk]
      rw [pow_succ]
    _ < Q * L := Nat.mul_lt_mul_of_pos_right hprev (by omega)

/-- The upper endpoint of `(floor x, floor (2x)]` is at most twice the
integer lower endpoint `floor x + 1`. -/
theorem floor_two_mul_le_two_mul_floor_add_one {x : ℝ} (hx : 0 ≤ x) :
    ⌊2 * x⌋₊ ≤ 2 * (⌊x⌋₊ + 1) := by
  have hxlt : x < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have htwo : 2 * x < ((2 * (⌊x⌋₊ + 1) : ℕ) : ℝ) := by
    exact_mod_cast (mul_lt_mul_of_pos_left hxlt (by norm_num : (0 : ℝ) < 2))
  have hfloorlt : ⌊2 * x⌋₊ < 2 * (⌊x⌋₊ + 1) := by
    exact (Nat.floor_lt (mul_nonneg (by norm_num) hx)).2 htwo
  exact hfloorlt.le

/-- For `x >= 1`, the integer lower endpoint is at least two. -/
theorem two_le_floor_add_one {x : ℝ} (hx : 1 ≤ x) : 2 ≤ ⌊x⌋₊ + 1 := by
  have hfloor : 1 ≤ ⌊x⌋₊ := by
    simpa using Nat.floor_mono hx
  omega

/-- Every fixed-cardinality modulus crosses `Q`; all such moduli have the
same explicit upper bound. -/
theorem comparable_crossing_primeProduct_bounds
    {x : ℝ} (hx : 1 ≤ x) {M Q : ℕ}
    {hM : M ≤ (comparablePrimeCandidates x).card}
    (hQ : 1 < Q) {s : Finset ℕ}
    (hs : s ⊆ comparablePrimePool x M hM)
    (hcard : s.card = comparableCrossing (⌊x⌋₊ + 1) Q
      (two_le_floor_add_one hx)) :
    Q ≤ primeProduct s ∧
      primeProduct s <
        Q * (⌊x⌋₊ + 1) *
          2 ^ comparableCrossing (⌊x⌋₊ + 1) Q
            (two_le_floor_add_one hx) := by
  let L := ⌊x⌋₊ + 1
  let k := comparableCrossing L Q (two_le_floor_add_one hx)
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hU : ⌊2 * x⌋₊ ≤ 2 * L :=
    floor_two_mul_le_two_mul_floor_add_one hx0
  have hb := comparable_fixedCard_primeProduct_bounds hs hcard
  constructor
  · exact (comparableCrossing_spec L Q (two_le_floor_add_one hx)).trans hb.1
  · calc
      primeProduct s ≤ ⌊2 * x⌋₊ ^ k := hb.2
      _ ≤ (2 * L) ^ k := pow_le_pow_left' hU k
      _ = 2 ^ k * L ^ k := by rw [mul_pow]
      _ < 2 ^ k * (Q * L) := Nat.mul_lt_mul_of_pos_left
        (comparableCrossing_power_lt_overshoot hQ) (pow_pos (by omega) _)
      _ = Q * L * 2 ^ k := by ring

/-- An adjacent least common multiple crosses `Q` and costs only one further
comparable prime beyond the modulus bound. -/
theorem comparable_crossing_oneExchange_lcm_bounds
    {x : ℝ} (hx : 1 ≤ x) {M Q : ℕ}
    {hM : M ≤ (comparablePrimeCandidates x).card}
    (hQ : 1 < Q) {s t : Finset ℕ}
    (hs : s ⊆ comparablePrimePool x M hM)
    (ht : t ⊆ comparablePrimePool x M hM)
    (hcard : s.card = comparableCrossing (⌊x⌋₊ + 1) Q
      (two_le_floor_add_one hx))
    (hex : OneExchange s t) :
    Q ≤ Nat.lcm (primeProduct s) (primeProduct t) ∧
      Nat.lcm (primeProduct s) (primeProduct t) <
        Q * (⌊x⌋₊ + 1) ^ 2 *
          2 ^ (comparableCrossing (⌊x⌋₊ + 1) Q
            (two_le_floor_add_one hx) + 1) := by
  let L := ⌊x⌋₊ + 1
  let k := comparableCrossing L Q (two_le_floor_add_one hx)
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hU : ⌊2 * x⌋₊ ≤ 2 * L :=
    floor_two_mul_le_two_mul_floor_add_one hx0
  have hb := comparable_oneExchange_lcm_bounds hs ht hcard hex
  constructor
  · exact (comparableCrossing_spec L Q (two_le_floor_add_one hx)).trans hb.1
  · calc
      Nat.lcm (primeProduct s) (primeProduct t) ≤
          ⌊2 * x⌋₊ ^ (k + 1) := hb.2
      _ ≤ (2 * L) ^ (k + 1) := pow_le_pow_left' hU (k + 1)
      _ = 2 ^ (k + 1) * (L ^ k * L) := by
        simp only [mul_pow, pow_succ]
        ring
      _ < 2 ^ (k + 1) * ((Q * L) * L) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_right
            (comparableCrossing_power_lt_overshoot hQ) (by omega))
          (pow_pos (by omega) _)
      _ = Q * L ^ 2 * 2 ^ (k + 1) := by ring

end

end TranslatedDepthSeven
