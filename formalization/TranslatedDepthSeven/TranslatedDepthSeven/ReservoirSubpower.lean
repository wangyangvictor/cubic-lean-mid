import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Subpower size of a logarithmic prime reservoir

For a fixed constant `M₀`, the prime reservoir used in the translated
determinant argument has

`ceil (M₀ * log H / log (log H))`

available primes.  This file proves directly, with an explicit threshold,
that every fixed exponential in this number is at most `H ^ ε`.  It also
records the particular polynomial--exponential expression which bounds the
number of vertices and one-prime-exchange edges of the reservoir graph.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The number of available primes at height `H`, with coefficient `M₀`. -/
def reservoirDepth (M₀ H : ℝ) : ℕ :=
  ⌈M₀ * Real.log H / Real.log (Real.log H)⌉₊

/-- A convenient explicit threshold for absorbing a fixed exponential in
`reservoirDepth M₀ H`.  No optimization is intended. -/
def reservoirSubpowerThreshold (M₀ b ε : ℝ) : ℝ :=
  Real.exp
    (Real.exp
      (max 1 (((M₀ + 1) * Real.log b) / ε)))

/-- Above the explicit threshold, every fixed base `b ≥ 1` raised to the
reservoir depth is bounded by `H ^ ε`. -/
theorem reservoirBase_pow_depth_le_rpow
    {M₀ b ε H : ℝ} (hM₀ : 0 ≤ M₀) (hb : 1 ≤ b) (hε : 0 < ε)
    (hH : reservoirSubpowerThreshold M₀ b ε ≤ H) :
    b ^ reservoirDepth M₀ H ≤ H ^ ε := by
  let u : ℝ := max 1 (((M₀ + 1) * Real.log b) / ε)
  let L : ℝ := Real.log H
  let ell : ℝ := Real.log L
  have hu_one : 1 ≤ u := le_max_left _ _
  have hu_pos : 0 < u := zero_lt_one.trans_le hu_one
  have hthreshold_pos : 0 < reservoirSubpowerThreshold M₀ b ε := by
    unfold reservoirSubpowerThreshold
    positivity
  have hHpos : 0 < H := hthreshold_pos.trans_le hH
  have hexpu_le_L : Real.exp u ≤ L := by
    apply (Real.le_log_iff_exp_le hHpos).2
    simpa [reservoirSubpowerThreshold, u, L] using hH
  have hLpos : 0 < L := (Real.exp_pos u).trans_le hexpu_le_L
  have hu_le_ell : u ≤ ell := by
    apply (Real.le_log_iff_exp_le hLpos).2
    simpa [ell] using hexpu_le_L
  have hell_one : 1 ≤ ell := hu_one.trans hu_le_ell
  have hell_pos : 0 < ell := zero_lt_one.trans_le hell_one
  have hlogb_nonneg : 0 ≤ Real.log b := Real.log_nonneg hb
  have hratio_nonneg :
      0 ≤ M₀ * L / ell := div_nonneg (mul_nonneg hM₀ hLpos.le) hell_pos.le
  have hdepth_cast :
      (reservoirDepth M₀ H : ℝ) ≤ M₀ * L / ell + 1 := by
    exact (Nat.ceil_lt_add_one hratio_nonneg).le
  have hell_le_L : ell ≤ L := by
    exact Real.log_le_self hLpos.le
  have hone_le_ratio : 1 ≤ L / ell := by
    exact (le_div_iff₀ hell_pos).2 (by simpa using hell_le_L)
  have hdepth_ratio :
      (reservoirDepth M₀ H : ℝ) ≤ (M₀ + 1) * L / ell := by
    calc
      (reservoirDepth M₀ H : ℝ) ≤ M₀ * L / ell + 1 := hdepth_cast
      _ ≤ M₀ * L / ell + L / ell := add_le_add (le_refl _) hone_le_ratio
      _ = (M₀ + 1) * L / ell := by ring
  have hcoefficient : (M₀ + 1) * Real.log b ≤ ε * ell := by
    have hquot : ((M₀ + 1) * Real.log b) / ε ≤ ell :=
      (le_max_right _ _).trans hu_le_ell
    simpa [mul_comm] using (div_le_iff₀ hε).mp hquot
  have hexponent :
      Real.log b * (reservoirDepth M₀ H : ℝ) ≤ ε * L := by
    calc
      Real.log b * (reservoirDepth M₀ H : ℝ)
          ≤ Real.log b * ((M₀ + 1) * L / ell) := by gcongr
      _ = ((M₀ + 1) * Real.log b) * L / ell := by ring
      _ ≤ (ε * ell) * L / ell := by gcongr
      _ = ε * L := by field_simp
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hb),
    Real.rpow_def_of_pos hHpos]
  exact Real.exp_le_exp.mpr (by simpa [L, mul_comm] using hexponent)

/-- The base-four estimate most often used to bound a finite family of
subsets of the prime pool. -/
theorem four_pow_reservoirDepth_le_rpow
    {M₀ ε H : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (hH : reservoirSubpowerThreshold M₀ 4 ε ≤ H) :
    (4 : ℝ) ^ reservoirDepth M₀ H ≤ H ^ ε := by
  exact reservoirBase_pow_depth_le_rpow hM₀ (by norm_num) hε hH

/-- Filter form of `four_pow_reservoirDepth_le_rpow`. -/
theorem eventually_four_pow_reservoirDepth_le_rpow
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in Filter.atTop,
      (4 : ℝ) ^ reservoirDepth M₀ H ≤ H ^ ε := by
  filter_upwards [Filter.eventually_ge_atTop
    (reservoirSubpowerThreshold M₀ 4 ε)] with H hH
  exact four_pow_reservoirDepth_le_rpow hM₀ hε hH

/-- An elementary bound used to absorb the polynomial factor in the number
of one-prime-exchange edges. -/
theorem nat_le_two_pow (m : ℕ) : m ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega

/-- The standard vertex-plus-edge majorant is bounded by twice a fixed
exponential. -/
theorem vertexEdgeMajorant_le (m : ℕ) :
    2 ^ m + m ^ 2 * 2 ^ m ≤ 2 * 8 ^ m := by
  have hm : m ≤ 2 ^ m := nat_le_two_pow m
  have hmsq : m ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hm 2
  have hpoly : m ^ 2 * 2 ^ m ≤ 8 ^ m := by
    calc
      m ^ 2 * 2 ^ m ≤ (2 ^ m) ^ 2 * 2 ^ m := Nat.mul_le_mul_right _ hmsq
      _ = 8 ^ m := by
        calc
          (2 ^ m) ^ 2 * 2 ^ m = 2 ^ (m * 2) * 2 ^ m := by rw [pow_mul]
          _ = 2 ^ (m * 2 + m) := by rw [pow_add]
          _ = 2 ^ (3 * m) := by congr 1; omega
          _ = (2 ^ 3) ^ m := by rw [pow_mul]
          _ = 8 ^ m := by norm_num
  have htwo : 2 ^ m ≤ 8 ^ m := Nat.pow_le_pow_left (by norm_num) m
  omega

/-- Consequently the usual upper bound for the total number of reservoir
vertices and one-prime-exchange edges is `O(H ^ ε)`, with the explicit
constant `2`. -/
theorem vertexEdgeMajorant_cast_le_two_mul_rpow
    {M₀ ε H : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (hH : reservoirSubpowerThreshold M₀ 8 ε ≤ H) :
    ((2 ^ reservoirDepth M₀ H
        + (reservoirDepth M₀ H) ^ 2 * 2 ^ reservoirDepth M₀ H : ℕ) : ℝ)
      ≤ 2 * H ^ ε := by
  let m := reservoirDepth M₀ H
  have hcomb : 2 ^ m + m ^ 2 * 2 ^ m ≤ 2 * 8 ^ m := vertexEdgeMajorant_le m
  have hcast :
      ((2 ^ m + m ^ 2 * 2 ^ m : ℕ) : ℝ) ≤ 2 * (8 : ℝ) ^ m := by
    exact_mod_cast hcomb
  have hsub : (8 : ℝ) ^ m ≤ H ^ ε :=
    reservoirBase_pow_depth_le_rpow hM₀ (by norm_num) hε hH
  exact hcast.trans (mul_le_mul_of_nonneg_left hsub (by norm_num))

/-- Filter form of `vertexEdgeMajorant_cast_le_two_mul_rpow`. -/
theorem eventually_vertexEdgeMajorant_cast_le_two_mul_rpow
    {M₀ ε : ℝ} (hM₀ : 0 ≤ M₀) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in Filter.atTop,
      ((2 ^ reservoirDepth M₀ H
          + (reservoirDepth M₀ H) ^ 2 * 2 ^ reservoirDepth M₀ H : ℕ) : ℝ)
        ≤ 2 * H ^ ε := by
  filter_upwards [Filter.eventually_ge_atTop
    (reservoirSubpowerThreshold M₀ 8 ε)] with H hH
  exact vertexEdgeMajorant_cast_le_two_mul_rpow hM₀ hε hH

end

end TranslatedDepthSeven
