import TranslatedDepthSeven.SurfaceMixedDegreeChoice

/-!
# A logarithmic surface block-degree choice

This file restores the degree scale used in the original Salberger argument.
The block degree is a fixed constant times

`log H * (1 + B ^ a / q)`,

rather than the convenient power `H ^ η` used in
`SurfaceMixedDegreeChoice`.  All constants are chosen before `H`, `B`, and
`q`.  The conclusion is the same literal packet-plus-mixed determinant
threshold used to construct the auxiliary hypersurface.
-/

namespace TranslatedDepthSeven.SurfaceMixedLogDegreeChoice
noncomputable section
open Filter
open scoped Topology
open SurfaceBlockLogThreshold
open SurfaceMixedDegreeChoice
set_option maxHeartbeats 2000000

private def archConstant (d D : ℕ) : ℝ :=
  Real.log (d : ℝ) + 2 + Real.log (D : ℝ) +
    2 * Real.log ((d : ℝ) + 1) + 2 * Real.log 4

private theorem archConstant_nonneg (d D : ℕ) (hd : 0 < d) (hD : 1 ≤ D) :
    0 ≤ archConstant d D := by
  have hdlog := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd)
  have hDlog := Real.log_nonneg (show (1 : ℝ) ≤ D by exact_mod_cast hD)
  have hd1log := Real.log_nonneg (show (1 : ℝ) ≤ (d : ℝ) + 1 by
    linarith [show (0 : ℝ) ≤ (d : ℝ) by positivity])
  have h4log := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  unfold archConstant
  positivity

/-- A fixed scale can simultaneously pay for the constant part of the
mixed-prime loss and for the coefficient-height power of `H`. -/
theorem exists_log_degree_scale (c R T : ℝ) (hc : 0 < c) :
    ∃ L : ℝ, 1 ≤ L ∧ R ≤ Real.log L ∧ T ≤ c * L := by
  let L : ℝ := max 1 (max (Real.exp R) (T / c))
  have hL1 : 1 ≤ L := le_max_left _ _
  have hExp : Real.exp R ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hDiv : T / c ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hlog := Real.log_le_log (Real.exp_pos R) hExp
  have hT : T ≤ c * L := by
    have := mul_le_mul_of_nonneg_left hDiv hc.le
    field_simp [hc.ne'] at this
    exact this
  refine ⟨L, hL1, ?_, hT⟩
  simpa only [Real.log_exp] using hlog

/-- Above a fixed height, `log H` is at least one. -/
theorem exists_log_height_control :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → 1 ≤ Real.log H := by
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.1
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max 1 H₁, le_max_left _ _, ?_⟩
  intro H hH
  exact hH₁ H ((le_max_right _ _).trans hH)

/-- The logarithmic ceiling choice.  Besides its factor-two upper bound, it
gives exactly the logarithmic gain needed to trade the packet modulus against
the box size. -/
theorem log_ceiling_degree_properties (H B q L a K : ℝ)
    (hlogH : 1 ≤ Real.log H) (hB : 0 < B) (hq : 1 ≤ q)
    (hL : 1 ≤ L) (hK : 1 ≤ K) :
    let k := ⌈L * Real.log H * (1 + B ^ a / q)⌉₊
    0 < k ∧
      (k : ℝ) ≤ 2 * L * Real.log H * (1 + B ^ a / q) ∧
      L * Real.log H ≤ (k : ℝ) ∧
      Real.log L + Real.log (Real.log H) + a * Real.log B ≤
        Real.log (k : ℝ) + Real.sqrt K * Real.log q := by
  dsimp only
  let X := L * Real.log H * (1 + B ^ a / q)
  have hlogHpos : 0 < Real.log H := zero_lt_one.trans_le hlogH
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hfrac : 0 < B ^ a / q := div_pos (Real.rpow_pos_of_pos hB a) hqpos
  have hbase : 1 ≤ L * Real.log H := by nlinarith
  have hXbase : L * Real.log H ≤ X := by
    dsimp [X]
    nlinarith
  have hX1 : 1 ≤ X := hbase.trans hXbase
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hkpos : 0 < ⌈X⌉₊ := Nat.one_le_ceil_iff.2 hXpos
  have hceil := Nat.le_ceil X
  have hceilup := Nat.ceil_lt_add_one hXpos.le
  have hproduct : L * Real.log H * B ^ a ≤ (⌈X⌉₊ : ℝ) * q := by
    have h := mul_le_mul_of_nonneg_right hceil hqpos.le
    dsimp [X] at h
    have hcancel : L * Real.log H * (1 + B ^ a / q) * q =
        L * Real.log H * q + L * Real.log H * B ^ a := by
      field_simp
    rw [hcancel] at h
    nlinarith [mul_nonneg (mul_nonneg hLpos.le hlogHpos.le) hqpos.le]
  have hlogs := Real.log_le_log
    (mul_pos (mul_pos hLpos hlogHpos) (Real.rpow_pos_of_pos hB a)) hproduct
  rw [Real.log_mul (mul_pos hLpos hlogHpos).ne' (Real.rpow_pos_of_pos hB a).ne',
    Real.log_mul hLpos.ne' hlogHpos.ne', Real.log_rpow hB,
    Real.log_mul (by exact_mod_cast hkpos.ne') hqpos.ne'] at hlogs
  have hsK : 1 ≤ Real.sqrt K := by
    have h := Real.sqrt_le_sqrt hK
    simpa using h
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  refine ⟨hkpos, ?_, hXbase.trans hceil, ?_⟩
  · have hbound : (⌈X⌉₊ : ℝ) ≤ 2 * X := by linarith
    simpa only [X, mul_assoc] using hbound
  · nlinarith [mul_nonneg (sub_nonneg.2 hsK) hlogq]

private theorem scalar_of_log_controls (d k b D H B q : ℕ)
    (K A Aex C a L : ℝ) (hd : 0 < d) (hD : 1 ≤ D)
    (hB : 1 ≤ B) (hq : 1 ≤ q) (hK : 0 < K) (ha : 0 ≤ a)
    (hcoef : (2 / 3 : ℝ) ≤
      ((2 / 3 : ℝ) * Real.sqrt (d : ℝ) / Real.sqrt K) * a)
    (hklog : Real.log L + Real.log (Real.log (H : ℝ)) +
      a * Real.log (B : ℝ) ≤
        Real.log (k : ℝ) + Real.sqrt K * Real.log (q : ℝ))
    (hqheight : Real.log (q : ℝ) ≤ Aex * Real.log (H : ℝ))
    (hreserve : archConstant d D /
      ((2 / 3 : ℝ) * Real.sqrt (d : ℝ) / Real.sqrt K) + 2 ≤
        Real.log L - C - Aex - 3 * A / 2)
    (hsize : ((b : ℝ) + 2 * Aex) * Real.log (H : ℝ) ≤
      ((2 / 3 : ℝ) * Real.sqrt (d : ℝ) / Real.sqrt K) * ((k : ℝ) + 1)) :
    Real.log ((d * affinePlaneMonomialCount k : ℕ) : ℝ) +
      Real.log (D : ℝ) + (b : ℝ) * Real.log (H : ℝ) +
        (2 * (k : ℝ) / 3) * (3 * Real.log ((d : ℝ) + 1) + Real.log (B : ℝ)) <
      ((smoothSurfaceJetExponent (d * affinePlaneMonomialCount k) : ℝ) /
        ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) * Real.log (q : ℝ) +
      ((2 * Real.sqrt 2 / 3) / Real.sqrt K *
        Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
          (Real.log (k : ℝ) - Real.log (Real.log (H : ℝ)) - C - Aex) -
        (Real.sqrt 2 * A / Real.sqrt K) *
          Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) -
            2 * Real.log 4 * (k : ℝ)) := by
  let n := d * affinePlaneMonomialCount k
  let c : ℝ := (2 / 3 : ℝ) * Real.sqrt (d : ℝ) / Real.sqrt K
  let g : ℝ := (2 * Real.sqrt 2 / 3) / Real.sqrt K * Real.sqrt (n : ℝ)
  let Z : ℝ := a * Real.log (B : ℝ) + archConstant d D / c + 2
  let W : ℝ := Real.sqrt K * Real.log (q : ℝ) + Real.log (k : ℝ) -
    Real.log (Real.log (H : ℝ)) - C - Aex - 3 * A / 2
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hc : 0 < c := by dsimp [c]; positivity
  have hg0 : 0 ≤ g := by dsimp [g]; positivity
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hZ : 0 ≤ Z := by
    have hconst := archConstant_nonneg d D hd hD
    dsimp [Z]
    positivity
  have hZW : Z ≤ W := by dsimp [Z, W, c] at *; linarith
  have hcg : c * ((k : ℝ) + 1) ≤ g := by
    have h := div_le_div_of_nonneg_right (sharp_gain_coefficient_ge d k) hsK.le
    convert h using 1 <;> dsimp [c, g, n] <;> ring
  have hgain : c * ((k : ℝ) + 1) * Z ≤ g * W :=
    (mul_le_mul_of_nonneg_right hcg hZ).trans
      (mul_le_mul_of_nonneg_left hZW hg0)
  have hjet := mul_le_mul_of_nonneg_right
    (jet_exponent_div_count_lower n (block_count_pos d k hd)) hlogq
  have hidentity :
      ((2 * Real.sqrt 2 / 3) * Real.sqrt (n : ℝ) - 2) * Real.log (q : ℝ) +
        ((2 * Real.sqrt 2 / 3) / Real.sqrt K * Real.sqrt (n : ℝ) *
          (Real.log (k : ℝ) - Real.log (Real.log (H : ℝ)) - C - Aex) -
          (Real.sqrt 2 * A / Real.sqrt K) * Real.sqrt (n : ℝ) -
            2 * Real.log 4 * (k : ℝ)) =
      g * W - 2 * Real.log (q : ℝ) - 2 * Real.log 4 * (k : ℝ) := by
    dsimp [g, W]
    field_simp [hsK.ne']
    ring
  have hBterm : (2 * (k : ℝ) / 3) * Real.log (B : ℝ) ≤
      c * ((k : ℝ) + 1) * (a * Real.log (B : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ ((k : ℝ) + 1) * Real.log (B : ℝ) by positivity)
    change (2 / 3 : ℝ) ≤ c * a at hcoef
    change (2 / 3 : ℝ) * (((k : ℝ) + 1) * Real.log (B : ℝ)) ≤
      (c * a) * (((k : ℝ) + 1) * Real.log (B : ℝ)) at h
    nlinarith
  have hcdiv : c * ((k : ℝ) + 1) * (archConstant d D / c) =
      archConstant d D * ((k : ℝ) + 1) := by
    field_simp [hc.ne']
  have hexpand : c * ((k : ℝ) + 1) * Z =
      c * ((k : ℝ) + 1) * (a * Real.log (B : ℝ)) +
      archConstant d D * ((k : ℝ) + 1) + 2 * (c * ((k : ℝ) + 1)) := by
    dsimp [Z]
    linear_combination hcdiv
  have harch := normalized_arch_bound_le d k b D H B hd hD
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hcpos : 0 < c * ((k : ℝ) + 1) := by positivity
  change _ < (smoothSurfaceJetExponent n : ℝ) / (n : ℝ) * Real.log (q : ℝ) + _
  dsimp [archConstant] at hexpand
  nlinarith only [hgain, hjet, hidentity, hBterm, hsize, hexpand,
    harch, h4, hcpos, hqheight]

/-- Choose the block degree on Salberger's logarithmic scale.  The fixed
constant `L` and the height threshold precede all box and packet parameters. -/
theorem exists_log_degree_choice (d b D : ℕ) (hd : 0 < d) (hD : 1 ≤ D)
    (K A Aex C a : ℝ) (hK : 1 ≤ K)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ L H₀ : ℝ, 1 ≤ L ∧ 1 ≤ H₀ ∧ ∀ H B q : ℕ,
      H₀ ≤ (H : ℝ) → 1 ≤ B → 1 ≤ q → (q : ℝ) ≤ (H : ℝ) ^ Aex →
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
          (1 + (B : ℝ) ^ a / (q : ℝ)) ∧
        1 ≤ Real.log (H : ℝ) ∧ ⌈Real.log (H : ℝ)⌉₊ ≤ k ∧
        Real.log ((d * affinePlaneMonomialCount k : ℕ) : ℝ) +
          Real.log (D : ℝ) + (b : ℝ) * Real.log (H : ℝ) +
            (2 * (k : ℝ) / 3) * (3 * Real.log ((d : ℝ) + 1) + Real.log (B : ℝ)) <
          ((smoothSurfaceJetExponent (d * affinePlaneMonomialCount k) : ℝ) /
            ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) * Real.log (q : ℝ) +
          ((2 * Real.sqrt 2 / 3) / Real.sqrt K *
            Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
              (Real.log (k : ℝ) - Real.log (Real.log (H : ℝ)) - C - Aex) -
            (Real.sqrt 2 * A / Real.sqrt K) *
              Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) -
                2 * Real.log 4 * (k : ℝ)) := by
  let c : ℝ := (2 / 3 : ℝ) * Real.sqrt (d : ℝ) / Real.sqrt K
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK0
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hc : 0 < c := by dsimp [c]; positivity
  have ha0 : 0 < a := (div_pos hsK hsd).trans ha
  have ha' : Real.sqrt K < a * Real.sqrt (d : ℝ) := (div_lt_iff₀ hsd).1 ha
  have hcoef : (2 / 3 : ℝ) ≤ c * a := by
    have hh := mul_le_mul_of_nonneg_left ha'.le (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have hh' := div_le_div_of_nonneg_right hh hsK.le
    calc
      (2 / 3 : ℝ) = ((2 / 3 : ℝ) * Real.sqrt K) / Real.sqrt K := by field_simp
      _ ≤ ((2 / 3 : ℝ) * (a * Real.sqrt (d : ℝ))) / Real.sqrt K := hh'
      _ = c * a := by dsimp [c]; ring
  obtain ⟨L, hL, hLreserve, hLsize⟩ := exists_log_degree_scale c
    (C + Aex + 3 * A / 2 + archConstant d D / c + 2)
    ((b : ℝ) + 2 * Aex) hc
  obtain ⟨H₀, hH₀, hheight⟩ := exists_log_height_control
  refine ⟨L, H₀, hL, hH₀, ?_⟩
  intro H B q hH hB hq hqheight
  have hlogH : 1 ≤ Real.log (H : ℝ) := hheight H hH
  have hHpos : (0 : ℝ) < H :=
    zero_lt_one.trans ((Real.log_pos_iff (by positivity)).mp
      (zero_lt_one.trans_le hlogH))
  let k := ⌈L * Real.log (H : ℝ) *
    (1 + (B : ℝ) ^ a / (q : ℝ))⌉₊
  obtain ⟨hkpos, hkupper, hkbase, hklog⟩ := log_ceiling_degree_properties
    (H : ℝ) (B : ℝ) (q : ℝ) L a K hlogH
      (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hB))
      (by exact_mod_cast hq) hL hK
  refine ⟨k, hkpos, hkupper, hlogH, ?_, ?_⟩
  · apply Nat.ceil_le.2
    have := mul_le_mul_of_nonneg_right hL (show 0 ≤ Real.log (H : ℝ) by linarith)
    simpa only [one_mul] using this.trans hkbase
  · have hqlog : Real.log (q : ℝ) ≤ Aex * Real.log (H : ℝ) := by
      have hh := Real.log_le_log
        (show (0 : ℝ) < q by exact_mod_cast (lt_of_lt_of_le zero_lt_one hq)) hqheight
      simpa only [Real.log_rpow hHpos] using hh
    have hreserve : archConstant d D / c + 2 ≤
        Real.log L - C - Aex - 3 * A / 2 := by
      linarith
    have hsize : ((b : ℝ) + 2 * Aex) * Real.log (H : ℝ) ≤
        c * ((k : ℝ) + 1) := by
      have hmul := mul_le_mul_of_nonneg_right hLsize
        (show 0 ≤ Real.log (H : ℝ) by linarith)
      have hcbase := mul_le_mul_of_nonneg_left hkbase hc.le
      nlinarith
    exact scalar_of_log_controls d k b D H B q K A Aex C a L hd hD hB hq
      hK0 ha0.le hcoef hklog hqlog hreserve hsize

/-- The logarithmic choice applied to the literal determinant-height
expression.  This is the numerical input needed by the existing auxiliary
hypersurface construction. -/
theorem exists_packet_mixed_logarithmic_threshold
    (d b D : ℕ) (hd : 0 < d) (hD : 1 ≤ D)
    (K A Aex C a : ℝ) (hK : 1 ≤ K)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ L H₀ : ℝ, 1 ≤ L ∧ 1 ≤ H₀ ∧ ∀ H B q : ℕ,
      H₀ ≤ (H : ℝ) → 1 ≤ B → 1 ≤ q → (q : ℝ) ≤ (H : ℝ) ^ Aex →
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
          (1 + (B : ℝ) ^ a / (q : ℝ)) ∧
        1 ≤ Real.log (H : ℝ) ∧ ⌈Real.log (H : ℝ)⌉₊ ≤ k ∧
        Real.log (((d * affinePlaneMonomialCount k).factorial *
          (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
            (((d + 1) ^ 3) * B) ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) <
          (smoothSurfaceJetExponent (d * affinePlaneMonomialCount k) : ℝ) * Real.log (q : ℝ) +
            ((2 * Real.sqrt 2 / 3) / Real.sqrt K *
              ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
                (Real.log (k : ℝ) - Real.log (Real.log (H : ℝ)) - C - Aex) -
              (Real.sqrt 2 * A / Real.sqrt K) *
                (((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
                  Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) -
              2 * (d * affinePlaneMonomialCount k : ℕ) *
                (Real.log 4 * (k : ℝ))) := by
  obtain ⟨L, H₀, hL, hH₀, hchoice⟩ :=
    exists_log_degree_choice d b D hd hD K A Aex C a hK ha
  refine ⟨L, H₀, hL, hH₀, ?_⟩
  intro H B q hH hB hq hqheight
  obtain ⟨k, hk, hkbound, hlogH, hcutoff, hscalar⟩ :=
    hchoice H B q hH hB hq hqheight
  refine ⟨k, hk, hkbound, hlogH, hcutoff, ?_⟩
  have hH1 : 1 ≤ H := by
    have hH1R : (1 : ℝ) ≤ (H : ℝ) :=
      ((Real.log_pos_iff (by positivity)).mp (zero_lt_one.trans_le hlogH)).le
    exact_mod_cast hH1R
  apply log_block_bound_lt_packet_mixed_gain d k b D H B
    (smoothSurfaceJetExponent (d * affinePlaneMonomialCount k)) q hd
    (lt_of_lt_of_le zero_lt_one hq) hD hH1 hB K A
    (Real.log (k : ℝ) - Real.log (Real.log (H : ℝ)) - C - Aex)
    (Real.log 4 * (k : ℝ))
  simpa only [mul_assoc] using hscalar

end
end TranslatedDepthSeven.SurfaceMixedLogDegreeChoice
