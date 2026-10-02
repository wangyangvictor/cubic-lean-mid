import TranslatedDepthSeven.SurfaceBlockLogThreshold
import TranslatedDepthSeven.SmoothSurfaceResidueExponent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A quantitative, height-dependent choice of the surface block degree and
prime cutoff. All constants precede the box and packet parameters. -/

namespace TranslatedDepthSeven.SurfaceMixedDegreeChoice
noncomputable section
open Filter
open scoped Topology
open SurfaceBlockLogThreshold
set_option maxHeartbeats 2000000

theorem jet_exponent_div_count_lower (n : ℕ) (hn : 0 < n) :
    (2 * Real.sqrt 2 / 3) * Real.sqrt (n : ℝ) - 2 ≤
      (smoothSurfaceJetExponent n : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).2
  have h := smoothSurfaceJetExponent_lower_bound n
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hnR, Real.rpow_one, ← Real.sqrt_eq_rpow] at h
  nlinarith

theorem log_block_count_le (d k : ℕ) (hd : 0 < d) :
    Real.log ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ≤
      (Real.log (d : ℝ) + 2) * ((k : ℝ) + 1) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < (d * affinePlaneMonomialCount k : ℕ) := by
    exact_mod_cast block_count_pos d k hd
  have hnle : ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ≤
      (d : ℝ) * ((k : ℝ) + 2) ^ 2 := by
    rw [block_count_formula]
    nlinarith [show (0 : ℝ) ≤ (d : ℝ) * ((k : ℝ) + 2) * ((k : ℝ) + 3) by positivity]
  have hlog := Real.log_le_log hnR hnle
  rw [Real.log_mul hdR.ne' (by positivity), Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hklog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) + 2 by positivity)
  have hdlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  nlinarith [mul_nonneg hdlog (Nat.cast_nonneg k)]

theorem normalized_arch_bound_le (d k b D H B : ℕ)
    (hd : 0 < d) (hD : 1 ≤ D) :
    Real.log ((d * affinePlaneMonomialCount k : ℕ) : ℝ) +
      Real.log (D : ℝ) + (b : ℝ) * Real.log (H : ℝ) +
        (2 * (k : ℝ) / 3) * (3 * Real.log ((d : ℝ) + 1) + Real.log (B : ℝ)) ≤
      (Real.log (d : ℝ) + 2 + Real.log (D : ℝ) + 2 * Real.log ((d : ℝ) + 1)) *
        ((k : ℝ) + 1) + (b : ℝ) * Real.log (H : ℝ) +
          (2 * (k : ℝ) / 3) * Real.log (B : ℝ) := by
  have hn := log_block_count_le d k hd
  have hDlog : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast hD)
  have hdlog : 0 ≤ Real.log ((d : ℝ) + 1) := Real.log_nonneg (by
    linarith [show (0 : ℝ) ≤ (d : ℝ) by positivity])
  nlinarith [mul_nonneg hDlog (Nat.cast_nonneg k)]

/-- A single height threshold absorbs logarithmic losses and ensures that
the power-sized degree is at least the lower prime cutoff. -/
theorem exists_height_control (η c R T : ℝ) (hη : 0 < η) (hc : 0 < c) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      1 ≤ Real.log H ∧ Real.log H ≤ H ^ η ∧
        Real.log (Real.log H) + R ≤ η / 2 * Real.log H ∧
          T ≤ c * η / 2 * (H ^ η + 1) := by
  have hsmall : ∀ᶠ H : ℝ in atTop,
      ‖Real.log (Real.log H)‖ ≤ (η / 4) * ‖Real.log H‖ :=
    (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).bound
      (by positivity : 0 < η / 4)
  have hpower : ∀ᶠ H : ℝ in atTop, ‖Real.log H‖ ≤ ‖H ^ η‖ := by
    simpa only [one_mul] using (isLittleO_log_rpow_atTop hη).bound zero_lt_one
  have hall : ∀ᶠ H : ℝ in atTop, 1 ≤ H ∧
      1 ≤ Real.log H ∧ Real.log H ≤ H ^ η ∧
        Real.log (Real.log H) + R ≤ η / 2 * Real.log H ∧
          T ≤ c * η / 2 * (H ^ η + 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1, hsmall, hpower,
      Real.tendsto_log_atTop.eventually_ge_atTop (4 * R / η),
      (tendsto_rpow_atTop hη).eventually_ge_atTop (2 * T / (c * η))]
      with H hH hlog hsmall hpower hR hT
    have hlog0 : 0 ≤ Real.log H := by linarith
    have hH0 : 0 ≤ H := by linarith
    have hll0 : 0 ≤ Real.log (Real.log H) := Real.log_nonneg hlog
    simp only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg hll0, abs_of_nonneg (Real.rpow_nonneg hH0 η)] at hsmall hpower
    have hR' : 4 * R ≤ Real.log H * η := (div_le_iff₀ hη).1 hR
    have hT' : 2 * T ≤ H ^ η * (c * η) := (div_le_iff₀ (mul_pos hc hη)).1 hT
    refine ⟨hH, hlog, hpower, ?_, ?_⟩ <;> nlinarith [mul_pos hc hη]
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.1 hall
  refine ⟨max 1 H₁, le_max_left _ _, ?_⟩
  intro H hH
  exact (hH₁ H ((le_max_right _ _).trans hH)).2

/-- The literal ceiling choice has a uniform factor-two upper bound and
combines the packet and auxiliary-prime logarithms with the sharp factor
`1 / sqrt K`. No upper bound on `B` or `q` is used here. -/
theorem ceiling_degree_properties (H B q η a K : ℝ)
    (hH : 1 ≤ H) (hB : 0 < B) (hq : 1 ≤ q) (hη : 0 < η) (hK : 1 ≤ K) :
    let k := ⌈H ^ η * (1 + B ^ a / q)⌉₊
    0 < k ∧ (k : ℝ) ≤ 2 * H ^ η * (1 + B ^ a / q) ∧
      H ^ η ≤ (k : ℝ) ∧
        η * Real.log H + a * Real.log B ≤ Real.log (k : ℝ) + Real.sqrt K * Real.log q := by
  dsimp only
  let X := H ^ η * (1 + B ^ a / q)
  have hH0 : 0 < H := by linarith
  have hq0 : 0 < q := by linarith
  have hpow1 : 1 ≤ H ^ η := Real.one_le_rpow hH hη.le
  have hfrac : 0 < B ^ a / q := div_pos (Real.rpow_pos_of_pos hB a) hq0
  have hXp : H ^ η ≤ X := by dsimp [X]; nlinarith
  have hX1 : 1 ≤ X := hpow1.trans hXp
  have hXpos : 0 < X := by linarith
  have hkpos : 0 < ⌈X⌉₊ := Nat.one_le_ceil_iff.2 hXpos
  have hceil := Nat.le_ceil X
  have hceilup := Nat.ceil_lt_add_one hXpos.le
  have hXmul : H ^ η * B ^ a ≤ (⌈X⌉₊ : ℝ) * q := by
    have h := mul_le_mul_of_nonneg_right hceil hq0.le
    dsimp [X] at h
    have hcancel : H ^ η * (1 + B ^ a / q) * q = H ^ η * q + H ^ η * B ^ a := by
      field_simp
    rw [hcancel] at h
    nlinarith [mul_nonneg (Real.rpow_nonneg hH0.le η) hq0.le]
  have hlogs := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hH0 η)
    (Real.rpow_pos_of_pos hB a)) hXmul
  rw [Real.log_mul (Real.rpow_pos_of_pos hH0 η).ne' (Real.rpow_pos_of_pos hB a).ne',
    Real.log_rpow hH0, Real.log_rpow hB,
    Real.log_mul (by exact_mod_cast hkpos.ne') hq0.ne'] at hlogs
  have hsK : 1 ≤ Real.sqrt K := by
    have h := Real.sqrt_le_sqrt hK
    simpa using h
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  refine ⟨hkpos, ?_, hXp.trans hceil, ?_⟩
  · have hbound : (⌈X⌉₊ : ℝ) ≤ 2 * X := by linarith
    simpa only [X, mul_assoc] using hbound
  · nlinarith [mul_nonneg (sub_nonneg.2 hsK) hlogq]

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

private theorem scalar_of_controls (d k b D H B q : ℕ)
    (K A Aex C η a : ℝ) (hd : 0 < d) (hD : 1 ≤ D)
    (hB : 1 ≤ B) (hq : 1 ≤ q) (hK : 0 < K) (hη : 0 < η) (ha : 0 ≤ a)
    (hlogH : 0 ≤ Real.log (H : ℝ))
    (hcoef : (2 / 3 : ℝ) ≤ ((2 / 3 : ℝ) * Real.sqrt (d : ℝ) / Real.sqrt K) * a)
    (hklog : η * Real.log (H : ℝ) + a * Real.log (B : ℝ) ≤
      Real.log (k : ℝ) + Real.sqrt K * Real.log (q : ℝ))
    (hqheight : Real.log (q : ℝ) ≤ Aex * Real.log (H : ℝ))
    (hheight : Real.log (Real.log (H : ℝ)) + C + Aex + 3 * A / 2 +
      archConstant d D / ((2 / 3 : ℝ) * Real.sqrt (d : ℝ) / Real.sqrt K) + 1 ≤
        η / 2 * Real.log (H : ℝ))
    (hsize : (b : ℝ) + 2 * Aex ≤
      ((2 / 3 : ℝ) * Real.sqrt (d : ℝ) / Real.sqrt K) * η / 2 * ((k : ℝ) + 1)) :
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
  let Z : ℝ := a * Real.log (B : ℝ) + η / 2 * Real.log (H : ℝ) +
    archConstant d D / c + 1
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
  have hZW : Z ≤ W := by dsimp [Z, W, c]; linarith
  have hcg : c * ((k : ℝ) + 1) ≤ g := by
    have h := div_le_div_of_nonneg_right (sharp_gain_coefficient_ge d k) hsK.le
    convert h using 1 <;> dsimp [c, g, n] <;> ring
  have hgain : c * ((k : ℝ) + 1) * Z ≤ g * W :=
    (mul_le_mul_of_nonneg_right hcg hZ).trans (mul_le_mul_of_nonneg_left hZW hg0)
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
  have hHterm : ((b : ℝ) + 2 * Aex) * Real.log (H : ℝ) ≤
      c * ((k : ℝ) + 1) * (η / 2 * Real.log (H : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hsize hlogH
    change (b : ℝ) + 2 * Aex ≤ c * η / 2 * ((k : ℝ) + 1) at hsize
    convert h using 1
    dsimp [c]
    ring
  have hcdiv : c * ((k : ℝ) + 1) * (archConstant d D / c) =
      archConstant d D * ((k : ℝ) + 1) := by
    field_simp [hc.ne']
  have hexpand : c * ((k : ℝ) + 1) * Z =
      c * ((k : ℝ) + 1) * (a * Real.log (B : ℝ)) +
      c * ((k : ℝ) + 1) * (η / 2 * Real.log (H : ℝ)) +
      archConstant d D * ((k : ℝ) + 1) + c * ((k : ℝ) + 1) := by
    dsimp [Z]
    linear_combination hcdiv
  have harch := normalized_arch_bound_le d k b D H B hd hD
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hcpos : 0 < c * ((k : ℝ) + 1) := by positivity
  change _ < (smoothSurfaceJetExponent n : ℝ) / (n : ℝ) * Real.log (q : ℝ) + _
  dsimp [archConstant] at hexpand
  nlinarith only [hgain, hjet, hidentity, hBterm, hHterm, hexpand,
    harch, h4, hcpos, hqheight]

/-- Choose degree and prime cutoff together, uniformly before the box and
packet modulus. The chosen cutoff is exactly the degree. The local packet
exponent is the actual smooth-surface jet exponent, and every negative
mixed-prime term is retained. The conclusion needs no upper bound on `B`.
The factor in the quantitative degree bound is the absolute constant two. -/
theorem exists_degree_choice (d b D : ℕ) (hd : 0 < d) (hD : 1 ≤ D)
    (K A Aex C η a : ℝ) (hK : 1 ≤ K) (hη : 0 < η)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H B q : ℕ,
      H₀ ≤ (H : ℝ) → 1 ≤ B → 1 ≤ q → (q : ℝ) ≤ (H : ℝ) ^ Aex →
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * (H : ℝ) ^ η * (1 + (B : ℝ) ^ a / (q : ℝ)) ∧
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
  have hK0 : 0 < K := by linarith
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
  obtain ⟨H₀, hH₀, hcontrols⟩ := exists_height_control η c
    (C + Aex + 3 * A / 2 + archConstant d D / c + 1)
    ((b : ℝ) + 2 * Aex) hη hc
  refine ⟨H₀, hH₀, ?_⟩
  intro H B q hH hB hq hqheight
  have hH1 : (1 : ℝ) ≤ H := hH₀.trans hH
  have hHpos : (0 : ℝ) < H := by linarith
  obtain ⟨hlogH, hcutoff, hheight, hsize⟩ := hcontrols H hH
  let k := ⌈(H : ℝ) ^ η * (1 + (B : ℝ) ^ a / (q : ℝ))⌉₊
  obtain ⟨hkpos, hkupper, hkpower, hklog⟩ := ceiling_degree_properties
    (H : ℝ) (B : ℝ) (q : ℝ) η a K hH1 (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hB))
      (by exact_mod_cast hq) hη hK
  refine ⟨k, hkpos, hkupper, hlogH, Nat.ceil_le.2 (hcutoff.trans hkpower), ?_⟩
  have hqlog : Real.log (q : ℝ) ≤ Aex * Real.log (H : ℝ) := by
    have hh := Real.log_le_log (show (0 : ℝ) < q by exact_mod_cast (lt_of_lt_of_le zero_lt_one hq)) hqheight
    simpa only [Real.log_rpow hHpos] using hh
  apply scalar_of_controls d k b D H B q K A Aex C η a hd hD hB hq hK0 hη ha0.le
    (by linarith) hcoef hklog hqlog
  · dsimp [c] at hheight
    linarith
  · have hkplus : (H : ℝ) ^ η + 1 ≤ (k : ℝ) + 1 := by
      change (H : ℝ) ^ η ≤ (k : ℝ) at hkpower
      linarith
    exact hsize.trans (mul_le_mul_of_nonneg_left hkplus
      (show 0 ≤ c * η / 2 by positivity))

/-- The quantitative choice applied to the literal determinant-height
expression. This is a numerical theorem: a geometric auxiliary equation
still requires the previously proved packet and mixed divisibility data. -/
theorem exists_packet_mixed_log_threshold
    (d b D : ℕ) (hd : 0 < d) (hD : 1 ≤ D)
    (K A Aex C η a : ℝ) (hK : 1 ≤ K) (hη : 0 < η)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H B q : ℕ,
      H₀ ≤ (H : ℝ) → 1 ≤ B → 1 ≤ q → (q : ℝ) ≤ (H : ℝ) ^ Aex →
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * (H : ℝ) ^ η * (1 + (B : ℝ) ^ a / (q : ℝ)) ∧
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
              2 * (d * affinePlaneMonomialCount k : ℕ) * (Real.log 4 * (k : ℝ))) := by
  obtain ⟨H₀, hH₀, hchoice⟩ := exists_degree_choice d b D hd hD K A Aex C η a hK hη ha
  refine ⟨H₀, hH₀, ?_⟩
  intro H B q hH hB hq hqheight
  obtain ⟨k, hk, hkbound, hlogH, hcutoff, hscalar⟩ := hchoice H B q hH hB hq hqheight
  refine ⟨k, hk, hkbound, hlogH, hcutoff, ?_⟩
  have hH1 : 1 ≤ H := by exact_mod_cast hH₀.trans hH
  apply log_block_bound_lt_packet_mixed_gain d k b D H B
    (smoothSurfaceJetExponent (d * affinePlaneMonomialCount k)) q hd
    (lt_of_lt_of_le zero_lt_one hq) hD hH1 hB K A
    (Real.log (k : ℝ) - Real.log (Real.log (H : ℝ)) - C - Aex)
    (Real.log 4 * (k : ℝ))
  simpa only [mul_assoc] using hscalar

end
end TranslatedDepthSeven.SurfaceMixedDegreeChoice
