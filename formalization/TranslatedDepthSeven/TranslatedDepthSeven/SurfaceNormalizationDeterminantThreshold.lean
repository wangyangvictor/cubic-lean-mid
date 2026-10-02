import TranslatedDepthSeven.AffinePlaneMonomialWeights
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Quantitative determinant threshold for a complete surface block

The block size and height threshold are chosen before the box size and
modulus. The local exponent is the literal exponent
`affinePlaneMonomialWeight t + (t + 1) * s` already used for arbitrary
surface-polynomial evaluation determinants.
-/

namespace TranslatedDepthSeven
noncomputable section
open Filter

set_option maxHeartbeats 1000000

/-- Decompose a positive row count into complete bivariate degree layers
and a final partial layer. -/
theorem exists_affinePlaneMonomialCount_remainder (n : ℕ) (hn : 0 < n) :
    ∃ t s : ℕ, n = affinePlaneMonomialCount t + s ∧ s < t + 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hzero : n = 0
    · subst n
      exact ⟨0, 0, by simp [affinePlaneMonomialCount], by omega⟩
    obtain ⟨t, s, heq, hs⟩ := ih (by omega)
    by_cases hnext : s + 1 < t + 2
    · exact ⟨t, s + 1, by omega, hnext⟩
    · refine ⟨t + 1, 0, ?_, by omega⟩
      have hcount : affinePlaneMonomialCount (t + 1) =
          affinePlaneMonomialCount t + (t + 2) := by
        simp [affinePlaneMonomialCount, Finset.sum_range_succ]
      rw [hcount]
      omega

/-- The sharp exponent supplied by a complete degree layer and a partial
layer dominates two thirds of the row count times the completed degree. -/
theorem affinePlane_partialWeight_lower_bound (t s : ℕ) :
    2 * t * (affinePlaneMonomialCount t + s) ≤
      3 * (affinePlaneMonomialWeight t + (t + 1) * s) := by
  have hc := two_mul_affinePlaneMonomialCount t
  have hw := three_mul_affinePlaneMonomialWeight t
  nlinarith

/-- Choose one normalization block whose local determinant exponent beats
the archimedean exponent by the requested positive margin. -/
theorem exists_surfaceBlock_exponent_gap
    (d b : ℕ) (hd : 0 < d) (η : ℝ) (hη : 0 < η) :
    ∃ k t s : ℕ,
      d * affinePlaneMonomialCount k = affinePlaneMonomialCount t + s ∧
      s < t + 2 ∧
      ((b * (d * affinePlaneMonomialCount k) +
          d * affinePlaneMonomialWeight k : ℕ) : ℝ) <
        (1 / Real.sqrt (d : ℝ) + η) *
          (affinePlaneMonomialWeight t + (t + 1) * s : ℕ) := by
  let a : ℝ := 1 / Real.sqrt (d : ℝ) + η
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have ha : 0 < a := by dsimp [a]; positivity
  have hsqrt_sq : (Real.sqrt (d : ℝ)) ^ 2 = d := Real.sq_sqrt hdR.le
  have hasqrt : a * Real.sqrt (d : ℝ) = 1 + η * Real.sqrt (d : ℝ) := by
    dsimp [a]
    field_simp
  obtain ⟨k, hk⟩ := exists_nat_gt
    ((3 * (b : ℝ) + 6 * a) / (2 * η * Real.sqrt (d : ℝ)))
  have hklarge : 3 * (b : ℝ) + 6 * a <
      2 * η * Real.sqrt (d : ℝ) * k := by
    have := (div_lt_iff₀ (by positivity : 0 < 2 * η * Real.sqrt (d : ℝ))).mp hk
    nlinarith
  let n := d * affinePlaneMonomialCount k
  have hcountpos : 0 < affinePlaneMonomialCount k := by
    have := two_mul_affinePlaneMonomialCount k
    nlinarith
  have hn : 0 < n := Nat.mul_pos hd hcountpos
  obtain ⟨t, s, hts, hs⟩ := exists_affinePlaneMonomialCount_remainder n hn
  refine ⟨k, t, s, hts, hs, ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcK : 2 * (affinePlaneMonomialCount k : ℝ) =
      ((k : ℝ) + 1) * (k + 2) := by
    exact_mod_cast two_mul_affinePlaneMonomialCount k
  have hcT : 2 * (affinePlaneMonomialCount t : ℝ) =
      ((t : ℝ) + 1) * (t + 2) := by
    exact_mod_cast two_mul_affinePlaneMonomialCount t
  have hwK : 3 * (affinePlaneMonomialWeight k : ℝ) =
      (k : ℝ) * (k + 1) * (k + 2) := by
    exact_mod_cast three_mul_affinePlaneMonomialWeight k
  have hnEq : (n : ℝ) = (d : ℝ) * affinePlaneMonomialCount k := by
    simp [n]
  have htsR : (n : ℝ) = (affinePlaneMonomialCount t : ℝ) + s := by
    exact_mod_cast hts
  have hsR : (s : ℝ) < t + 2 := by exact_mod_cast hs
  have htlarge : Real.sqrt (d : ℝ) * (k + 1) < t + 3 := by
    have hsqle : (Real.sqrt (d : ℝ) * (k + 1)) ^ 2 ≤ 2 * (n : ℝ) := by
      rw [mul_pow, hsqrt_sq]
      nlinarith [mul_nonneg hdR.le (Nat.cast_nonneg k)]
    have hsqgt : 2 * (n : ℝ) < ((t : ℝ) + 3) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (Real.sqrt (d : ℝ) * (k + 1) - (t + 3))]
  have hweight := affinePlane_partialWeight_lower_bound t s
  have hweightR : 2 * (t : ℝ) * n ≤
      3 * ((affinePlaneMonomialWeight t + (t + 1) * s : ℕ) : ℝ) := by
    rw [hts]
    exact_mod_cast hweight
  have harch : ((b * n + d * affinePlaneMonomialWeight k : ℕ) : ℝ) =
      (n : ℝ) * ((b : ℝ) + 2 * k / 3) := by
    push_cast
    rw [hnEq]
    have hwratio : 3 * (affinePlaneMonomialWeight k : ℝ) =
        2 * k * (affinePlaneMonomialCount k : ℝ) := by
      nlinarith [congrArg (fun x : ℝ => (k : ℝ) * x) hcK]
    nlinarith [congrArg (fun x : ℝ => (d : ℝ) * x) hwratio]
  have hgap : 3 * (b : ℝ) + 2 * k < 2 * a * t := by
    have hp := mul_lt_mul_of_pos_left htlarge (by positivity : 0 < 2 * a)
    nlinarith
  change ((b * n + d * affinePlaneMonomialWeight k : ℕ) : ℝ) <
    a * ((affinePlaneMonomialWeight t + (t + 1) * s : ℕ) : ℝ)
  rw [harch]
  have hp := mul_lt_mul_of_pos_right hgap hnR
  have hq := mul_le_mul_of_nonneg_left hweightR ha.le
  nlinarith

/-- For every fixed block coefficient bound, a block and a height threshold
exist before the box size and modulus are chosen. The local exponent is
exactly the partial-layer exponent used in the surface determinant theorem.
Only positivity of the degree is needed; in the application `d ≥ 4`. -/
theorem exists_surfaceNormalization_determinant_threshold
    (d b D : ℕ) (hd : 0 < d) (η : ℝ) (hη : 0 < η) :
    ∃ k t s : ℕ, ∃ B₀ : ℝ,
      1 ≤ B₀ ∧
      d * affinePlaneMonomialCount k = affinePlaneMonomialCount t + s ∧
      s < t + 2 ∧
      0 < affinePlaneMonomialWeight t + (t + 1) * s ∧
      ∀ B q : ℝ, B₀ ≤ B →
        B ^ (1 / Real.sqrt (d : ℝ) + η) ≤ q →
        (((d * affinePlaneMonomialCount k).factorial *
            D ^ (d * affinePlaneMonomialCount k) : ℕ) : ℝ) *
          B ^ (b * (d * affinePlaneMonomialCount k) +
            d * affinePlaneMonomialWeight k) <
          q ^ (affinePlaneMonomialWeight t + (t + 1) * s) := by
  obtain ⟨k, t, s, hrows, hs, hgap⟩ := exists_surfaceBlock_exponent_gap d b hd η hη
  let n := d * affinePlaneMonomialCount k
  let A := b * n + d * affinePlaneMonomialWeight k
  let E := affinePlaneMonomialWeight t + (t + 1) * s
  let a : ℝ := 1 / Real.sqrt (d : ℝ) + η
  let δ : ℝ := a * E - A
  let C : ℝ := (n.factorial * D ^ n : ℕ)
  have hδ : 0 < δ := sub_pos.2 hgap
  have hE : 0 < E := by
    by_contra he
    have he0 : E = 0 := by omega
    change (A : ℝ) < a * E at hgap
    rw [he0, Nat.cast_zero, mul_zero] at hgap
    exact (Nat.cast_nonneg A).not_gt hgap
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop hδ).eventually_gt_atTop C)
  refine ⟨k, t, s, max 1 B₁, le_max_left _ _, hrows, hs, hE, ?_⟩
  intro B q hB hq
  have hB1 : 1 ≤ B := (le_max_left 1 B₁).trans hB
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hC : C < B ^ δ := hB₁ B ((le_max_right 1 B₁).trans hB)
  change C * B ^ A < q ^ E
  calc
    C * B ^ A < B ^ δ * B ^ A :=
      mul_lt_mul_of_pos_right hC (pow_pos hBpos A)
    _ = B ^ (a * (E : ℝ)) := by
      rw [← Real.rpow_natCast B A, ← Real.rpow_add hBpos]
      congr 1
      dsimp [δ]
      ring
    _ = (B ^ a) ^ E := Real.rpow_mul_natCast hBpos.le a E
    _ ≤ q ^ E := pow_le_pow_left₀ (Real.rpow_nonneg hBpos.le a) hq E

/-- Integer-valued version, ready for the strict natural-number comparison
in `det_normalizationSurfaceBlockEvaluation_eq_zero`. -/
theorem exists_surfaceNormalization_determinant_threshold_nat
    (d b D : ℕ) (hd : 0 < d) (η : ℝ) (hη : 0 < η) :
    ∃ k t s : ℕ, ∃ B₀ : ℝ,
      1 ≤ B₀ ∧
      d * affinePlaneMonomialCount k = affinePlaneMonomialCount t + s ∧
      s < t + 2 ∧
      0 < affinePlaneMonomialWeight t + (t + 1) * s ∧
      ∀ B q : ℕ, B₀ ≤ (B : ℝ) →
        (B : ℝ) ^ (1 / Real.sqrt (d : ℝ) + η) ≤ q →
        (d * affinePlaneMonomialCount k).factorial *
          D ^ (d * affinePlaneMonomialCount k) *
          B ^ (b * (d * affinePlaneMonomialCount k) +
            d * affinePlaneMonomialWeight k) <
          q ^ (affinePlaneMonomialWeight t + (t + 1) * s) := by
  obtain ⟨k, t, s, B₀, hB₀, hrows, hs, hE, hbound⟩ :=
    exists_surfaceNormalization_determinant_threshold d b D hd η hη
  refine ⟨k, t, s, B₀, hB₀, hrows, hs, hE, ?_⟩
  intro B q hB hq
  exact_mod_cast hbound B q hB hq

end
end TranslatedDepthSeven
