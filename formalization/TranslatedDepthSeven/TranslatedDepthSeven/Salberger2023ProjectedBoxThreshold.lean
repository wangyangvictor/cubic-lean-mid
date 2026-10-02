import TranslatedDepthSeven.BoundedAffineProjectionMassInternal
import TranslatedDepthSeven.Salberger2023CurveCountNumerics

/-!
# Uniform local-prime threshold after bounded plane projection

The plane projection enlarges a source box of side `M` to the literal side
`projectedCurveCertificateRadius N δ M`.  Its extra factor is polynomial in
the varying degree.  When `δ = O(1 + log V)`, that factor is absorbed in a
fixed exponent gap, uniformly for every degree above Salberger's cutoff.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1500000

/-- The actual homogeneous-coordinate box after applying a bounded affine
plane projection to a source box of side `M`. -/
def salbergerProjectedCurveBoxRadius (N δ M : ℕ) : ℕ :=
  max 1 (boundedAffineProjectionRowMassBound N δ * max 1 M)

/-- A convenient polynomial majorant for the explicit projection row mass. -/
theorem boundedAffineProjectionRowMassBound_le_degreePower (N δ : ℕ) :
    boundedAffineProjectionRowMassBound N δ ≤
      (N + 1) * (δ + 1) ^ (2 * (N + 1)) := by
  unfold boundedAffineProjectionRowMassBound boundedAffineProjectionEntryBound
  apply Nat.mul_le_mul_left
  apply max_le
  · exact Nat.pow_le_pow_right (by omega : 1 ≤ δ + 1) (by omega)
  · have hbase : δ * δ + 1 ≤ (δ + 1) ^ 2 := by nlinarith
    calc
      (δ * δ + 1) ^ (N + 1) ≤ ((δ + 1) ^ 2) ^ (N + 1) :=
        Nat.pow_le_pow_left hbase _
      _ = (δ + 1) ^ (2 * (N + 1)) := by rw [← pow_mul]

private theorem projectedBox_rpow_le_of_polylog_absorption
    {R C l V r γ β : ℝ} {k : ℕ}
    (hR : 0 ≤ R)
    (hRle : R ≤ C * l ^ k * V)
    (hr0 : 0 ≤ r)
    (hrγ : r ≤ γ)
    (hbase : 1 ≤ C * l ^ k * V)
    (hfactor : 1 ≤ C * l ^ k)
    (hγtwo : γ ≤ 2)
    (hV0 : 0 ≤ V)
    (habsorb : C ^ 2 * l ^ (2 * k) * V ^ γ ≤ V ^ β) :
    R ^ r ≤ V ^ β := by
  calc
    R ^ r ≤ (C * l ^ k * V) ^ r :=
      Real.rpow_le_rpow hR hRle hr0
    _ ≤ (C * l ^ k * V) ^ γ :=
      Real.rpow_le_rpow_of_exponent_le hbase hrγ
    _ = (C * l ^ k) ^ γ * V ^ γ := by
      rw [Real.mul_rpow (by positivity) hV0]
    _ ≤ (C * l ^ k) ^ (2 : ℕ) * V ^ γ := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [Real.rpow_two] using
          (Real.rpow_le_rpow_of_exponent_le hfactor hγtwo)
      · positivity
    _ = C ^ 2 * l ^ (2 * k) * V ^ γ := by
      rw [mul_pow, ← pow_mul]
      rw [Nat.mul_comm k 2]
    _ ≤ V ^ β := habsorb

private theorem projectedCurve_boxPower_pointwise
    (N δ M : ℕ) (Cd γ β V : ℝ)
    (hCd : 0 ≤ Cd)
    (hV : 1 < V)
    (hδ : (δ : ℝ) ≤ Cd * (1 + Real.log V))
    (hM : (M : ℝ) ≤ V)
    (hrγ : 8 / ((δ : ℝ) + 3) ≤ γ)
    (hγtwo : γ ≤ 2)
    (habsorb :
      (((N + 1 : ℕ) : ℝ) * (Cd + 1) ^ (2 * (N + 1))) ^ 2 *
          (1 + Real.log V) ^ (2 * (2 * (N + 1))) * V ^ γ ≤ V ^ β) :
    (salbergerProjectedCurveBoxRadius N δ M : ℝ) ^
        (8 / ((δ : ℝ) + 3)) ≤ V ^ β := by
  let k : ℕ := 2 * (N + 1)
  let C : ℝ := (N + 1 : ℕ) * (Cd + 1) ^ k
  let l : ℝ := 1 + Real.log V
  have hl : 1 ≤ l := by
    dsimp only [l]
    have : (0 : ℝ) ≤ Real.log V := Real.log_nonneg hV.le
    linarith
  have hδone : ((δ + 1 : ℕ) : ℝ) ≤ (Cd + 1) * l := by
    push_cast
    dsimp only [l] at hδ ⊢
    nlinarith
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact one_le_mul_of_one_le_of_one_le (by
      exact_mod_cast (show 1 ≤ N + 1 by omega))
      (one_le_pow₀ (by linarith))
  have hmass : (boundedAffineProjectionRowMassBound N δ : ℝ) ≤
      C * l ^ k := by
    have hnat := boundedAffineProjectionRowMassBound_le_degreePower N δ
    calc
      (boundedAffineProjectionRowMassBound N δ : ℝ) ≤
          (((N + 1) * (δ + 1) ^ (2 * (N + 1)) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      _ = ((N + 1 : ℕ) : ℝ) * (((δ + 1 : ℕ) : ℝ) ^ k) := by
        push_cast
        rfl
      _ ≤ ((N + 1 : ℕ) : ℝ) * (((Cd + 1) * l) ^ k) := by
        gcongr
      _ = C * l ^ k := by
        dsimp only [C]
        rw [mul_pow]
        ring
  have hmaxM : ((max 1 M : ℕ) : ℝ) ≤ V := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le hV.le hM
  have hbox : (salbergerProjectedCurveBoxRadius N δ M : ℝ) ≤
      C * l ^ k * V := by
    rw [salbergerProjectedCurveBoxRadius, Nat.cast_max, Nat.cast_one,
      Nat.cast_mul]
    apply max_le
    · have : (1 : ℝ) ≤ C * l ^ k :=
        one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hl)
      exact this.trans (le_mul_of_one_le_right (by positivity) hV.le)
    · exact mul_le_mul hmass hmaxM (by positivity) (by positivity)
  have hr0 : 0 ≤ 8 / ((δ : ℝ) + 3) := by positivity
  have hbase : 1 ≤ C * l ^ k * V := by
    have : (1 : ℝ) ≤ C * l ^ k :=
      one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hl)
    exact this.trans (le_mul_of_one_le_right (by positivity) hV.le)
  have hfactor : 1 ≤ C * l ^ k := by
    exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hl)
  apply projectedBox_rpow_le_of_polylog_absorption
  · positivity
  · exact hbox
  · exact hr0
  · exact hrγ
  · exact hbase
  · exact hfactor
  · exact hγtwo
  · linarith
  · simpa only [C, k, l] using habsorb

/-- The projected box satisfies the actual local threshold uniformly in the
varying degree and source side.  The exponent is selected before `V`, `δ`
and `M`. -/
theorem exists_uniform_projectedCurve_boxPrimeExponent
    (N : ℕ) (Cd ε : ℝ) (hCd : 0 ≤ Cd) (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ β < ε / 2 ∧
      (∀ δ : ℕ, ⌈16 / ε⌉₊ < δ →
        8 / ((δ : ℝ) + 3) < β) ∧
      ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ,
        ⌈16 / ε⌉₊ < δ →
        (δ : ℝ) ≤ Cd * (1 + Real.log V) →
        (M : ℝ) ≤ V →
        (salbergerProjectedCurveBoxRadius N δ M : ℝ) ^
            (8 / ((δ : ℝ) + 3)) ≤ V ^ β := by
  let c : ℕ := ⌈16 / ε⌉₊
  let γ : ℝ := 8 / ((c : ℝ) + 4)
  let β : ℝ := (γ + ε / 2) / 2
  let k : ℕ := 2 * (N + 1)
  let C : ℝ := (N + 1 : ℕ) * (Cd + 1) ^ k
  have hden : 0 < (c : ℝ) + 4 := by positivity
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  have hc : 16 / ε ≤ (c : ℝ) := Nat.le_ceil _
  have hc' : 16 ≤ (c : ℝ) * ε := (div_le_iff₀ hε).mp hc
  have hγlt : γ < ε / 2 := by
    dsimp only [γ]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hγβ : γ < β := by dsimp only [β]; linarith
  have hβε : β < ε / 2 := by dsimp only [β]; linarith
  have hβ : 0 < β := hγ.trans hγβ
  have hγtwo : γ ≤ 2 := by
    dsimp only [γ]
    apply (div_le_iff₀ hden).mpr
    have hc0 : (0 : ℝ) ≤ c := by positivity
    nlinarith
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact one_le_mul_of_one_le_of_one_le (by
      exact_mod_cast (show 1 ≤ N + 1 by omega))
      (one_le_pow₀ (by linarith))
  have hdegree : ∀ δ : ℕ, c < δ → 8 / ((δ : ℝ) + 3) < β := by
    intro δ hδ
    have hδ' : (c : ℝ) + 1 ≤ (δ : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hδ
    have hle : 8 / ((δ : ℝ) + 3) ≤ γ := by
      dsimp only [γ]
      exact div_le_div_of_nonneg_left (by norm_num) hden (by linarith)
    exact hle.trans_lt hγβ
  have habsorb := eventually_polylog_mul_rpow_le_rpow
    (C ^ 2) γ β (2 * k) (sq_nonneg C) hγβ
  refine ⟨β, hβ, hβε, by simpa only [c] using hdegree, ?_⟩
  filter_upwards [habsorb, eventually_gt_atTop (1 : ℝ)] with V habsorb hV
  intro δ M hcut hδ hM
  have hrγ : 8 / ((δ : ℝ) + 3) ≤ γ := by
    have hδ' : (c : ℝ) + 1 ≤ (δ : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (by simpa only [c] using hcut)
    dsimp only [γ]
    exact div_le_div_of_nonneg_left (by norm_num) hden (by linarith)
  apply projectedCurve_boxPower_pointwise N δ M Cd γ β V hCd hV hδ hM hrγ hγtwo
  simpa only [C, k] using habsorb

/-- Direct conversion from the projected-box comparison to the strict prime
threshold used by the local determinant theorem. -/
theorem projectedCurve_primeThreshold_of_box_bound
    {N δ M p : ℕ} {V β : ℝ}
    (hbox : (salbergerProjectedCurveBoxRadius N δ M : ℝ) ^
      (8 / ((δ : ℝ) + 3)) ≤ V ^ β)
    (hp : 4 * V ^ β < p) :
    4 * (salbergerProjectedCurveBoxRadius N δ M : ℝ) ^
        (8 / ((δ : ℝ) + 3)) < p := by
  exact (mul_le_mul_of_nonneg_left hbox (by norm_num)).trans_lt hp

end

end TranslatedDepthSeven
