import TranslatedDepthSeven.Parameters

/-!
# Exact rescaling of an integral congruence class

This file records, in arbitrary finite dimension, the elementary change of
variables `x = x₀ + r z` used before the curve estimate.  It proves existence
and uniqueness from literal coordinatewise congruence and the translated-box
bound on the new coordinates.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Coordinatewise congruence of two integral vectors modulo `r`. -/
def IntVectorCongruent {n : ℕ} (r : ℕ)
    (x x₀ : IntVector n) : Prop :=
  ∀ i, (x i : ZMod r) = (x₀ i : ZMod r)

/-- Two coordinatewise congruent vectors differ by `r` times an integral
vector. -/
theorem exists_intVector_rescaling
    {n r : ℕ} {x x₀ : IntVector n}
    (hcongr : IntVectorCongruent r x x₀) :
    ∃ z : IntVector n, ∀ i, x i = x₀ i + r * z i := by
  classical
  have hdvd : ∀ i, (r : ℤ) ∣ x₀ i - x i := by
    intro i
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (x₀ i) r).mp
    exact hcongr i
  let c : IntVector n := fun i ↦ Classical.choose (hdvd i)
  have hc : ∀ i, x₀ i - x i = (r : ℤ) * c i :=
    fun i ↦ Classical.choose_spec (hdvd i)
  refine ⟨fun i ↦ -c i, ?_⟩
  intro i
  have hxi : x i = x₀ i - (r : ℤ) * c i := by
    linarith [hc i]
  simpa [mul_neg, sub_eq_add_neg] using hxi

/-- The rescaled integral vector is unique when `r` is positive. -/
theorem intVector_rescaling_unique
    {n r : ℕ} (hr : 0 < r) {x x₀ z z' : IntVector n}
    (hz : ∀ i, x i = x₀ i + r * z i)
    (hz' : ∀ i, x i = x₀ i + r * z' i) : z = z' := by
  funext i
  have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  apply mul_left_cancel₀ hr0
  linarith [hz i, hz' i]

/-- Exact existence and uniqueness of the congruence-class rescaling. -/
theorem existsUnique_intVector_rescaling
    {n r : ℕ} (hr : 0 < r) {x x₀ : IntVector n}
    (hcongr : IntVectorCongruent r x x₀) :
    ∃! z : IntVector n, ∀ i, x i = x₀ i + r * z i := by
  obtain ⟨z, hz⟩ := exists_intVector_rescaling hcongr
  exact ⟨z, hz, fun z' hz' ↦ intVector_rescaling_unique hr hz' hz⟩

/-- A pair of points in one real translated box, separated by `r z`, gives
the sharp coordinate bound `|z_i| ≤ 2R/r`. -/
theorem intVector_rescaling_coordinate_bound
    {n r : ℕ} (hr : 0 < r)
    {x x₀ z : IntVector n} {center : RealVector n} {R : ℝ}
    (hx : ∀ i, |(x i : ℝ) - center i| ≤ R)
    (hx₀ : ∀ i, |(x₀ i : ℝ) - center i| ≤ R)
    (hscale : ∀ i, x i = x₀ i + r * z i) (i : Fin n) :
    |(z i : ℝ)| ≤ 2 * R / r := by
  have hdist : |(x i : ℝ) - x₀ i| ≤ 2 * R := by
    calc
      |(x i : ℝ) - x₀ i| =
          |((x i : ℝ) - center i) - ((x₀ i : ℝ) - center i)| := by ring_nf
      _ ≤ |(x i : ℝ) - center i| + |(x₀ i : ℝ) - center i| := abs_sub _ _
      _ ≤ R + R := add_le_add (hx i) (hx₀ i)
      _ = 2 * R := by ring
  have heq : |(x i : ℝ) - x₀ i| = (r : ℝ) * |(z i : ℝ)| := by
    have hcast := congrArg (fun a : ℤ ↦ (a : ℝ)) (hscale i)
    norm_num at hcast
    rw [hcast, add_sub_cancel_left, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg r)]
  rw [heq] at hdist
  rw [le_div_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)]
  simpa [mul_comm] using hdist

end

end TranslatedDepthSeven
