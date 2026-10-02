import TranslatedDepthSeven.SurfaceNormalizationDeterminantThreshold
import Mathlib.Analysis.MeanInequalities

/-!
# Summing the exact smooth surface determinant exponents

The exponent is constructed from the first `n` bivariate monomials, including
the last partial degree layer. The lower bound retains the coefficient
`2 * sqrt 2 / 3`; its error is at most twice the number of rows. These are
numerical statements. No local smoothness, point count, or determinant
divisibility is postulated here.
-/

namespace TranslatedDepthSeven
noncomputable section

set_option maxHeartbeats 1000000

/-- The exact first-`n` bivariate jet weight, using complete degree layers
and the required part of the next layer. The empty packet has weight zero. -/
def smoothSurfaceJetExponent (n : ℕ) : ℕ :=
  if hn : 0 < n then
    let h := exists_affinePlaneMonomialCount_remainder n hn
    affinePlaneMonomialWeight h.choose + (h.choose + 1) * h.choose_spec.choose
  else 0

@[simp] theorem smoothSurfaceJetExponent_zero : smoothSurfaceJetExponent 0 = 0 := by
  simp [smoothSurfaceJetExponent]

/-- The decomposition and exact exponent are produced internally from the
number of rows, rather than supplied as a row-weight hypothesis. -/
theorem exists_smoothSurfaceJetExponent_layer (n : ℕ) (hn : 0 < n) :
    ∃ t u : ℕ, n = affinePlaneMonomialCount t + u ∧ u < t + 2 ∧
      smoothSurfaceJetExponent n = affinePlaneMonomialWeight t + (t + 1) * u := by
  let h := exists_affinePlaneMonomialCount_remainder n hn
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2, ?_⟩
  simp [smoothSurfaceJetExponent, hn]

private theorem jetLayer_count_mono {a b : ℕ} (hab : a ≤ b) :
    affinePlaneMonomialCount a ≤ affinePlaneMonomialCount b := by
  unfold affinePlaneMonomialCount
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hab 1)
  · simp

private theorem jetLayer_unique (t u t' u' : ℕ)
    (hu : u < t + 2) (hu' : u' < t' + 2)
    (heq : affinePlaneMonomialCount t + u = affinePlaneMonomialCount t' + u') :
    t = t' ∧ u = u' := by
  have hstep (k : ℕ) : affinePlaneMonomialCount (k + 1) =
      affinePlaneMonomialCount k + (k + 2) := by
    simp [affinePlaneMonomialCount, Finset.sum_range_succ]
  have hnegt : ¬ t < t' := by
    intro hlt
    have hle := jetLayer_count_mono (by omega : t + 1 ≤ t')
    rw [hstep] at hle
    omega
  have hnegt' : ¬ t' < t := by
    intro hlt
    have hle := jetLayer_count_mono (by omega : t' + 1 ≤ t)
    rw [hstep] at hle
    omega
  have htt' : t = t' := by omega
  subst t'
  exact ⟨rfl, by omega⟩

/-- Any valid complete-layer/partial-layer decomposition computes the
canonical exponent. Thus a determinant proof can use its existing layer
indices without any equality assumption about the chosen exponent. -/
theorem smoothSurfaceJetExponent_eq_of_layer (n t u : ℕ)
    (hn : n = affinePlaneMonomialCount t + u) (hu : u < t + 2) :
    smoothSurfaceJetExponent n = affinePlaneMonomialWeight t + (t + 1) * u := by
  have hcount : 0 < affinePlaneMonomialCount t := by
    have := two_mul_affinePlaneMonomialCount t
    nlinarith
  obtain ⟨t', u', hn', hu', hE⟩ :=
    exists_smoothSurfaceJetExponent_layer n (by omega)
  obtain ⟨rfl, rfl⟩ := jetLayer_unique t' u' t u hu' hu (hn'.symm.trans hn)
  exact hE

private theorem rpow_three_halves_eq_mul_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  convert Real.rpow_one_add' hx (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0) using 1
  norm_num

/-- The sharp leading coefficient of the local surface exponent, with an
explicit universal linear error. -/
theorem smoothSurfaceJetExponent_lower_bound (n : ℕ) :
    (2 * Real.sqrt 2 / 3) * (n : ℝ) ^ (3 / 2 : ℝ) - 2 * n ≤
      (smoothSurfaceJetExponent n : ℝ) := by
  by_cases hn : 0 < n
  · obtain ⟨t, u, hnEq, hu, hE⟩ := exists_smoothSurfaceJetExponent_layer n hn
    have hc : 2 * (affinePlaneMonomialCount t : ℝ) =
        ((t : ℝ) + 1) * (t + 2) := by
      exact_mod_cast two_mul_affinePlaneMonomialCount t
    have hnEqR : (n : ℝ) = (affinePlaneMonomialCount t : ℝ) + u := by
      exact_mod_cast hnEq
    have huR : (u : ℝ) < t + 2 := by exact_mod_cast hu
    have hsquare : 2 * (n : ℝ) < ((t : ℝ) + 3) ^ 2 := by nlinarith
    have hsqrt : Real.sqrt (2 * (n : ℝ)) ≤ t + 3 := by
      have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * n)
      nlinarith [Real.sqrt_nonneg (2 * (n : ℝ))]
    have hw : 2 * (t : ℝ) * n ≤ 3 * (smoothSurfaceJetExponent n : ℝ) := by
      rw [hE, hnEq]
      exact_mod_cast affinePlane_partialWeight_lower_bound t u
    have hm := mul_le_mul_of_nonneg_right hsqrt (show (0 : ℝ) ≤ n by positivity)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hm
    rw [rpow_three_halves_eq_mul_sqrt _ (by positivity)]
    nlinarith
  · have hn0 : n = 0 := by omega
    subst n
    simp

/-- Sum over an actual finite family of smooth residue classes. `M` is
only an upper bound for its cardinality; zero-sized classes are allowed. -/
theorem sum_smoothSurfaceJetExponent_lower_bound
    {ι : Type*} (a : Finset ι) (n : ι → ℕ) (M : ℕ)
    (hM : 0 < M) (hcard : a.card ≤ M) :
    (2 * Real.sqrt 2 / 3) * ((∑ i ∈ a, n i : ℕ) : ℝ) ^ (3 / 2 : ℝ) /
        Real.sqrt (M : ℝ) - 2 * (∑ i ∈ a, n i : ℕ) ≤
      ((∑ i ∈ a, smoothSurfaceJetExponent (n i) : ℕ) : ℝ) := by
  let c : ℝ := 2 * Real.sqrt 2 / 3
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hloc : c * (∑ i ∈ a, (n i : ℝ) ^ (3 / 2 : ℝ)) ≤
      ∑ i ∈ a, ((smoothSurfaceJetExponent (n i) : ℝ) + 2 * n i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      have := smoothSurfaceJetExponent_lower_bound (n i)
      dsimp [c]
      linarith
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := a) (f := fun i => (n i : ℝ)) (p := (3 / 2 : ℝ)) (by norm_num)
    (fun i hi => Nat.cast_nonneg _)
  norm_num only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at hholder
  rw [← Real.sqrt_eq_rpow] at hholder
  have hsqrtcard : Real.sqrt (a.card : ℝ) ≤ Real.sqrt (M : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hcard
  have hholderM : (∑ i ∈ a, (n i : ℝ)) ^ (3 / 2 : ℝ) ≤
      Real.sqrt (M : ℝ) * ∑ i ∈ a, (n i : ℝ) ^ (3 / 2 : ℝ) :=
    hholder.trans (mul_le_mul_of_nonneg_right hsqrtcard (by positivity))
  have htotal : c * (∑ i ∈ a, (n i : ℝ)) ^ (3 / 2 : ℝ) ≤
      Real.sqrt (M : ℝ) *
        ((∑ i ∈ a, (smoothSurfaceJetExponent (n i) : ℝ)) +
          2 * ∑ i ∈ a, (n i : ℝ)) := by
    have h₁ := mul_le_mul_of_nonneg_left hholderM hc
    have h₂ := mul_le_mul_of_nonneg_left hloc (Real.sqrt_nonneg (M : ℝ))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h₂
    nlinarith
  have hsqrtM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hM)
  have hdiv : c * (∑ i ∈ a, (n i : ℝ)) ^ (3 / 2 : ℝ) / Real.sqrt (M : ℝ) ≤
      (∑ i ∈ a, (smoothSurfaceJetExponent (n i) : ℝ)) +
        2 * ∑ i ∈ a, (n i : ℝ) := by
    apply (div_le_iff₀ hsqrtM).2
    simpa only [mul_comm (Real.sqrt (M : ℝ))] using htotal
  push_cast
  dsimp [c] at hdiv
  linarith

/-- Tangent estimate that measures exactly the loss from discarding some
rows. This does not need differentiability or a limiting argument. -/
theorem rpow_three_halves_discard_lower_bound (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (3 / 2 : ℝ) - (3 / 2 : ℝ) * (x - y) * Real.sqrt x ≤
      y ^ (3 / 2 : ℝ) := by
  rw [rpow_three_halves_eq_mul_sqrt x hx, rpow_three_halves_eq_mul_sqrt y hy]
  have hp : 0 ≤ (Real.sqrt x - Real.sqrt y) ^ 2 *
      (Real.sqrt x + 2 * Real.sqrt y) := by positivity
  have heq : (Real.sqrt x - Real.sqrt y) ^ 2 *
      (Real.sqrt x + 2 * Real.sqrt y) =
      x * Real.sqrt x - 3 * y * Real.sqrt x + 2 * y * Real.sqrt y := by
    calc
      _ = (Real.sqrt x) ^ 2 * Real.sqrt x -
          3 * (Real.sqrt y) ^ 2 * Real.sqrt x +
          2 * (Real.sqrt y) ^ 2 * Real.sqrt y := by ring
      _ = _ := by rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
  rw [heq] at hp
  nlinarith

/-- A sharp-coefficient global smooth-class estimate with `b` discarded
rows. Singular reductions can be discarded without inventing a smooth
local exponent for them. Their total loss is displayed explicitly. -/
theorem sum_smoothSurfaceJetExponent_lower_bound_discard
    {ι : Type*} (a : Finset ι) (n : ι → ℕ) (M s b : ℕ)
    (hM : 0 < M) (hcard : a.card ≤ M) (hb : b ≤ s)
    (hrows : (∑ i ∈ a, n i) = s - b) :
    (2 * Real.sqrt 2 / 3) * (s : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt (M : ℝ) -
        Real.sqrt 2 * b * Real.sqrt (s : ℝ) / Real.sqrt (M : ℝ) - 2 * s ≤
      ((∑ i ∈ a, smoothSurfaceJetExponent (n i) : ℕ) : ℝ) := by
  have hlocal := sum_smoothSurfaceJetExponent_lower_bound a n M hM hcard
  rw [hrows] at hlocal
  have htangent := rpow_three_halves_discard_lower_bound (s : ℝ) ((s - b : ℕ) : ℝ)
    (by positivity) (by positivity)
  rw [Nat.cast_sub hb] at hlocal htangent
  have hc : 0 ≤ 2 * Real.sqrt 2 / 3 / Real.sqrt (M : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left htangent hc
  have hmul' : (2 * Real.sqrt 2 / 3) * (s : ℝ) ^ (3 / 2 : ℝ) /
        Real.sqrt (M : ℝ) - Real.sqrt 2 * b * Real.sqrt (s : ℝ) /
        Real.sqrt (M : ℝ) ≤
      (2 * Real.sqrt 2 / 3) * ((s : ℝ) - b) ^ (3 / 2 : ℝ) /
        Real.sqrt (M : ℝ) := by
    convert hmul using 1 <;> ring
  have hbR : (0 : ℝ) ≤ b := by positivity
  linarith

end
end TranslatedDepthSeven
