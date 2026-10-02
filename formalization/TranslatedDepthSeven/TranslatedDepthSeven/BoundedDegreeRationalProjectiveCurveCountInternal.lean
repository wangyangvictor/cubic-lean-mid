import TranslatedDepthSeven.BoundedDegreeProjectedCurveCountInternal
import TranslatedDepthSeven.BoundedAffineChartProjectionPrimeInternal
import TranslatedDepthSeven.IntegerBoxCount

/-! Coefficient-uniform bounded-degree rational-curve counting. Bounded
projection is constructed from the actual curve, and the eventual threshold
is removed using a fixed ambient box. -/
namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published Filter
open scoped Topology
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000

/-- The bounded integral projection can be chosen internally. -/
theorem eventually_boundedDegree_rationalCurve_count_internal
    (N D : ℕ) (hN : 1 < N) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ,
      2 ≤ δ → δ ≤ D → (M : ℝ) ≤ V →
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (hI : I.IsPrime),
        I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) →
        HasProjectiveDimensionDegree I 1 δ →
      ∀ X : Finset (IntVector N),
        (∀ z ∈ X, ∀ f ∈ I, eval (rationalIntegralAffineChartPoint z) f = 0) →
        (∀ z ∈ X, ∀ i, (z i).natAbs ≤ M) →
        (X.card : ℝ) ≤ V ^ ((1 : ℝ) / 2 + ε) := by
  filter_upwards [eventually_boundedDegree_projectedCurve_count_internal N D ε hε,
    eventually_ge_atTop (1 : ℝ)] with V hcount hV
  intro δ M hδ hδD hM I hI hIhom hdegree X hzero hbox
  by_cases hX : X.Nonempty
  · obtain ⟨z, hz⟩ := hX
    have hXzero : MvPolynomial.X (0 : Fin (N + 1)) ∉ I := by
      intro hmem
      have heq := hzero z hz (MvPolynomial.X 0) hmem
      have : (1 : ℚ) = 0 := by simpa using heq
      exact one_ne_zero this
    obtain ⟨A, hA, G, hprojection, _himageDegree⟩ :=
      exists_mem_boundedIntegralAffineProjectionMatrices N 1 δ hN
        I hI hIhom hXzero δ hdegree le_rfl
    exact hcount δ M hδ hδD hM I hI hIhom hdegree A G hA hprojection X hzero hbox
  · rw [Finset.not_nonempty_iff_eq_empty] at hX
    simp only [hX, Finset.card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (by linarith) _

/-- One constant, chosen before the coefficients, degree, height and point
set, bounds every bounded-degree rational curve by H^(1/2+epsilon). The
coordinates are the actual affine integer points in the first chart. -/
theorem exists_boundedDegree_rationalCurve_halfPower_count
    (N D : ℕ) (hN : 1 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℕ, 2 ≤ δ → δ ≤ D →
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (hI : I.IsPrime),
        I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) →
        HasProjectiveDimensionDegree I 1 δ →
      ∀ H : ℝ, 1 ≤ H → ∀ X : Finset (IntVector N),
        (∀ z ∈ X, ∀ f ∈ I, eval (rationalIntegralAffineChartPoint z) f = 0) →
        (∀ z ∈ X, ∀ i, |(z i : ℝ)| ≤ H) →
        (X.card : ℝ) ≤ C * H ^ ((1 : ℝ) / 2 + ε) := by
  classical
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp
    (eventually_boundedDegree_rationalCurve_count_internal N D hN ε hε)
  let T : ℝ := max 1 V₀
  let a : ℝ := 1 / 2 + ε
  let C : ℝ := (2 : ℝ) ^ a + (((2 * ⌈T⌉₊ + 1) ^ N : ℕ) : ℝ) + 1
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hT : 1 ≤ T := le_max_left _ _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδD I hI hIhom hdegree H hH X hzero hbox
  by_cases hlarge : T ≤ 2 * H
  · have hM : (⌈H⌉₊ : ℝ) ≤ 2 * H :=
      (Nat.ceil_lt_add_one (by linarith : 0 ≤ H)).le.trans (by linarith)
    have hboxNat : ∀ z ∈ X, ∀ i, (z i).natAbs ≤ ⌈H⌉₊ := by
      intro z hz i
      have hreal : ((z i).natAbs : ℝ) ≤ H := by simpa only [Nat.cast_natAbs, Int.cast_abs] using hbox z hz i
      exact_mod_cast hreal.trans (Nat.le_ceil H)
    have hcount := hV₀ (2 * H) ((le_max_right 1 V₀).trans hlarge)
      δ ⌈H⌉₊ hδ hδD hM I hI hIhom hdegree X hzero hboxNat
    have hrewrite : (2 * H) ^ a = (2 : ℝ) ^ a * H ^ a :=
      Real.mul_rpow (by norm_num) (by linarith)
    change (X.card : ℝ) ≤ C * H ^ a
    apply hcount.trans
    rw [hrewrite]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    dsimp only [C]
    have : (0 : ℝ) ≤ (((2 * ⌈T⌉₊ + 1) ^ N : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  · have hHT : H ≤ T := by linarith
    have hboxT : ∀ z ∈ X, ∀ i, (z i).natAbs ≤ ⌈T⌉₊ := by
      intro z hz i
      have hreal : ((z i).natAbs : ℝ) ≤ H := by simpa only [Nat.cast_natAbs, Int.cast_abs] using hbox z hz i
      exact_mod_cast (hreal.trans hHT).trans (Nat.le_ceil T)
    have hsmall : (X.card : ℝ) ≤ (((2 * ⌈T⌉₊ + 1) ^ N : ℕ) : ℝ) := by
      exact_mod_cast card_intVector_finset_le_box X hboxT
    have hpow : 1 ≤ H ^ a := Real.one_le_rpow hH ha
    change (X.card : ℝ) ≤ C * H ^ a
    apply hsmall.trans
    calc
      (((2 * ⌈T⌉₊ + 1) ^ N : ℕ) : ℝ) ≤ C := by
        dsimp only [C]
        have : 0 ≤ (2 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
        linarith
      _ ≤ C * H ^ a := by nlinarith [hC]

end
end TranslatedDepthSeven
