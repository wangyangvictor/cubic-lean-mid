import CubicTenVariables.CoordinateFourierSchwartz
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Uniform Fourier decay from a common compact support and bounded derivatives.
The derivative bounds are genuine hypotheses and are converted to integral bounds;
no oscillatory localization or delta-method conclusion is assumed. Compact parameter
families supply these bounds when their derivatives are jointly continuous. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.UniformFourierFamily
open MeasureTheory
open scoped BigOperators FourierTransform Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The common support bounds the integral of each actual derivative. -/
theorem integral_norm_iteratedFDeriv_le (f : E → ℂ) (K : Set E)
    (hK : IsCompact K) (hs : tsupport f ⊆ K) (j : ℕ) (B : ℝ)
    (hb : ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    (∫ x, ‖iteratedFDeriv ℝ j f x‖) ≤ B * (volume K).toReal := by
  have he : (∫ x in K, ‖iteratedFDeriv ℝ j f x‖) =
      ∫ x, ‖iteratedFDeriv ℝ j f x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : iteratedFDeriv ℝ j f x = 0 := by
      by_contra hn
      exact hx (hs (support_iteratedFDeriv_subset j hn))
    simp [hz]
  have h := norm_setIntegral_le_of_norm_le_const_ae' (μ := volume) (f := fun x => ‖iteratedFDeriv ℝ j f x‖) hK.measure_lt_top
    (Filter.Eventually.of_forall fun x hx => by
      simpa only [norm_norm] using hb x hx)
  rw [he, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at h
  exact h

/-- Explicit Fourier decay. All derivative orders through `N` are controlled on
one compact set; outside it their vanishing follows from the support condition. -/
theorem pow_mul_norm_fourier_le (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (K : Set E) (hK : IsCompact K) (hs : tsupport f ⊆ K)
    (N : ℕ) (B : ℕ → ℝ)
    (hb : ∀ j, j ≤ N → ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B j)
    (ξ : E) :
    ‖ξ‖ ^ N * ‖𝓕 f ξ‖ ≤ (2 : ℝ)^N * (volume K).toReal *
      ∑ j ∈ Finset.range (N+1), B j := by
  have hc : HasCompactSupport f := hK.of_isClosed_subset isClosed_closure hs
  have hint (j : ℕ) : Integrable (iteratedFDeriv ℝ j f) :=
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
      (hc.iteratedFDeriv j)
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K := (0 : ℕ∞)) (N := (N : ℕ∞)) (hf.of_le (by exact_mod_cast le_top))
    (fun k j hk _ => by
      have hk0 : k = 0 := by simpa using hk
      subst k
      simpa using (hint j).norm)
    (k := 0) (n := N) (by simp) (by simp) ξ
  simp only [norm_iteratedFDeriv_zero, pow_zero, Nat.cast_zero, zero_add, mul_zero, one_mul,
    Finset.range_one, Finset.sum_product, Finset.sum_singleton] at h
  calc
    _ ≤ (2 : ℝ)^N * ∑ j ∈ Finset.range (N+1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ := h
    _ ≤ (2 : ℝ)^N * ∑ j ∈ Finset.range (N+1), B j * (volume K).toReal := by
      gcongr with j hj
      exact integral_norm_iteratedFDeriv_le f K hK hs j (B j)
        (hb j (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A bound valid at every frequency, including zero. The constant is explicit
and depends only on the common support and derivative bounds through `N`. -/
theorem one_add_norm_pow_mul_fourier_le (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (K : Set E) (hK : IsCompact K) (hs : tsupport f ⊆ K)
    (N : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hb : ∀ j, j ≤ N → ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ B j)
    (ξ : E) :
    (1 + ‖ξ‖)^N * ‖𝓕 f ξ‖ ≤
      (2 : ℝ)^N * (1 + (2 : ℝ)^N) * (volume K).toReal *
        ∑ j ∈ Finset.range (N+1), B j := by
  have hN := pow_mul_norm_fourier_le f hf K hK hs N B hb ξ
  have h0 := pow_mul_norm_fourier_le f hf K hK hs 0 B
    (fun j hj => hb j (hj.trans (Nat.zero_le N))) ξ
  simp only [pow_zero, one_mul, Nat.zero_add, Finset.range_one,
    Finset.sum_singleton] at h0
  have hB0 : B 0 ≤ ∑ j ∈ Finset.range (N+1), B j :=
    Finset.single_le_sum (fun j _ => hB j) (by simp)
  have h0' : ‖𝓕 f ξ‖ ≤ (volume K).toReal * ∑ j ∈ Finset.range (N+1), B j := by
    exact h0.trans (mul_le_mul_of_nonneg_left hB0 ENNReal.toReal_nonneg)
  have hp : (1 + ‖ξ‖)^N ≤ (2 : ℝ)^N * (1 + ‖ξ‖^N) := by
    have h := add_pow_le (show (0:ℝ) ≤ 1 by norm_num) (norm_nonneg ξ) N
    simp only [one_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.sub_le N 1)) (by positivity))
  calc
    _ ≤ ((2 : ℝ)^N * (1 + ‖ξ‖^N)) * ‖𝓕 f ξ‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = (2 : ℝ)^N * (‖𝓕 f ξ‖ + ‖ξ‖^N * ‖𝓕 f ξ‖) := by ring
    _ ≤ (2 : ℝ)^N * ((volume K).toReal * (∑ j ∈ Finset.range (N+1), B j) +
        (2 : ℝ)^N * (volume K).toReal * (∑ j ∈ Finset.range (N+1), B j)) := by
      gcongr
    _ = _ := by ring

/-- Compact parameters turn joint continuity of the finitely many derivatives
into a single decay constant before every parameter and frequency. -/
theorem exists_uniform_bound {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (A : T → E → ℂ) (hA : ∀ t, ContDiff ℝ ∞ (A t))
    (K : Set E) (hK : IsCompact K) (hs : ∀ t, tsupport (A t) ⊆ K)
    (N : ℕ)
    (hj : ∀ j, j ≤ N → Continuous (fun z : T × E =>
      iteratedFDeriv ℝ j (A z.1) z.2)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : T) (ξ : E),
      ‖𝓕 (A t) ξ‖ ≤ C / (1 + ‖ξ‖)^N := by
  have hb : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      (j ≤ N → ∀ (t : T) (x : E), x ∈ K → ‖iteratedFDeriv ℝ j (A t) x‖ ≤ B) := by
    intro j
    by_cases hjN : j ≤ N
    · obtain ⟨B,hB⟩ := (isCompact_univ.prod hK).bddAbove_image (hj j hjN).norm.continuousOn
      refine ⟨max 0 B,le_max_left _ _,?_⟩
      intro _ t x hx
      exact (hB ⟨(t,x),⟨Set.mem_univ t,hx⟩,rfl⟩).trans (le_max_right _ _)
    · exact ⟨0,le_rfl,fun h => (hjN h).elim⟩
  choose B hB hb using hb
  let C := (2 : ℝ)^N * (1 + (2 : ℝ)^N) * (volume K).toReal *
    ∑ j ∈ Finset.range (N+1), B j
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro t ξ
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖ξ‖) N)).mpr
  rw [mul_comm]
  exact (one_add_norm_pow_mul_fourier_le (A t) (hA t) K hK (hs t) N B hB
    (fun j hj x hx => hb j hj t x hx) ξ).trans (le_max_right _ _)

/-- The same uniform estimate for the literal product-coordinate Fourier
integral. Parameters and the constant precede every coordinate frequency;
Euclidean and coordinate measures are identified exactly, with no Haar factor.
The input amplitudes and their derivative bounds are stated in Euclidean
coordinates, and the conclusion uses the coordinate supremum norm. -/
theorem exists_coordinate_bound {T : Type*} [TopologicalSpace T] [CompactSpace T]
    {n : ℕ} (A : T → EuclideanSpace ℝ (Fin n) → ℂ)
    (hA : ∀ t, ContDiff ℝ ∞ (A t))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hs : ∀ t, tsupport (A t) ⊆ K) (N : ℕ)
    (hj : ∀ j, j ≤ N → Continuous (fun z : T × EuclideanSpace ℝ (Fin n) =>
      iteratedFDeriv ℝ j (A z.1) z.2)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : T) (ξ : Fin n → ℝ),
      ‖ScalarLatticePoisson.fourier
        (fun x => A t ((EuclideanSpace.equiv (Fin n) ℝ).symm x)) ξ‖ ≤
          C / (1 + ‖ξ‖)^N := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_bound A hA K hK hs N hj
  refine ⟨C,hC,?_⟩
  intro t ξ
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hξ : ‖ξ‖ ≤ ‖e.symm ξ‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (e.symm ξ))).mpr
    intro i
    simpa [e] using PiLp.norm_apply_le (e.symm ξ) i
  have he : 𝓕 (A t) (e.symm ξ) = ScalarLatticePoisson.fourier
      (fun x => A t (e.symm x)) ξ := by
    simpa [e] using CoordinateFourierSchwartz.euclidean_fourier_eq
      (fun x => A t (e.symm x)) ξ
  rw [← he]
  exact (hbound t (e.symm ξ)).trans
    (div_le_div_of_nonneg_left (zero_le_one.trans hC) (by positivity)
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖ξ‖ ≤ 1 + ‖e.symm ξ‖) N))

end CubicTenVariables.UniformFourierFamily
