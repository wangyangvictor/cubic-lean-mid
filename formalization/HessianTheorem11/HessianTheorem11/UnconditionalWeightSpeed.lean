import HessianTheorem11.UnconditionalWeightIntegral
import HessianTheorem11.UnconditionalWeightTransport

/-! The rational least-length point gives an actual integer weight vector
attaining the best normalized monomial weight for a fixed finite support. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightOptimization
open MvPolynomial RationalDescent
variable {n : ℕ}

def realWeight (z : Fin n → ℤ) : WeightSpace n :=
  WithLp.toLp 2 (fun j => (z j : ℝ))

def finiteMinimum (S : Finset (Fin n →₀ ℕ)) (z : Fin n → ℤ) : ℤ :=
  if h : S.Nonempty then S.inf' h (monomialWeight z) else 0

def finiteSpeed (S : Finset (Fin n →₀ ℕ)) (z : Fin n → ℤ) : ℝ :=
  (finiteMinimum S z : ℝ) / ‖realWeight z‖

theorem finiteMinimum_le {S : Finset (Fin n →₀ ℕ)} (z : Fin n → ℤ)
    {e : Fin n →₀ ℕ} (he : e ∈ S) : finiteMinimum S z ≤ monomialWeight z e := by
  classical
  have hS : S.Nonempty := ⟨e,he⟩
  simpa only [finiteMinimum, dif_pos hS] using Finset.inf'_le (monomialWeight z) he

theorem finiteMinimum_attained {S : Finset (Fin n →₀ ℕ)} (hS : S.Nonempty)
    (z : Fin n → ℤ) : ∃ e ∈ S, finiteMinimum S z = monomialWeight z e := by
  classical
  simpa only [finiteMinimum, dif_pos hS] using Finset.exists_mem_eq_inf' hS (monomialWeight z)

@[simp] theorem realMonomialWeight_realWeight (e : Fin n →₀ ℕ) (z : Fin n → ℤ) :
    realMonomialWeight e (realWeight z) = (monomialWeight z e : ℝ) := by
  simp [realMonomialWeight, realWeight, monomialWeight]

@[simp] theorem weightSum_realWeight (z : Fin n → ℤ) :
    weightSum (realWeight z) = ((∑ j, z j : ℤ) : ℝ) := by
  simp [weightSum, realWeight]

theorem finiteSpeed_le_minimumNorm {S : Finset (Fin n →₀ ℕ)} (hS : S.Nonempty)
    {w : WeightSpace n} (hw : MinimumNorm S w) (z : Fin n → ℤ)
    (hsum : ∑ j, z j = 0) : finiteSpeed S z ≤ 1 / ‖w‖ := by
  by_cases hp : 0 < finiteMinimum S z
  · apply normalized_bound hS hw (realWeight z) (by simp [hsum])
      (finiteMinimum S z : ℝ) (by exact_mod_cast hp)
    intro e he
    rw [realMonomialWeight_realWeight]
    exact_mod_cast finiteMinimum_le z he
  · have hz : finiteSpeed S z ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast le_of_not_gt hp) (norm_nonneg _)
    exact hz.trans (one_div_nonneg.mpr (norm_nonneg _))

theorem finiteSpeed_of_minimumNorm_multiple {S : Finset (Fin n →₀ ℕ)}
    (hS : S.Nonempty) {w : WeightSpace n} (hw : MinimumNorm S w)
    (N : ℤ) (hN : 0 < N) (z : Fin n → ℤ)
    (hz : realWeight z = (N : ℝ) • w) :
    finiteSpeed S z = 1 / ‖w‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hweight (e : Fin n →₀ ℕ) :
      (monomialWeight z e : ℝ) = (N : ℝ) * realMonomialWeight e w := by
    rw [← realMonomialWeight_realWeight, hz, map_smul]
    rfl
  have hmin : finiteMinimum S z = N := by
    apply le_antisymm
    · obtain ⟨e,he,heq⟩ := minimumNorm_active hS hw
      have hh : monomialWeight z e = N := by
        have h := hweight e
        rw [heq,mul_one] at h
        exact_mod_cast h
      exact (finiteMinimum_le z he).trans hh.le
    · obtain ⟨e,he,heq⟩ := finiteMinimum_attained hS z
      rw [heq]
      have h := mul_le_mul_of_nonneg_left (hw.1.2 e he) hNr.le
      rw [mul_one, ← hweight] at h
      exact_mod_cast h
  have hn : ‖w‖ ≠ 0 := (norm_pos_iff.mpr (feasible_ne_zero hS hw.1)).ne'
  rw [finiteSpeed,hmin,hz,norm_smul,Real.norm_eq_abs,abs_of_pos hNr]
  field_simp

/-- An actual integer vector achieves the maximum over all integer
sum-zero weights; the proof does not assume a rational-polyhedron theorem. -/
theorem exists_fixed_support_maximizer (S : Finset (Fin n →₀ ℕ))
    (hS : S.Nonempty) (hne : (feasible S).Nonempty) :
    ∃ z : Fin n → ℤ, (∑ j, z j) = 0 ∧
      (∀ e ∈ S, 0 < monomialWeight z e) ∧
      0 < finiteSpeed S z ∧
      ∀ u : Fin n → ℤ, (∑ j, u j) = 0 → finiteSpeed S u ≤ finiteSpeed S z := by
  obtain ⟨w,N,z,hw,hN,hz,hsum,hpos,hne⟩ := exists_integral_optimal_ray S hS hne
  have he := finiteSpeed_of_minimumNorm_multiple hS hw N hN z hz
  refine ⟨z,hsum,hpos,?_,?_⟩
  · rw [he]
    exact one_div_pos.mpr (norm_pos_iff.mpr (feasible_ne_zero hS hw.1))
  · intro u hu
    rw [he]
    exact finiteSpeed_le_minimumNorm hS hw u hu

theorem instability_eq_finiteSpeed {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) (f : WeightFrame K n) :
    f.instability F = finiteSpeed (PolynomialRestriction.restrict f.matrix F).support f.weight := by
  unfold WeightFrame.instability finiteSpeed minimumWeight finiteMinimum
  congr 1
  simp [realWeight, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

end HessianTheorem11.UnconditionalWeightOptimization
