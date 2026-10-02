import HessianTheorem11.UnconditionalWeightRational
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-! Actual integral representatives of the rational fixed-support optimal
ray, obtained by clearing a finite family of positive denominators. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightOptimization
open MvPolynomial
variable {n : ℕ}

/-- A rational real vector has a positive integral multiple. -/
theorem exists_positive_integral_multiple (w : WeightSpace n)
    (hrat : ∃ u : Fin n → ℚ, ∀ j, (u j : ℝ) = w j) :
    ∃ (N : ℤ) (z : Fin n → ℤ), 0 < N ∧
      WithLp.toLp 2 (fun j => (z j : ℝ)) = (N : ℝ) • w := by
  obtain ⟨u,hu⟩ := hrat
  obtain ⟨N,hN⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) u
  choose z hz using hN
  refine ⟨N,z,N.property,?_⟩
  ext j
  have h : (z j : ℚ) = (N.val : ℚ) * u j := by
    simpa only [Algebra.smul_def] using hz j
  have hh : (z j : ℝ) = (N.val : ℝ) * (u j : ℝ) := by exact_mod_cast h
  simpa only [hu j] using hh

/-- The fixed-support optimum is represented by actual determinant-one
integral variable weights. The real minimum-norm point is retained so that
its sharp comparison theorem applies without any new optimization premise. -/
theorem exists_integral_optimal_ray (S : Finset (Fin n →₀ ℕ))
    (hS : S.Nonempty) (hne : (feasible S).Nonempty) :
    ∃ (w : WeightSpace n) (N : ℤ) (z : Fin n → ℤ),
      MinimumNorm S w ∧ 0 < N ∧
      WithLp.toLp 2 (fun j => (z j : ℝ)) = (N : ℝ) • w ∧
      (∑ j, z j) = 0 ∧ (∀ e ∈ S, 0 < monomialWeight z e) ∧ z ≠ 0 := by
  obtain ⟨w,hw,_⟩ := exists_unique_minimumNorm S hne
  obtain ⟨N,z,hN,hz⟩ := exists_positive_integral_multiple w (minimumNorm_rational hw)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : (∑ j, z j) = 0 := by
    have h := congrArg weightSum hz
    rw [map_smul,hw.1.1,smul_zero] at h
    change (∑ j, (z j : ℝ)) = 0 at h
    exact_mod_cast h
  have hp : ∀ e ∈ S, 0 < monomialWeight z e := by
    intro e he
    have h := congrArg (realMonomialWeight e) hz
    rw [map_smul] at h
    have hpos : 0 < (N : ℝ) * realMonomialWeight e w :=
      mul_pos hNr (lt_of_lt_of_le zero_lt_one (hw.1.2 e he))
    change (∑ j, (e j : ℝ) * (z j : ℝ)) = (N : ℝ) * realMonomialWeight e w at h
    rw [← h] at hpos
    exact_mod_cast hpos
  refine ⟨w,N,z,hw,hN,hz,hsum,hp,?_⟩
  intro hz0
  obtain ⟨e,he⟩ := hS
  have h := hp e he
  simp [hz0,monomialWeight] at h

end HessianTheorem11.UnconditionalWeightOptimization
