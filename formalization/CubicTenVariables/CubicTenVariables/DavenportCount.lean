import CubicTenVariables.DimensionBoxCount
import CubicTenVariables.DavenportDimension
import CubicTenVariables.DavenportHomogeneity
import CubicTenVariables.IntegerAnisotropy
import CubicTenVariables.Literature.Bernert

/-! Davenport's actual Hessian-rank count, proved from rational anisotropy.
The stronger bound O(B^r), with no epsilon loss, follows by counting the
homogeneous rational closure of the exact-rank locus. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial HessianTheorem11 TranslatedDepthSeven

/-- Literal integer Hessian-rank counts satisfy the dimension exponent. -/
theorem hessianRankCount_le_of_no_integer_zero {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) (r : ℕ) :
    ∃ K : ℕ, ∀ B : ℕ, 1 ≤ B → hessianRankCount F B r ≤ K * B ^ r := by
  classical
  let A := anisotropicCubicOfNoIntegerZero F hF hzero
  let Z : Set (Fin n → ℚ) := {x | (hessian A.polynomial x).rank = r}
  obtain ⟨K, hK⟩ := homogeneous_box_count (vanishingIdeal ℚ Z)
    (DavenportHomogeneity.rank_locus_vanishingIdeal_isHomogeneous
      A.polynomial A.homogeneous r)
    (DavenportDimension.rank_locus_dimension_le A)
  refine ⟨K, fun B hB ↦ ?_⟩
  apply hK ((integerBox n B).filter fun x ↦ integerHessianRank F x = r) B hB
    (Finset.filter_subset _ _)
  intro x hx f hf
  exact hf _ (Finset.mem_filter.mp hx).2

/-- The standard epsilon formulation follows from the stronger integral
power bound. No Davenport literature premise is used. -/
theorem proved_davenportGood_of_no_integer_zero {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) : DavenportGood F := by
  intro ε hε r _hr
  obtain ⟨K, hK⟩ := hessianRankCount_le_of_no_integer_zero F hF hzero r
  refine ⟨(K : ℝ) + 1, by positivity, fun B hB ↦ ?_⟩
  have hcount : (hessianRankCount F B r : ℝ) ≤ (K : ℝ) * (B : ℝ) ^ r := by
    exact_mod_cast hK B hB
  have hpower : (B : ℝ) ^ r ≤ (B : ℝ) ^ ((r : ℝ) + ε) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB) (by linarith)
  calc
    (hessianRankCount F B r : ℝ) ≤ (K : ℝ) * (B : ℝ) ^ r := hcount
    _ ≤ ((K : ℝ) + 1) * (B : ℝ) ^ ((r : ℝ) + ε) :=
      mul_le_mul (by linarith) hpower (by positivity) (by positivity)

/-- The precise tensor used to represent an arbitrary cubic already
satisfies Bernert's geometric hypothesis, without Davenport as an input. -/
theorem proved_canonicalTensor_good {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    Literature.TensorDavenportGood (symmetricTensorOfCubic F) :=
  (Literature.canonicalTensor_good_iff F hF).mpr
    (proved_davenportGood_of_no_integer_zero F hF hzero)

end CubicTenVariables
