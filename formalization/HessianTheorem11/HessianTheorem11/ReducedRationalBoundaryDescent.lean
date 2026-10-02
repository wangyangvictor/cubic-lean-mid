import HessianTheorem11.ReducedRationalFlagDescent
import HessianTheorem11.NonzeroLimitTransport

/-! The arithmetic descent step for an existing nonzero weight limit.
This is an actual conditional helper, not a replacement external input:
existence of the invariant boundary flag is not asserted here. -/
noncomputable section
namespace HessianTheorem11.ReducedRationalBoundary
open MvPolynomial RationalDescent PolynomialRestriction PolynomialWeightTransport

variable {K : Type*} [Field K] {n : ℕ}

theorem nonnegativeWeights_of_same_weightFlag
    (F : MvPolynomial (Fin n) K) (B C : Matrix (Fin n) (Fin n) K)
    (w : Fin n → ℤ) (hB : Function.Injective B.mulVec)
    (hflags : weightFlag B w = weightFlag C w)
    (hW : HasNonnegativeWeights (restrict B F) w) :
    HasNonnegativeWeights (restrict C F) w := by
  have h := hasNonnegativeWeights_restrict_of_entry_weights
    (frameTransition B C hB) w w (frameTransition_weight_monotone B C w hB hflags)
    (restrict B F) hW
  rwa [restrict_restrict, matrix_mul_frameTransition] at h

/-- If the geometric existing-limit flag is Galois invariant, its full
nonnegative support and exact nonzero weight vector descend to rational
coordinates. This proves the arithmetic step without a descent input.
It does not assert existence of such a flag for a nonclosed orbit. -/
theorem rational_existing_limit_of_invariant_flag (F : RationalPolynomial n)
    (f : WeightFrame GeometricField n) (hf : f.RationalFlag) (hw : f.weight ≠ 0)
    (hW : HasNonnegativeWeights (restrict f.matrix (geometricPolynomial F)) f.weight) :
    ∃ B : Matrix (Fin n) (Fin n) ℚ, Function.Injective B.mulVec ∧
      ∃ w : Fin n → ℤ, (∑ i, w i) = 0 ∧ w ≠ 0 ∧
        HasNonnegativeWeights (restrict B F) w := by
  obtain ⟨g,hweight,hflag⟩ := ReducedRationalDescent.rationalFlagDescent.split f hf
  have hflags : weightFlag f.matrix f.weight =
      weightFlag (g.matrix.map (algebraMap ℚ GeometricField)) f.weight := by
    rw [hweight] at hflag
    exact hflag.symm
  have h := nonnegativeWeights_of_same_weightFlag (geometricPolynomial F)
    f.matrix (g.matrix.map (algebraMap ℚ GeometricField)) f.weight f.injective hflags hW
  rw [← hweight] at h
  change HasNonnegativeWeights
    (restrict (g.matrix.map (algebraMap ℚ GeometricField))
      (map (algebraMap ℚ GeometricField) F)) g.weight at h
  rw [← map_restrict] at h
  refine ⟨g.matrix,g.injective,g.weight,g.sum_zero,by rwa [hweight],?_⟩
  unfold HasNonnegativeWeights at h ⊢
  simpa only [MvPolynomial.support_map_of_injective _ (algebraMap ℚ GeometricField).injective]
    using h

end HessianTheorem11.ReducedRationalBoundary
