import CubicTenVariables.ComplementMergedSieve

/-! Exact finite-tail allocation maps, retaining the original integer
frequency. Merging the two allocated factors recovers the existing sieve map. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementAllocationSamples
open MvPolynomial NumericalPrimeDepth NumericalDepthAllocation

abbrev Sample := ComplementMergedSieve.Sample
abbrev Allocation (i : Fin 5) :=
  ((Fin (5-i.val) → ℕ) × (Fin (5-i.val) → ℕ)) × (Fin 10 → ℤ)

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

/-- The full tail of exact ordinary and square-prime factors at the
original frequency, indexed by consecutive depths i+2,...,6. -/
def allocationTuple (h : CoarseBounds F C) (i : Fin 5) (x : Sample) : Allocation i :=
  ((fun k => primePart h x.1.1 x.2 (i.val+k.val+2),
    fun k => squarePart h x.1.2 x.2 (i.val+k.val+2)),x.2)

/-- Forget the split into the two kinds of prime factors, retaining the frequency. -/
def mergeAllocation (i : Fin 5) (z : Allocation i) :
    (Fin (5-i.val) → ℕ) × (Fin 10 → ℤ) :=
  (fun k => z.1.1 k*z.1.2 k,z.2)

theorem merge_allocationTuple (h : CoarseBounds F C) (i : Fin 5) (x : Sample) :
    mergeAllocation i (allocationTuple h i x) = ComplementMergedSieve.mergedTuple h i x := rfl

theorem image_merge_allocationTuple (h : CoarseBounds F C) (i : Fin 5) (E : Finset Sample) :
    (E.image (allocationTuple h i)).image (mergeAllocation i) =
      E.image (ComplementMergedSieve.mergedTuple h i) := by
  classical
  rw [Finset.image_image]
  rfl

end CubicTenVariables.ComplementAllocationSamples
