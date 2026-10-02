import CubicTenVariables.FixedFamilyFiberPointCount

/-! The precise prime-field family count used by the prime-square estimate.
The family is fixed before the counting constant; the prime, parameter and
dimension threshold are arbitrary afterwards. This interface is narrower
than the general bounded-degree finite-field literature proposition.

This module only defines the interface and proves its implication from the
older literature input. It does not claim an unconditional inhabitant.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FixedFamilyPrimeFieldPointCount
open MvPolynomial BihomogeneousIncidenceFamily
open scoped Classical

/-- A bound for every literal fiber of a fixed integral polynomial family
over prime fields, using that fiber's actual geometric equation dimension.
Empty fibers and equations which specialize to zero are included. -/
def Uniform : Prop :=
  ∀ (m n t : ℕ) (f : Fin t → Polynomial m n),
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime]
      (v : Fin m → ZMod p) (j : ℕ),
      IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p) v ≤
        (j : WithBot ℕ∞) →
      (Finset.univ.filter (fun x : Fin n → ZMod p =>
        ∀ i, value (f i) v x = 0)).card ≤ C * p^j

/-- The finite-filter API used by the stationary-point estimate. -/
theorem exists_filter_bound (count : Uniform) {m n t : ℕ}
    (f : Fin t → Polynomial m n) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime]
      (v : Fin m → ZMod p) (j : ℕ),
      IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p) v ≤
        (j : WithBot ℕ∞) →
      (Finset.univ.filter (fun x : Fin n → ZMod p =>
        ∀ i, value (f i) v x = 0)).card ≤ C * p^j :=
  count m n t f

/-- The original broader literature input implies this exact interface.
This is a compatibility implication, not a proof of either input. -/
theorem of_literature (count : Literature.BoundedDegreeAffinePointCount) :
    Uniform := by
  intro m n t f
  obtain ⟨C,hC,hcount⟩ := FixedFamilyFiberPointCount.exists_filter_bound count f
  refine ⟨C,hC,?_⟩
  intro p hp v j hdim
  have hc := hcount (ZMod p) v j hdim
  rw [ZMod.card] at hc
  convert hc using 1
  congr 1
  ext x
  simp

end CubicTenVariables.FixedFamilyPrimeFieldPointCount
