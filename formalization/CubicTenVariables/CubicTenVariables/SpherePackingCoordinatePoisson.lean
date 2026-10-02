import CubicTenVariables.SpherePackingPoisson
import CubicTenVariables.CoordinateFourierSchwartz

/-! The standard-lattice theorem reused from Sphere-Packing-Lean, transported
to the exact coordinate Fourier integral in this project. Source attribution
and the copied Apache-2.0 license accompany `SpherePackingPoisson.lean`.
No scalar-lattice Poisson premise is used. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SpherePackingCoordinatePoisson
open scoped BigOperators FourierTransform
variable {n : ℕ}

/-- Shifted unit-lattice Poisson summation with literal real coordinate
vectors and the negative `2πi` coordinate Fourier integral. -/
theorem standard (f : SchwartzMap (Fin n → ℝ) ℂ) (x : Fin n → ℝ) :
    (∑' z : Fin n → ℤ, f (x + fun i => (z i : ℝ))) =
      ∑' k : Fin n → ℤ, ScalarLatticePoisson.phase 1 x k *
        ScalarLatticePoisson.fourier f (fun i => (k i : ℝ)) := by
  let fE : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin n) ℝ) f
  let xE : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm x
  have hfourier (k : Fin n → ℤ) :
      𝓕 (fun y : EuclideanSpace ℝ (Fin n) => fE y)
          (SchwartzMap.PoissonSummation.Standard.intVec k) =
        ScalarLatticePoisson.fourier f (fun i => (k i : ℝ)) :=
    CoordinateFourierSchwartz.euclidean_fourier_eq f (fun i => (k i : ℝ))
  have hphase (k : Fin n → ℤ) :
      Complex.exp (2 * Real.pi * Complex.I *
        ⟪xE, SchwartzMap.PoissonSummation.Standard.intVec k⟫_[ℝ]) =
      ScalarLatticePoisson.phase 1 x k := by
    simp only [RCLike.wInner_one_eq_sum]
    change Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((∑ i, (k i : ℝ) * x i : ℝ) : ℂ)) = _
    simp [ScalarLatticePoisson.phase]
  calc
    _ = ∑' z : SchwartzMap.standardLattice n, fE (xE + z) := by
      simpa only [SchwartzMap.PoissonSummation.Standard.coe_equivIntVec] using
        (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := n)).tsum_eq
          (fun z : SchwartzMap.standardLattice n => fE (xE + z))
    _ = ∑' k : Fin n → ℤ,
        𝓕 (fun y : EuclideanSpace ℝ (Fin n) => fE y)
          (SchwartzMap.PoissonSummation.Standard.intVec k) *
        Complex.exp (2 * Real.pi * Complex.I *
          ⟪xE, SchwartzMap.PoissonSummation.Standard.intVec k⟫_[ℝ]) :=
      SchwartzMap.PoissonSummation.Standard.poissonSummation_standard fE xE
    _ = _ := by simp_rw [hfourier, hphase, mul_comm]

end CubicTenVariables.SpherePackingCoordinatePoisson
