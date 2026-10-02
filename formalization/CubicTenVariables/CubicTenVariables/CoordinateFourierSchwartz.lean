import CubicTenVariables.Literature.ScalarLatticePoisson
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The literal coordinate Fourier integral preserves Schwartz functions.
The Euclidean-space adapter preserves the product coordinate Lebesgue
measure and the negative `2πi` dot-product kernel. No Poisson statement is
assumed. The result also includes dimension zero. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CoordinateFourierSchwartz
open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform
variable {n : ℕ}

/-- Change of coordinates from mathlib's Euclidean Fourier transform to
the exact integral used in the scalar-lattice statement. -/
theorem euclidean_fourier_eq (f : (Fin n → ℝ) → ℂ) (ξ : Fin n → ℝ) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm ξ) = ScalarLatticePoisson.fourier f ξ := by
  rw [Real.fourier_eq', ScalarLatticePoisson.fourier_eq_volume_integral]
  have hm := (PiLp.volume_preserving_ofLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
    (fun x : Fin n → ℝ => f x * Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ)))
  rw [← hm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 1
    congr 1
    simp only [PiLp.inner_apply]
    change (↑(-2 * Real.pi * ∑ i, ξ i * x.ofLp i) : ℂ) * Complex.I = _
    push_cast
    ring

/-- The Fourier transform as an actual Schwartz function in the original
coordinate sup norm. -/
def transform (f : SchwartzMap (Fin n → ℝ) ℂ) : SchwartzMap (Fin n → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin n) ℝ).symm
    (SchwartzMap.fourierTransformCLM ℂ
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin n) ℝ) f))

theorem transform_apply (f : SchwartzMap (Fin n → ℝ) ℂ) (ξ : Fin n → ℝ) :
    transform f ξ = ScalarLatticePoisson.fourier f ξ := by
  change 𝓕 (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))
    ((EuclideanSpace.equiv (Fin n) ℝ).symm ξ) = _
  exact euclidean_fourier_eq f ξ

/-- The exact coordinate integral has a Schwartz representative, with no
analytic or Poisson premise supplied by the caller. -/
theorem exists_schwartz (f : SchwartzMap (Fin n → ℝ) ℂ) :
    ∃ g : SchwartzMap (Fin n → ℝ) ℂ,
      ∀ ξ : Fin n → ℝ, g ξ = ScalarLatticePoisson.fourier f ξ :=
  ⟨transform f, transform_apply f⟩

end CubicTenVariables.CoordinateFourierSchwartz
