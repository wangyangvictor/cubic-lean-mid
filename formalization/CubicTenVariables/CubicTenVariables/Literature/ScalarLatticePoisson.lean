import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Explicit generic scalar-lattice Poisson input

Primary textbook: E. M. Stein and R. Shakarchi, *Functional Analysis:
Introduction to Further Topics in Analysis*, Princeton Lectures in Analysis IV,
Princeton University Press, 2011, Chapter 8, Section 8.2, Proposition 8.2
and its proof, printed pp. 379–380. The proof gives the shifted integer-lattice
identity and absolute rapid convergence. The Fourier convention is fixed in
Chapter 3, Section 1.5, printed p. 107.

Primary text (PDF pages 398–399 and 126, counting the cover as page 1):
https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/0/26656/files/2023/10/STEIN-Shakarchi-Stein-Functional-Analysis_-Introduction-to-Further-Topics-in-Analysis-Princeton-Lectures-in-Analysis-Princeton-University-Press-2011.pdf

The scalar-lattice statement below is the affine-change corollary for
x ↦ a+c*x, c>0, of that proposition, not its verbatim statement. Its lattice
covolume is c^n, dual lattice is c^-1 Z^n, and translated dual phase has a
positive sign. The zero-dimensional case is the one-point identity.
All integrals use the product of the n standard coordinate Lebesgue measures;
this is definitionally the `volume` used by our physical oscillatory integrals.
The sup norm on `Fin n → ℝ` defines the same Schwartz space as the Euclidean
norm, since these norms are equivalent in finite dimension.

The proposition is retained as the interface used by the application adapters.
Its unconditional inhabitant is proved in `ScalarLatticePoissonProved` by
reusing the multidimensional Sphere-Packing-Lean theorem. No axiom, polynomial,
complete sum, counting formula or arithmetic saving is introduced or assumed.
Smooth compactly supported functions enter via
mathlib's proved `HasCompactSupport.toSchwartzMap`.
-/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ScalarLatticePoisson
open MeasureTheory
open scoped BigOperators SchwartzMap
variable {n : ℕ}

/-- Fourier transform with the negative 2πi coordinate-dot-product kernel
and the explicit product coordinate Lebesgue measure. -/
def fourier (f : (Fin n → ℝ) → ℂ) (ξ : Fin n → ℝ) : ℂ :=
  ∫ x : Fin n → ℝ, f x * Complex.exp
    (-2*(Real.pi : ℂ)*Complex.I*((∑ i, ξ i*x i : ℝ) : ℂ))
    ∂Measure.pi (fun _ : Fin n => (volume : Measure ℝ))

/-- No norm-dependent Haar normalization is hidden in the integral. -/
theorem fourier_eq_volume_integral (f : (Fin n → ℝ) → ℂ) (ξ : Fin n → ℝ) :
    fourier f ξ = ∫ x : Fin n → ℝ, f x * Complex.exp
      (-2*(Real.pi : ℂ)*Complex.I*((∑ i, ξ i*x i : ℝ) : ℂ)) := rfl

/-- The shifted scalar lattice x=a+cz, in literal real coordinates. -/
def point (c : ℝ) (a : Fin n → ℝ) (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i => a i+c*(z i : ℝ)

/-- The positive Fourier character from translation by a. -/
def phase (c : ℝ) (a : Fin n → ℝ) (v : Fin n → ℤ) : ℂ :=
  Complex.exp (2*(Real.pi : ℂ)*Complex.I*
    (((∑ i, (v i : ℝ)*a i)/c : ℝ) : ℂ))

end CubicTenVariables.ScalarLatticePoisson
namespace CubicTenVariables.Literature
open MeasureTheory ScalarLatticePoisson
open scoped BigOperators SchwartzMap

/-- Affine scalar-lattice corollary of Stein–Shakarchi (2011), Chapter 8,
Proposition 8.2 and its proof, pp. 379–380. Absolute summability is an explicit
conclusion on each side. The dual summability statement is independent of a.
The theorem `ScalarLatticePoissonProved.proved` supplies this proposition;
it is not a new axiom. -/
def SteinShakarchi2011Poisson : Prop :=
  ∀ (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ) (c : ℝ), 0 < c →
    ∀ a : Fin n → ℝ,
      Summable (fun z : Fin n → ℤ => ‖f (point c a z)‖) ∧
      Summable (fun v : Fin n → ℤ => ‖fourier f (fun i => (v i : ℝ)/c)‖) ∧
      (∑' z : Fin n → ℤ, f (point c a z)) =
        ((c : ℂ)^n)⁻¹ * ∑' v : Fin n → ℤ,
          phase c a v * fourier f (fun i => (v i : ℝ)/c)

end CubicTenVariables.Literature
