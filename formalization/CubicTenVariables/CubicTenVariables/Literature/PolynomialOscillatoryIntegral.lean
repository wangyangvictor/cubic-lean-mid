import CubicTenVariables.SingularIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Explicit polynomial oscillatory localization input

Primary reference: T. D. Browning and D. R. Heath-Brown, *Rational points on
quartic hypersurfaces*, J. reine angew. Math. 629 (2009), 37–88, Lemma 6 and
its proof. Pinned text: arXiv:math/0701348v2, printed pp. 14–15 (Lemma 9,
printed p. 21, applies it after rescaling).
https://arxiv.org/pdf/math/0701348v2

The real-coefficient version is the one used in that proof at the normalized
polynomial P⁻³g(Px); the proof uses degree/coefficient bounds, not integrality.
Here the polynomial and weight are fixed before every phase/frequency/scale.
Their degree, coefficient height, support radius and derivative bounds may
enter the constants. This is weaker than the uniform coefficient-height form.

Crucially, the localization set is the PRINTED ENLARGED BOX |x|≤1+S, not
supp(w). The source manuscript's support-restricted refinement is not encoded.
The input is a proposition passed explicitly, not an axiom or an inhabitant.
No cubic, rational anisotropy, finite sum or arithmetic estimate occurs in it.
-/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PolynomialOscillatory
open MvPolynomial MeasureTheory
open scoped BigOperators Topology ContDiff

/-- The literal real polynomial phase, including the negative linear term. -/
def integral {n : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (t : ℝ) (u : Fin n → ℝ) : ℂ :=
  ∫ x : Fin n → ℝ, (w x : ℂ) * Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I *
      ((t * eval x f - ∑ i, u i * x i : ℝ) : ℂ))

/-- The exact enlarged-box window in the cited lemma. On the function space
Fin n → R, the norm is the maximum of the coordinate absolute values. -/
def window {n : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (S H t : ℝ) (u : Fin n → ℝ) (R : ℝ) : Set (Fin n → ℝ) :=
  {x | ‖x‖ ≤ 1 + S ∧
    ‖(fun i => t * eval x (pderiv i f) - u i)‖ ≤ R * max 1 (Real.sqrt (|t| * H))}

/-- This real measure is finite: the window is contained in the fixed box. -/
theorem window_measure_ne_top {n : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (S H t : ℝ) (u : Fin n → ℝ) (R : ℝ) : volume (window f S H t u R) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (show volume (Metric.closedBall (0 : Fin n → ℝ) (1 + S)) < ⊤ from
      measure_closedBall_lt_top).ne
  apply measure_mono
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1

end PolynomialOscillatory
namespace Literature
open MvPolynomial MeasureTheory
open scoped Topology ContDiff

/-- Generic fixed-polynomial/fixed-weight specialization of BHB09 Lemma 6.
Constants precede the varying t,u,R. The lower cutoff R₀ permits exactly the
source's R>c(d,n); choosing a larger cutoff changes no intended application. -/
def BrowningHeathBrown2009Lemma6 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (f : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ), ContDiff ℝ ∞ w → HasCompactSupport w →
    (∀ x, 0 ≤ w x) → ∀ S : ℝ, 0 ≤ S →
    (∀ x ∈ tsupport w, ‖x‖ ≤ S) →
    ∃ H : ℝ, 1 ≤ H ∧ ∀ N : ℕ, 1 ≤ N →
      ∃ C R₀ : ℝ, 1 ≤ C ∧ 1 ≤ R₀ ∧
      ∀ (t : ℝ) (u : Fin n → ℝ) (R : ℝ), R₀ ≤ R →
      ‖PolynomialOscillatory.integral f w t u‖ ≤
        C * (R ^ (-(N : ℝ)) +
          (volume (PolynomialOscillatory.window f S H t u R)).toReal)

end Literature
end CubicTenVariables
