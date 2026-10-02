import CubicTenVariables.CountingEndpoint
import HessianTheorem11.Geometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Concrete complete sums, singular-series expressions and Davenport goodness.

The sign convention is the manuscript's `eq:defSq`:
`S_q(v) = Σ_(a mod q, (a,q)=1) Σ_(x mod q) exp(2πi(a F(x)+v·x)/q)`.
Residues are represented by `Fin q`, so these are finite sums with no
quotient-ring representative choices. No convergence or analytic estimate
is asserted by these definitions. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial
open scoped BigOperators

/-- The concrete additive exponential `exp(2π i m/q)`. The complete-sum
outer index is empty at `q=0`, so that value does not represent a modulus. -/
def residueExponential (q : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (q : ℂ))

@[simp] theorem residueExponential_zero (q : ℕ) :
    residueExponential q 0 = 1 := by
  simp [residueExponential]

/-- The integer phase evaluated on the canonical residue representatives. -/
def completeSumPhase {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    {q : ℕ} (a : Fin q) (x : Fin n → Fin q) (v : Fin n → ℤ) : ℤ :=
  (a.val : ℤ) * eval (fun i => ((x i).val : ℤ)) F +
    ∑ i : Fin n, v i * (x i).val

/-- The actual complete cubic exponential sum with the manuscript's positive
frequency sign. The definition is meaningful for arbitrary integer polynomials. -/
def completeCubicSum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q : ℕ) (v : Fin n → ℤ) : ℂ :=
  ∑ a : Fin q, if Nat.Coprime a.val q then
    ∑ x : Fin n → Fin q, residueExponential q (completeSumPhase F a x v)
  else 0

@[simp] theorem completeCubicSum_zero_modulus {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ) :
    completeCubicSum F 0 v = 0 := by
  simp [completeCubicSum]

@[simp] theorem completeCubicSum_one {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ) :
    completeCubicSum F 1 v = 1 := by
  simp [completeCubicSum, completeSumPhase, residueExponential]

/-- The zero-frequency term `q^(-n) S_q(0)`, with the artificial index
`q=0` set to zero. -/
def singularSeriesTerm {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (q : ℕ) : ℂ :=
  if q = 0 then 0 else completeCubicSum F q 0 / (q : ℂ) ^ n

@[simp] theorem singularSeriesTerm_zero {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    singularSeriesTerm F 0 = 0 := by
  simp [singularSeriesTerm]

@[simp] theorem singularSeriesTerm_one {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    singularSeriesTerm F 1 = 1 := by
  simp [singularSeriesTerm]

/-- The actual partial singular series, summed over the positive moduli ≤Q. -/
def singularSeriesPartial {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (Q : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, singularSeriesTerm F q

/-- The formal `tsum` of the actual singular-series terms. A use as an
analytic singular series requires a separate convergence theorem. -/
def singularSeries {n : ℕ} (F : MvPolynomial (Fin n) ℤ) : ℂ :=
  ∑' q : ℕ, singularSeriesTerm F q

/-- Absolute convergence of the actual series, an explicit proposition
and not an assertion that this property has been proved. -/
def SingularSeriesAbsolutelyConvergent {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) : Prop :=
  Summable (fun q : ℕ => ‖singularSeriesTerm F q‖)

@[simp] theorem singularSeriesPartial_zero {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    singularSeriesPartial F 0 = 0 := by
  simp [singularSeriesPartial]

@[simp] theorem singularSeriesPartial_one {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    singularSeriesPartial F 1 = 1 := by
  simp [singularSeriesPartial]

/-- Rank over Q of the actual Hessian evaluated at an integral vector. -/
def integerHessianRank {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (x : Fin n → ℤ) : ℕ :=
  (HessianTheorem11.hessian (map (Int.castRingHom ℚ) F)
    (fun i => (x i : ℚ))).rank

/-- The actual number of integer vectors of Hessian rank exactly r in the
closed box. This count includes the origin, as in Davenport goodness. -/
def hessianRankCount {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (B r : ℕ) : ℕ := by
  classical
  exact ((integerBox n B).filter fun x => integerHessianRank F x = r).card

/-- Davenport's growth property for the actual Hessian rank counts.
The form F is fixed; constants may depend on F, epsilon and r. Restricting
B to positive integral radii suffices for arbitrary real radii by rounding. -/
def DavenportGood {n : ℕ} (F : MvPolynomial (Fin n) ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ r : ℕ, r ≤ n →
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B →
      (hessianRankCount F B r : ℝ) ≤ C * (B : ℝ) ^ ((r : ℝ) + ε)

theorem hessianRankCount_le_box_card {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (B r : ℕ) : hessianRankCount F B r ≤ (integerBox n B).card := by
  classical
  exact Finset.card_filter_le _ _

end CubicTenVariables
