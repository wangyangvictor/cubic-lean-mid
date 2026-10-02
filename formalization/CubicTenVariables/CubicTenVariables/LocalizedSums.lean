import CubicTenVariables.ExponentialSums
import CubicTenVariables.WeightedCounting
import Init.Data.Nat.Lcm

/-! The literal localized complete sums from `eq:inel-global-complete-sum`.
The two exponential factors have moduli q and lcm(q,W), respectively. The
normalization and real frequency below retain this distinction. No Poisson
identity, convergence, multiplicativity or estimate is assumed here. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial
open scoped BigOperators Classical

theorem residueExponential_add (q : ℕ) (a b : ℤ) :
    residueExponential q (a + b) =
      residueExponential q a * residueExponential q b := by
  unfold residueExponential
  rw [Int.cast_add]
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) + b) / q =
      2 * (Real.pi : ℂ) * Complex.I * a / q +
        2 * (Real.pi : ℂ) * Complex.I * b / q := by ring
  rw [he, Complex.exp_add]

/-- The manuscript's S_(q,W)(v), using canonical representatives modulo
lcm(q,W) and the actual residue restriction modulo W. -/
def localizedCompleteCubicSum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q W : ℕ) (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) : ℂ :=
  ∑ a : Fin q, if Nat.Coprime a.val q then
    ∑ x : Fin n → Fin (Nat.lcm q W),
      if integerResidue W (fun i => ((x i).val : ℤ)) ∈ Ω then
        residueExponential q ((a.val : ℤ) * eval (fun i => ((x i).val : ℤ)) F) *
          residueExponential (Nat.lcm q W) (∑ i, v i * (x i).val)
      else 0
  else 0

@[simp] theorem localizedCompleteCubicSum_zero_modulus {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) :
    localizedCompleteCubicSum F 0 W Ω v = 0 := by
  simp [localizedCompleteCubicSum]

/-- Trivial localization recovers precisely the original positive-sign
complete sum, including its normalization at modulus one. -/
@[simp] theorem localizedCompleteCubicSum_univ_one {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (q : ℕ) (v : Fin n → ℤ) :
    localizedCompleteCubicSum F q 1 Set.univ v = completeCubicSum F q v := by
  unfold localizedCompleteCubicSum
  rw [Nat.lcm_one_right]
  simp only [Set.mem_univ, if_true, ← residueExponential_add,
    completeCubicSum, completeSumPhase]

/-- The actual zero-frequency normalization after localized Poisson
summation. A subsequent analytic theorem must justify summing these terms. -/
def localizedSingularSeriesTerm {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (W : ℕ) (Ω : Set (Fin n → ZMod W)) (q : ℕ) : ℂ :=
  if q = 0 then 0 else
    localizedCompleteCubicSum F q W Ω 0 / (Nat.lcm q W : ℂ) ^ n

def localizedSingularSeries {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (W : ℕ) (Ω : Set (Fin n → ZMod W)) : ℂ :=
  ∑' q : ℕ, localizedSingularSeriesTerm F W Ω q

@[simp] theorem localizedSingularSeriesTerm_univ_one {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (q : ℕ) :
    localizedSingularSeriesTerm F 1 Set.univ q = singularSeriesTerm F q := by
  simp [localizedSingularSeriesTerm, singularSeriesTerm]

@[simp] theorem localizedSingularSeries_univ_one {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) :
    localizedSingularSeries F 1 Set.univ = singularSeries F := by
  simp [localizedSingularSeries, singularSeries]

/-- This is the frequency entering the localized oscillatory integral.
Replacing its denominator by q requires a separate comparison argument. -/
def localizedFrequency {n : ℕ} (q W : ℕ) (v : Fin n → ℤ) : Fin n → ℝ :=
  fun i => (v i : ℝ) / (Nat.lcm q W : ℝ)

@[simp] theorem localizedFrequency_one {n : ℕ} (q : ℕ) (v : Fin n → ℤ) :
    localizedFrequency q 1 v = fun i => (v i : ℝ) / (q : ℝ) := by
  unfold localizedFrequency
  rw [Nat.lcm_one_right]

end CubicTenVariables
