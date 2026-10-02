import CubicTenVariables.FixedLeadingSurfaceLogarithmicNumerics
import TranslatedDepthSeven.QuantitativePrefixPersistentDegreeBound

/-!
# Logarithmic bounds for degrees of actual persistent curves

The terminal auxiliary degree is logarithmic even though the root auxiliary
degree is larger.  Persistence and the internal proper-section degree bound
transfer that terminal bound to the already certified root-component degree.
The constant below is independent of the curve, the lower coefficients, and
the height.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceLogarithmicPersistentDegree

open MvPolynomial TranslatedDepthSeven Published
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Convert the integer terminal Bezout cap into the uniform logarithmic
degree hypothesis used by the projected-plane curve count. -/
theorem degree_le_log_volume_of_terminalCap
    {δ d b H : ℕ} {L V : ℝ}
    (hL : 0 ≤ L) (hH : 1 ≤ H) (hHV : (H : ℝ) ≤ V)
    (hdegree : δ ≤ d * (b + ⌈4 * L * Real.log (H : ℝ)⌉₊)) :
    (δ : ℝ) ≤ (d : ℝ) * ((b : ℝ) + 1 + 4 * L) *
      (1 + Real.log V) := by
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlogH : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg hHreal
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg (hHreal.trans hHV)
  have hlogHV : Real.log (H : ℝ) ≤ Real.log V :=
    Real.log_le_log (by linarith) hHV
  have hceil : (⌈4 * L * Real.log (H : ℝ)⌉₊ : ℝ) ≤
      4 * L * Real.log (H : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hcap : (b : ℝ) + (⌈4 * L * Real.log (H : ℝ)⌉₊ : ℝ) ≤
      ((b : ℝ) + 1 + 4 * L) * (1 + Real.log V) := by
    have hprod := mul_le_mul_of_nonneg_left hlogHV
      (show 0 ≤ 4 * L by positivity)
    have hblog : 0 ≤ ((b : ℝ) + 1) * Real.log V := by positivity
    nlinarith
  have hdegreeReal : (δ : ℝ) ≤
      (d : ℝ) * ((b : ℝ) + (⌈4 * L * Real.log (H : ℝ)⌉₊ : ℝ)) := by
    exact_mod_cast hdegree
  calc
    (δ : ℝ) ≤ (d : ℝ) *
        ((b : ℝ) + (⌈4 * L * Real.log (H : ℝ)⌉₊ : ℝ)) := hdegreeReal
    _ ≤ (d : ℝ) * (((b : ℝ) + 1 + 4 * L) * (1 + Real.log V)) :=
      mul_le_mul_of_nonneg_left hcap (by positivity)
    _ = _ := by ring

/-- Apply the logarithmic degree bound to a nonempty cell of the actual
prefix partition, using its terminal auxiliary rather than its root cut. -/
theorem quantitativePrefixPersistent_degree_le_log_volume
    {d b H : ℕ} {L V : ℝ}
    (hL : 0 ≤ L) (hH : 1 ≤ H) (hHV : (H : ℝ) ≤ V)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    {P : Finset ℕ} {depth : ℕ}
    (u : IntVector 3) (m : ℕ) (X : Finset (IntVector 3))
    (allowed : IntVector 3 → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hallowed : ∀ z ∈ X, allowed z ⊆ P)
    (hroom : ∀ z ∈ X, depth ≤ (allowed z).card)
    (hauxiliary : ∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
      (auxiliary v (integralResidueVector z)).IsHomogeneous
          (b + blockDegree v) ∧
        auxiliary v (integralResidueVector z) ∉
          finiteEquationIdeal sourceEquations)
    (hterminal : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      v.1.card = depth →
        b + blockDegree v ≤ b + ⌈4 * L * Real.log (H : ℝ)⌉₊)
    (Q : Ideal (MvPolynomial (Fin 4) Qbar)) (δ : ℕ)
    (hQprime : Q.IsPrime)
    (hQhom : Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar))
    (hQdegree : HasProjectiveDimensionDegree Q 1 δ)
    (hcell : (quantitativePrefixPersistentCell sourceEquations auxiliary
      u m X allowed (some Q)).Nonempty) :
    (δ : ℝ) ≤ (d : ℝ) * ((b : ℝ) + 1 + 4 * L) *
      (1 + Real.log V) := by
  exact degree_le_log_volume_of_terminalCap hL hH hHV
    (quantitativePrefixPersistent_degree_le_terminalCap sourceEquations
      hgeometricPrime hdegree u m X allowed blockDegree auxiliary
      hallowed hroom hauxiliary hterminal Q δ hQprime hQhom hQdegree hcell)

end CubicTenVariables.FixedLeadingSurfaceLogarithmicPersistentDegree
