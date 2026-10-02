import CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplit
import TranslatedDepthSeven.Salberger2023StableQbarCurveCountInternal

/-!
# The persistent-root high-degree callback from the internal curve count

The only supplied facts about the actual cells are their root-component
certificates, logarithmic degree caps, vanishing equations and coordinate
bounds.  No coefficient-height hypothesis on an auxiliary surface is needed.
The projected-plane construction supplies its own bounded equation.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceProjectedCurveHighDegreeBridge

open MvPolynomial TranslatedDepthSeven Published Filter
open FixedLeadingSurfacePersistentRootDegreeSplit
open scoped Topology
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000

/-- The internally proved high-degree estimate supplies the existing root
callback, with constant one, above a threshold uniform in the surface,
its auxiliaries, all component degrees and all actual point sets. -/
theorem exists_eventually_internal_rootCallback
    (Cd epsilon : ℝ) (hCd : 0 ≤ Cd) (hepsilon : 0 < epsilon) :
    ∃ cutoff : ℕ, ∀ᶠ V : ℝ in atTop,
      ∀ M : ℕ, (M : ℝ) ≤ V →
      ∀ (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
        (G₀ : MvPolynomial (Fin 4) ℚ)
        (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          Finset (IntVector 3))
        (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ),
      (∀ Q ∈ finiteEquationMinimalPrimes
          (qbarSurfaceCutEquationFamily sourceEquations G₀),
        Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
        HasProjectiveDimensionDegree Q 1 (degree Q)) →
      (∀ Q, some Q ∈ activeQbarPersistentRootComponentOptions
          sourceEquations G₀ cell →
        (degree Q : ℝ) ≤ Cd * (1 + Real.log V)) →
      (∀ Q, some Q ∈ activeQbarPersistentRootComponentOptions
          sourceEquations G₀ cell →
        ∀ z ∈ cell (some Q), ∀ f ∈ Q,
          eval (fun i ↦ (integralAffineChartVector z i : Qbar)) f = 0) →
      (∀ Q, some Q ∈ activeQbarPersistentRootComponentOptions
          sourceEquations G₀ cell →
        ∀ z ∈ cell (some Q), ∀ i, (z i).natAbs ≤ M) →
      Salberger2023Theorem316PersistentRootCallback
        sourceEquations G₀ cell degree cutoff 1 epsilon V := by
  classical
  obtain ⟨cutoff, hcount⟩ :=
    exists_eventually_stableQbarCurve_count_internal 3 (by decide)
      Cd epsilon hCd hepsilon
  refine ⟨cutoff, ?_⟩
  filter_upwards [hcount, eventually_ge_atTop (1 : ℝ)] with V hcountV hV
  intro M hM sourceEquations G₀ cell degree hrootData hdegree hzero hbox
  intro Q hQactive hQhigh hQstable
  have hQoption :=
    ((mem_activeQbarPersistentRootComponentOptions_iff
      sourceEquations G₀ cell (some Q)).mp hQactive).1
  obtain ⟨Q', hQ', hsome⟩ :=
    (mem_finiteEquationComponentOptions_iff
      (qbarSurfaceCutEquationFamily sourceEquations G₀) (some Q)).mp hQoption
  have hQQ' : Q' = Q := Option.some_injective _ hsome
  have hQfamily : Q ∈ finiteEquationMinimalPrimes
      (qbarSurfaceCutEquationFamily sourceEquations G₀) := by
    simpa only [hQQ'] using hQ'
  have hQprime : Q.IsPrime := isPrime_of_mem_finiteMinimalPrimes hQfamily
  have hQdata := hrootData Q hQfamily
  have hcard := hcountV (degree Q) M hQhigh (hdegree Q hQactive) hM
    Q hQprime hQdata.1 hQdata.2 hQstable (cell (some Q))
      (hzero Q hQactive) (hbox Q hQactive)
  have hlog : 1 ≤ 1 + Real.log V := by
    have := Real.log_nonneg hV
    linarith
  have hfactor : (1 : ℝ) ≤ (1 + Real.log V) ^ (3 : ℕ) := one_le_pow₀ hlog
  refine hcard.trans ?_
  dsimp only [salberger2023Theorem316CurveError]
  rw [one_mul]
  exact le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) hfactor

end CubicTenVariables.FixedLeadingSurfaceProjectedCurveHighDegreeBridge
