import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Universal formal implicit-function input. This is the standard lifting
property at a simple root, for arbitrary polynomial equations and arbitrary
prescribed formal arcs in the other coordinates. No cubic, Hessian, matrix
identity, or numerical target appears in this input. -/

namespace HessianTheorem11
open MvPolynomial

structure FormalImplicitFunctionInput (K : Type) [Field K] : Prop where
  lift : ∀ {σ : Type} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial σ K) (j : σ) (u : σ → PowerSeries K),
    u j = 0 →
    eval (fun i => PowerSeries.constantCoeff (u i)) P = 0 →
    eval (fun i => PowerSeries.constantCoeff (u i)) (pderiv j P) ≠ 0 →
    ∃ z : PowerSeries K, PowerSeries.constantCoeff z = 0 ∧
      eval₂ PowerSeries.C (Function.update u j z) P = 0

end HessianTheorem11
