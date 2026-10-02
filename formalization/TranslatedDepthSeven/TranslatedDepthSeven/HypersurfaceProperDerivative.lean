import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.Ideal.Span

/-!
# A proper derivative section and an affine nonzero derivative

These elementary consequences of Euler's identity permit use of an ordinary
affine birational projection. The singular image points lie on one proper
derivative section; no projection adapted to a specified smooth point is
needed. The remaining image points have a nonzero affine partial derivative.

The proper derivative section is the same device used for singular points
in Heath-Brown, Annals of Mathematics 155 (2002), proof of Theorem 14.
-/

namespace TranslatedDepthSeven

open MvPolynomial
open scoped BigOperators

theorem exists_nonzero_partial_of_positive_homogeneous
    {N e : ℕ} (G : MvPolynomial (Fin N) ℚ)
    (hG : G ≠ 0) (hhom : G.IsHomogeneous e) (he : 0 < e) :
    ∃ j, MvPolynomial.pderiv j G ≠ 0 := by
  classical
  by_contra! hz
  have heuler := hhom.sum_X_mul_pderiv
  have hcast : (e : MvPolynomial (Fin N) ℚ) ≠ 0 := by
    intro hzcast
    have hq : (e : ℚ) = 0 := by
      simpa using congrArg (MvPolynomial.eval (fun _ : Fin N ↦ (0 : ℚ))) hzcast
    exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt he) : (e : ℚ) ≠ 0) hq
  have hmul : (e : MvPolynomial (Fin N) ℚ) * G = 0 := by
    simpa [hz, nsmul_eq_mul] using heuler.symm
  exact mul_ne_zero hcast hG hmul

/-- A nonzero partial derivative has smaller degree than the equation and
therefore cannot belong to its principal ideal. -/
theorem partial_not_mem_span_of_nonzero
    {N e : ℕ} (G : MvPolynomial (Fin N) ℚ)
    (hG : G ≠ 0) (hhom : G.IsHomogeneous e) (he : 0 < e)
    (j : Fin N) (hj : MvPolynomial.pderiv j G ≠ 0) :
    MvPolynomial.pderiv j G ∉ Ideal.span {G} := by
  intro hmem
  have hdeg := MvPolynomial.totalDegree_le_of_dvd_of_isDomain
    (Ideal.mem_span_singleton.mp hmem) hj
  rw [hhom.totalDegree hG, hhom.pderiv.totalDegree hj] at hdeg
  omega

theorem exists_proper_partial_of_positive_homogeneous
    {N e : ℕ} (G : MvPolynomial (Fin N) ℚ)
    (hG : G ≠ 0) (hhom : G.IsHomogeneous e) (he : 0 < e) :
    ∃ j, MvPolynomial.pderiv j G ≠ 0 ∧
      MvPolynomial.pderiv j G ∉ Ideal.span {G} := by
  obtain ⟨j, hj⟩ := exists_nonzero_partial_of_positive_homogeneous G hG hhom he
  exact ⟨j, hj, partial_not_mem_span_of_nonzero G hG hhom he j hj⟩

/-- On the chart `x₀ = 1`, a nonzero projective gradient at a zero of a
homogeneous equation supplies a nonzero spatial partial derivative.
There is no division by the degree, so this statement holds in every
characteristic. -/
theorem exists_nonzero_affine_partial_of_homogeneous_gradient
    {K : Type*} [CommRing K] {N e : ℕ}
    (G : MvPolynomial (Fin (N + 1)) K) (hhom : G.IsHomogeneous e)
    (y : Fin (N + 1) → K) (hy0 : y 0 = 1)
    (hzero : MvPolynomial.eval y G = 0)
    (hgradient : ∃ j, MvPolynomial.eval y (MvPolynomial.pderiv j G) ≠ 0) :
    ∃ j : Fin N, MvPolynomial.eval y (MvPolynomial.pderiv j.succ G) ≠ 0 := by
  classical
  by_contra! hz
  have heuler := congrArg (MvPolynomial.eval y) hhom.sum_X_mul_pderiv
  have hfirst : MvPolynomial.eval y (MvPolynomial.pderiv 0 G) = 0 := by
    simpa [Fin.sum_univ_succ, hy0, hz, hzero] using heuler
  obtain ⟨j, hj⟩ := hgradient
  refine hj ?_
  exact Fin.cases hfirst hz j

end TranslatedDepthSeven
