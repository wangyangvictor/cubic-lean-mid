import CubicTenVariables.LocalPolynomialAvoidance
import CubicTenVariables.RationalHessianMinor
import CubicTenVariables.Literature.Pleasants
import HessianTheorem11.RationalIrreducibility

/-! Actual smooth local zeros with Hessian rank at least eight.

The high-rank selection is proved from a supplied smooth local point. It
uses a rational Hessian minor, a constructed elimination identity, and an
actual implicit-function patch. No local-density, geometric-integrality
transfer, or polynomial-avoidance assertion is assumed. The final p-adic
existence corollary retains precisely the explicit Pleasants input.
-/

noncomputable section
namespace CubicTenVariables.HighRankLocalPoint
open MvPolynomial HessianTheorem11

/-- Every neighborhood of a nonzero smooth local zero contains a nonzero
smooth zero at which the actual Hessian has rank at least eight. -/
theorem exists_high_rank_zero_mem_open
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [Algebra ℚ K]
    (F : AnisotropicCubic 10) (x : Fin 10 → K) (hx : x ≠ 0)
    (hFx : eval₂ (algebraMap ℚ K) x F.polynomial = 0)
    (i : Fin 10) (hi : eval₂ (algebraMap ℚ K) x (pderiv i F.polynomial) ≠ 0)
    (U : Set (Fin 10 → K)) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ y : Fin 10 → K, y ≠ 0 ∧ y ∈ U ∧
      eval₂ (algebraMap ℚ K) y F.polynomial = 0 ∧
      (∃ j : Fin 10, eval₂ (algebraMap ℚ K) y (pderiv j F.polynomial) ≠ 0) ∧
      8 ≤ (hessian (map (algebraMap ℚ K) F.polynomial) y).rank := by
  obtain ⟨r, rows, cols, _, hnotdiv, hdetect⟩ :=
    RationalHessianMinor.exists_rational_hessian_minor F
  obtain ⟨y, hy, hFy, hiy, hDy⟩ :=
    LocalPolynomialAvoidance.exists_zero_avoiding_rational_polynomial (m := 9)
      F.polynomial (RationalHessianMinor.hessianMinor F.polynomial rows cols)
      (anisotropic_cubic_irreducible F (by omega)) hnotdiv i x hFx hi
      (U \ {0}) (hU.sdiff isClosed_singleton) ⟨hxU, hx⟩
  exact ⟨y, hy.2, hy.1, hFy, ⟨i, hiy⟩, hdetect K y hDy⟩

/-- Pleasants supplies the initial smooth p-adic zero; the rank-eight
selection is the preceding internal proof. All primes are included. -/
theorem padic_high_rank_zero
    (pleasants : Literature.Pleasants1971Theorem2Qp)
    (F : AnisotropicCubic 10) (p : ℕ) [Fact p.Prime] :
    ∃ y : Fin 10 → ℚ_[p], y ≠ 0 ∧
      eval₂ (algebraMap ℚ ℚ_[p]) y F.polynomial = 0 ∧
      (∃ j : Fin 10, eval₂ (algebraMap ℚ ℚ_[p]) y (pderiv j F.polynomial) ≠ 0) ∧
      8 ≤ (hessian (map (algebraMap ℚ ℚ_[p]) F.polynomial) y).rank := by
  obtain ⟨x, hx, hFx, i, hi⟩ :=
    Literature.padic_eval₂_nonsingular_zero_of_pleasants pleasants F (by omega) p
  obtain ⟨y, hy, _, hFy, hgy, hry⟩ :=
    exists_high_rank_zero_mem_open F x hx hFx i hi Set.univ isOpen_univ (Set.mem_univ _)
  exact ⟨y, hy, hFy, hgy, hry⟩

end CubicTenVariables.HighRankLocalPoint
