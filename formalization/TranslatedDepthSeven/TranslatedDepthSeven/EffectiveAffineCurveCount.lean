import TranslatedDepthSeven.RationalQbarPrimePila
import TranslatedDepthSeven.PilaSubpower

/-!
# Effective integral-point counting for rational affine curves

This file records the degree-effective curve estimate which is needed when
the degree of a determinant-method auxiliary form is allowed to grow with
the height.  The older `Pila1995TheoremA` interface is coefficient-uniform
for each *fixed* degree, but does not control its constant as the degree
varies.

The external proposition below is the real-height reformulation of
Cluckers--Dèbes--Hendel--Nguyen--Vermeulen, *Forum Math. Sigma* 13 (2025),
Corollary 2.2 (itself citing Castryck--Cluckers--Dittmann--Nguyen,
Theorem 3): for an irreducible affine curve of degree `d` in `A^N_Q`,

`N_aff(C,B) \ll_N d^3 B^(1/d) (log B + d)`.

Passing from integer `B >= 1` and the closed box to real `H > 1` and the
strict box only uses the ceiling of `H` and changes the ambient constant.
The ideal predicate below literally includes irreducibility over `Q`, the
affine dimension, and the ordinary Hilbert degree.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

namespace Published

/-- **CDHNV 2025, Corollary 2.2, real-height ideal form.**

The constant depends only on the ambient affine dimension `N`; in
particular it is chosen before the degree, the rational prime ideal, and
the height. -/
def CDHNV2025Corollary22 : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
      HasAffineHilbertDimensionDegree I 1 d →
      ∀ H : ℝ, 1 < H →
        ((rationalPilaIntegralPoints I H).card : ℝ) ≤
          c * (d : ℝ) ^ (3 : ℕ) * H ^ ((d : ℝ)⁻¹) *
            (Real.log H + (d : ℝ))

/-- Literal specialization of the effective affine-curve theorem. -/
theorem cDHNV2025_corollary22_apply
    (hCurve : CDHNV2025Corollary22)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
        HasAffineHilbertDimensionDegree I 1 d →
        ∀ H : ℝ, 1 < H →
          ((rationalPilaIntegralPoints I H).card : ℝ) ≤
            c * (d : ℝ) ^ (3 : ℕ) * H ^ ((d : ℝ)⁻¹) *
              (Real.log H + (d : ℝ)) :=
  hCurve N hN

end Published

open Published

/-- For nonlinear curves, the effective printed estimate is bounded by a
square-root power while retaining its explicit polynomial degree factor.
No bounded-degree maximum is taken. -/
theorem cDHNV2025_curve_halfPower
    (hCurve : Published.CDHNV2025Corollary22)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ), 2 ≤ d →
        ∀ (I : Ideal (MvPolynomial (Fin N) ℚ)),
          HasAffineHilbertDimensionDegree I 1 d →
          ∀ H : ℝ, 1 < H →
            ((rationalPilaIntegralPoints I H).card : ℝ) ≤
              c * (d : ℝ) ^ (3 : ℕ) * H ^ (1 / 2 : ℝ) *
                (Real.log H + (d : ℝ)) := by
  obtain ⟨c, hc, hsource⟩ := hCurve N hN
  refine ⟨c, hc, ?_⟩
  intro d hd I hI H hH
  have hprinted := hsource d I hI H hH
  have hpower : H ^ ((d : ℝ)⁻¹) ≤ H ^ (1 / 2 : ℝ) :=
    curveDegree_rpow_le_half hd hH.le
  have hdegree : 0 ≤ (d : ℝ) ^ (3 : ℕ) := by positivity
  have hlogdegree : 0 ≤ Real.log H + (d : ℝ) := by
    have hlog : 0 ≤ Real.log H := Real.log_nonneg hH.le
    positivity
  calc
    ((rationalPilaIntegralPoints I H).card : ℝ) ≤
        c * (d : ℝ) ^ (3 : ℕ) * H ^ ((d : ℝ)⁻¹) *
          (Real.log H + (d : ℝ)) := hprinted
    _ ≤ c * (d : ℝ) ^ (3 : ℕ) * H ^ (1 / 2 : ℝ) *
          (Real.log H + (d : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower (mul_nonneg hc.le hdegree))
        hlogdegree

end

end TranslatedDepthSeven
