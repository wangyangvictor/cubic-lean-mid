import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Normed.Group.Rat
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.Localization.Rat

/-!
# An elementary height bound for integral roots

The only arithmetic input needed for the auxiliary coordinates of a finite
relative cover is Cauchy's classical root bound.  If an integer is a root of
a monic integral polynomial, its absolute value is at most the largest
absolute value of a coefficient.  This file proves that statement directly
from Mathlib's `Polynomial.IsRoot.norm_lt_cauchyBound`.

There is no algebraic-geometric or counting assumption in this file.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset Polynomial

/-- Largest absolute value among the nonzero coefficients of an integral
polynomial. -/
def integralPolynomialCoefficientNatAbsMax (p : Polynomial ℤ) : ℕ :=
  p.support.sup fun k ↦ (p.coeff k).natAbs

theorem coeff_natAbs_le_integralPolynomialCoefficientNatAbsMax
    (p : Polynomial ℤ) (k : ℕ) :
    (p.coeff k).natAbs ≤ integralPolynomialCoefficientNatAbsMax p := by
  by_cases hk : k ∈ p.support
  · exact Finset.le_sup (f := fun j ↦ (p.coeff j).natAbs) hk
  · rw [Polynomial.notMem_support_iff.mp hk, Int.natAbs_zero]
    exact Nat.zero_le _

theorem nnnorm_intCast_rat_eq_natAbs (z : ℤ) :
    ‖(z : ℚ)‖₊ = (z.natAbs : NNReal) := by
  apply NNReal.eq
  simp [Int.norm_cast_rat, Int.norm_eq_abs]

theorem map_intCast_coeff_nnnorm_le
    (p : Polynomial ℤ) (k : ℕ) :
    ‖(p.map (Int.castRingHom ℚ)).coeff k‖₊ ≤
      integralPolynomialCoefficientNatAbsMax p := by
  rw [Polynomial.coeff_map]
  change ‖((p.coeff k : ℤ) : ℚ)‖₊ ≤
    (integralPolynomialCoefficientNatAbsMax p : NNReal)
  rw [nnnorm_intCast_rat_eq_natAbs]
  exact_mod_cast
    coeff_natAbs_le_integralPolynomialCoefficientNatAbsMax p k

theorem map_intCast_cauchyBound_le
    (p : Polynomial ℤ) (hp : p.Monic) :
    (p.map (Int.castRingHom ℚ)).cauchyBound ≤
      integralPolynomialCoefficientNatAbsMax p + 1 := by
  rw [Polynomial.cauchyBound]
  have hlead : (p.map (Int.castRingHom ℚ)).leadingCoeff = 1 :=
    (hp.map (Int.castRingHom ℚ)).leadingCoeff
  rw [hlead, nnnorm_one, div_one]
  gcongr
  apply Finset.sup_le
  intro k hk
  exact map_intCast_coeff_nnnorm_le p k

/-- Cauchy's root bound in the precise integral form used below. -/
theorem monic_integral_root_natAbs_le_coefficientMax
    (p : Polynomial ℤ) (hp : p.Monic) (r : ℤ)
    (hr : Polynomial.eval r p = 0) :
    r.natAbs ≤ integralPolynomialCoefficientNatAbsMax p := by
  let pQ : Polynomial ℚ := p.map (Int.castRingHom ℚ)
  have hpQ : pQ ≠ 0 := (hp.map (Int.castRingHom ℚ)).ne_zero
  have hrQ : pQ.IsRoot (r : ℚ) := by
    change (p.map (Int.castRingHom ℚ)).eval ((Int.castRingHom ℚ) r) = 0
    rw [Polynomial.eval_map_apply, hr]
    exact RingHom.map_zero (Int.castRingHom ℚ)
  have hroot := hrQ.norm_lt_cauchyBound hpQ
  have hbound := map_intCast_cauchyBound_le p hp
  have hlt : (r.natAbs : NNReal) <
      (integralPolynomialCoefficientNatAbsMax p + 1 : ℕ) := by
    simpa only [nnnorm_intCast_rat_eq_natAbs, Nat.cast_add, Nat.cast_one] using
      hroot.trans_le hbound
  have hnat : r.natAbs < integralPolynomialCoefficientNatAbsMax p + 1 := by
    exact_mod_cast hlt
  exact Nat.lt_succ_iff.mp (by simpa [Nat.add_comm] using hnat)

end

end TranslatedDepthSeven
