import TranslatedDepthSeven.CharacteristicPolynomialHeight
import Mathlib.Data.Rat.Lemmas

/-!
# Height bounds after specializing denominator-cleared triangular data

The geometric spreading argument ends with finite, completely explicit
data: one nonzero integral polynomial on the parameter space and finitely
many integral numerator polynomials.  On the principal open where the first
polynomial does not vanish, the coefficients of the resulting monic
relations are quotients of their specialized values.

This file proves the remaining height assertion.  It contains no
elimination theory and no algebraic-geometric compactness principle.  In
particular, the only input is the literal finite list of numerator and
denominator polynomials.  Its output is one support bound, one coefficient
bound, and one degree bound, independent of the specialization.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset MvPolynomial Polynomial

/-- Naive multiplicative height of a rational number. -/
def rationalCoefficientHeight (q : ℚ) : ℕ :=
  max q.num.natAbs q.den

/-- Reducing an integral quotient can only decrease both numerator and
denominator. -/
theorem rationalCoefficientHeight_int_div_int_le
    (a b : ℤ) (hb : b ≠ 0) :
    rationalCoefficientHeight ((a : ℚ) / (b : ℚ)) ≤
      max a.natAbs b.natAbs := by
  let q : ℚ := (a : ℚ) / (b : ℚ)
  obtain ⟨c, hac, hbc⟩ :=
    Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hb
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at hbc
    exact hb hbc
  have hnum : q.num.natAbs ≤ a.natAbs := by
    calc
      q.num.natAbs ≤ c.natAbs * q.num.natAbs :=
        Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hc)
      _ = a.natAbs := by rw [hac, Int.natAbs_mul]
  have hden : q.den ≤ b.natAbs := by
    calc
      q.den ≤ c.natAbs * q.den :=
        Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hc)
      _ = b.natAbs := by
        rw [hbc, Int.natAbs_mul, Int.natAbs_natCast]
  change rationalCoefficientHeight q ≤ _
  exact max_le (hnum.trans (Nat.le_max_left _ _))
    (hden.trans (Nat.le_max_right _ _))

/-- The largest support cardinality in a literal finite family of integral
parameter polynomials. -/
def finiteIntegralPolynomialSupportBound
    {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℤ) : ℕ :=
  Finset.univ.sup fun i ↦ (f i).support.card

/-- The largest coefficient absolute value in a literal finite family. -/
def finiteIntegralPolynomialCoefficientBound
    {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℤ) : ℕ :=
  Finset.univ.sup fun i ↦ mvPolynomialCoefficientNatAbsMax (f i)

/-- The largest total degree in a literal finite family. -/
def finiteIntegralPolynomialDegreeBound
    {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℤ) : ℕ :=
  Finset.univ.sup fun i ↦ (f i).totalDegree

theorem support_card_le_finiteIntegralPolynomialSupportBound
    {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℤ) (i : ι) :
    (f i).support.card ≤ finiteIntegralPolynomialSupportBound f := by
  classical
  exact Finset.le_sup (s := Finset.univ)
    (f := fun j ↦ (f j).support.card) (Finset.mem_univ i)

theorem coefficientMax_le_finiteIntegralPolynomialCoefficientBound
    {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℤ) (i : ι) :
    mvPolynomialCoefficientNatAbsMax (f i) ≤
      finiteIntegralPolynomialCoefficientBound f := by
  classical
  exact Finset.le_sup (s := Finset.univ)
    (f := fun j ↦ mvPolynomialCoefficientNatAbsMax (f j))
    (Finset.mem_univ i)

theorem totalDegree_le_finiteIntegralPolynomialDegreeBound
    {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ ℤ) (i : ι) :
    (f i).totalDegree ≤ finiteIntegralPolynomialDegreeBound f := by
  classical
  exact Finset.le_sup (s := Finset.univ)
    (f := fun j ↦ (f j).totalDegree) (Finset.mem_univ i)

/-- A finite family of fixed integral parameter polynomials has one literal
polynomial evaluation bound, uniform in the member of the family and in the
integral specialization. -/
theorem finiteIntegralPolynomialFamily_eval_natAbs_le
    {ι σ : Type*} [Fintype ι] {H : ℕ}
    (f : ι → MvPolynomial σ ℤ)
    (u : σ → ℤ) (hu : ∀ j, (u j).natAbs ≤ H) (i : ι) :
    (MvPolynomial.eval u (f i)).natAbs ≤
      finiteIntegralPolynomialSupportBound f *
        finiteIntegralPolynomialCoefficientBound f *
        max 1 H ^ finiteIntegralPolynomialDegreeBound f := by
  let S := finiteIntegralPolynomialSupportBound f
  let C := finiteIntegralPolynomialCoefficientBound f
  let E := finiteIntegralPolynomialDegreeBound f
  have hbase : 1 ≤ max 1 H := Nat.le_max_left 1 H
  calc
    (MvPolynomial.eval u (f i)).natAbs ≤
        (f i).support.card * mvPolynomialCoefficientNatAbsMax (f i) *
          max 1 H ^ (f i).totalDegree :=
      eval_natAbs_le_support_mul_coeff_mul_pow_generic (f i) u
        (fun _m hm ↦ coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax
          (f i) hm) le_rfl hu
    _ ≤ S * C * max 1 H ^ E := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul
          (support_card_le_finiteIntegralPolynomialSupportBound f i)
          (coefficientMax_le_finiteIntegralPolynomialCoefficientBound f i))
        (Nat.pow_le_pow_right hbase
          (totalDegree_le_finiteIntegralPolynomialDegreeBound f i))
    _ = finiteIntegralPolynomialSupportBound f *
        finiteIntegralPolynomialCoefficientBound f *
        max 1 H ^ finiteIntegralPolynomialDegreeBound f := rfl

/-- Put one denominator and all numerator polynomials in a single literal
finite family.  This is convenient because the same three complexity bounds
then control both parts of every specialized coefficient. -/
def denominatorClearedCoefficientPolynomials
    {M N D : ℕ}
    (denominator : MvPolynomial (Fin M) ℤ)
    (numerator : Fin N → Fin D → MvPolynomial (Fin M) ℤ) :
    Option (Fin N × Fin D) → MvPolynomial (Fin M) ℤ
  | none => denominator
  | some ik => numerator ik.1 ik.2

/-- The monic relation obtained by specializing a table of integral
numerators with one common denominator.  All lower coefficients have degree
strictly less than `D`. -/
def specializedDenominatorClearedMonicRelation
    {M N D : ℕ}
    (denominator : MvPolynomial (Fin M) ℤ)
    (numerator : Fin N → Fin D → MvPolynomial (Fin M) ℤ)
    (u : Fin M → ℤ) (i : Fin N) : ℚ[X] :=
  Polynomial.X ^ D + ∑ k : Fin D,
    Polynomial.C (((MvPolynomial.eval u (numerator i k) : ℤ) : ℚ) /
      ((MvPolynomial.eval u denominator : ℤ) : ℚ)) *
        Polynomial.X ^ (k : ℕ)

theorem specializedDenominatorClearedMonicRelation_monic
    {M N D : ℕ}
    (denominator : MvPolynomial (Fin M) ℤ)
    (numerator : Fin N → Fin D → MvPolynomial (Fin M) ℤ)
    (u : Fin M → ℤ) (i : Fin N) :
    (specializedDenominatorClearedMonicRelation
      denominator numerator u i).Monic := by
  unfold specializedDenominatorClearedMonicRelation
  apply monic_X_pow_add
  exact degree_sum_fin_lt _

theorem specializedDenominatorClearedMonicRelation_coeff
    {M N D : ℕ}
    (denominator : MvPolynomial (Fin M) ℤ)
    (numerator : Fin N → Fin D → MvPolynomial (Fin M) ℤ)
    (u : Fin M → ℤ) (i : Fin N) (k : Fin D) :
    (specializedDenominatorClearedMonicRelation
      denominator numerator u i).coeff k =
      ((MvPolynomial.eval u (numerator i k) : ℤ) : ℚ) /
        ((MvPolynomial.eval u denominator : ℤ) : ℚ) := by
  classical
  unfold specializedDenominatorClearedMonicRelation
  rw [Polynomial.coeff_add]
  have hkD : (k : ℕ) ≠ D := Nat.ne_of_lt k.isLt
  rw [Polynomial.coeff_X_pow, if_neg hkD, zero_add]
  change (Polynomial.lcoeff ℚ (k : ℕ)) (∑ x : Fin D, _) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro x _hx hxk
    have hne : (k : ℕ) ≠ (x : ℕ) := by
      intro h
      exact hxk (Fin.ext h.symm)
    simp [hne]
  · simp

/-- **Uniform specialization-height bridge.**  Once a relative triangular
presentation has been written using one integral denominator and a finite
table of integral numerator polynomials, every lower coefficient of every
specialized monic relation has a single polynomial height bound.  The three
constants in the bound are computed directly from that displayed finite
table. -/
theorem specializedDenominatorClearedMonicRelation_coeff_height_le
    {M N D H : ℕ}
    (denominator : MvPolynomial (Fin M) ℤ)
    (numerator : Fin N → Fin D → MvPolynomial (Fin M) ℤ)
    (u : Fin M → ℤ) (hu : ∀ j, (u j).natAbs ≤ H)
    (hdenominator : MvPolynomial.eval u denominator ≠ 0)
    (i : Fin N) (k : Fin D) :
    rationalCoefficientHeight
        ((specializedDenominatorClearedMonicRelation
          denominator numerator u i).coeff k) ≤
      let f := denominatorClearedCoefficientPolynomials denominator numerator
      finiteIntegralPolynomialSupportBound f *
        finiteIntegralPolynomialCoefficientBound f *
        max 1 H ^ finiteIntegralPolynomialDegreeBound f := by
  let f := denominatorClearedCoefficientPolynomials denominator numerator
  let B := finiteIntegralPolynomialSupportBound f *
    finiteIntegralPolynomialCoefficientBound f *
    max 1 H ^ finiteIntegralPolynomialDegreeBound f
  have hnum : (MvPolynomial.eval u (numerator i k)).natAbs ≤ B := by
    simpa only [f, B, denominatorClearedCoefficientPolynomials] using
      (finiteIntegralPolynomialFamily_eval_natAbs_le f u hu
        (some (i, k)))
  have hden : (MvPolynomial.eval u denominator).natAbs ≤ B := by
    simpa only [f, B, denominatorClearedCoefficientPolynomials] using
      (finiteIntegralPolynomialFamily_eval_natAbs_le f u hu none)
  rw [specializedDenominatorClearedMonicRelation_coeff]
  refine (rationalCoefficientHeight_int_div_int_le
    (MvPolynomial.eval u (numerator i k))
    (MvPolynomial.eval u denominator) hdenominator).trans ?_
  exact max_le hnum hden

end

end TranslatedDepthSeven
