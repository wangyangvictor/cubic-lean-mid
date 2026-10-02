import TranslatedDepthSeven.MonicIntegralRootHeight
import TranslatedDepthSeven.RelativeTriangularCoefficientHeight

/-!
# Uniform height of scaled coordinates on a finite relative cover

A finite morphism over a principal open may be presented by finitely many
affine coordinates integral over the localized base.  Multiplying those
coordinates by one fixed power of the principal-open denominator gives
integral coordinates satisfying monic equations over the original integral
base.  This file treats the resulting finite table of monic equations as
literal algebraic data and proves the required polynomial specialization
bound.

The exponent and all finite coefficient bounds below depend only on the
fixed table.  In particular they are chosen before any fibre parameter and
before any epsilon used in point counting.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset MvPolynomial Polynomial

/-- The monic integral equation obtained from a fixed table of lower
coefficient polynomials after specializing the base parameter. -/
def specializedMonicIntegralParameterRelation
    {M L D : ℕ}
    (coefficient : Fin L → Fin D → MvPolynomial (Fin M) ℤ)
    (u : Fin M → ℤ) (j : Fin L) : Polynomial ℤ :=
  Polynomial.X ^ D + ∑ k : Fin D,
    Polynomial.C (MvPolynomial.eval u (coefficient j k)) *
      Polynomial.X ^ (k : ℕ)

theorem specializedMonicIntegralParameterRelation_monic
    {M L D : ℕ}
    (coefficient : Fin L → Fin D → MvPolynomial (Fin M) ℤ)
    (u : Fin M → ℤ) (j : Fin L) :
    (specializedMonicIntegralParameterRelation coefficient u j).Monic := by
  unfold specializedMonicIntegralParameterRelation
  apply monic_X_pow_add
  exact degree_sum_fin_lt _

theorem specializedMonicIntegralParameterRelation_coeff_lt
    {M L D : ℕ}
    (coefficient : Fin L → Fin D → MvPolynomial (Fin M) ℤ)
    (u : Fin M → ℤ) (j : Fin L) (k : Fin D) :
    (specializedMonicIntegralParameterRelation coefficient u j).coeff k =
      MvPolynomial.eval u (coefficient j k) := by
  classical
  unfold specializedMonicIntegralParameterRelation
  rw [Polynomial.coeff_add]
  have hkD : (k : ℕ) ≠ D := Nat.ne_of_lt k.isLt
  rw [Polynomial.coeff_X_pow, if_neg hkD, zero_add]
  change (Polynomial.lcoeff ℤ (k : ℕ)) (∑ x : Fin D, _) = _
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

/-- Regard the fixed lower-coefficient table as one finite family of
integral polynomials on the base. -/
def monicIntegralParameterRelationCoefficientFamily
    {M L D : ℕ}
    (coefficient : Fin L → Fin D → MvPolynomial (Fin M) ℤ) :
    Fin L × Fin D → MvPolynomial (Fin M) ℤ :=
  fun jk ↦ coefficient jk.1 jk.2

/-- Literal specialization bound attached to the fixed monic-equation
table.  The `max 1` also controls the leading coefficient. -/
def monicIntegralParameterRelationSpecializationBound
    {M L D : ℕ}
    (coefficient : Fin L → Fin D → MvPolynomial (Fin M) ℤ)
    (Y : ℕ) : ℕ :=
  let f := monicIntegralParameterRelationCoefficientFamily coefficient
  max 1
    (finiteIntegralPolynomialSupportBound f *
      finiteIntegralPolynomialCoefficientBound f *
      max 1 Y ^ finiteIntegralPolynomialDegreeBound f)

/-- A fixed power of an ambient height absorbing the support and coefficient
constants of one monic-relation table. -/
def monicIntegralParameterRelationHeightExponent
    {M L D : ℕ}
    (coefficient : Fin L → Fin D → MvPolynomial (Fin M) ℤ)
    (baseCoordinateExponent : ℕ) : ℕ :=
  let f := monicIntegralParameterRelationCoefficientFamily coefficient
  finiteIntegralPolynomialSupportBound f *
      finiteIntegralPolynomialCoefficientBound f +
    baseCoordinateExponent * finiteIntegralPolynomialDegreeBound f

/-- The polynomial specialization bound is absorbed by a fixed height power.
The exponent depends only on the fixed coefficient table and the already
chosen exponent for the base coordinates. -/
theorem monicIntegralParameterRelationSpecializationBound_cast_le_heightPower
    {M L D Y baseCoordinateExponent : ℕ}
    (coefficient : Fin L → Fin D → MvPolynomial (Fin M) ℤ)
    (H : ℝ) (hH : 2 ≤ H)
    (hY : (Y : ℝ) ≤ H ^ baseCoordinateExponent) :
    (monicIntegralParameterRelationSpecializationBound coefficient Y : ℝ) ≤
      H ^ monicIntegralParameterRelationHeightExponent
        coefficient baseCoordinateExponent := by
  let f := monicIntegralParameterRelationCoefficientFamily coefficient
  let K := finiteIntegralPolynomialSupportBound f *
    finiteIntegralPolynomialCoefficientBound f
  let E := finiteIntegralPolynomialDegreeBound f
  have hKtwoNat : K ≤ 2 ^ K := by
    induction K with
    | zero => simp
    | succ K hK =>
        calc
          K + 1 ≤ 2 ^ K + 1 := Nat.add_le_add_right hK 1
          _ ≤ 2 ^ K + 2 ^ K :=
            Nat.add_le_add_left Nat.one_le_two_pow (2 ^ K)
          _ = 2 ^ (K + 1) := by rw [pow_succ]; omega
  have hKtwo : (K : ℝ) ≤ (2 : ℝ) ^ K := by exact_mod_cast hKtwoNat
  have hK : (K : ℝ) ≤ H ^ K :=
    hKtwo.trans (pow_le_pow_left₀ (by norm_num) hH K)
  have honeH : (1 : ℝ) ≤ H := by linarith
  have honePower : (1 : ℝ) ≤ H ^ baseCoordinateExponent :=
    one_le_pow₀ honeH
  have hmaxY : ((max 1 Y : ℕ) : ℝ) ≤ H ^ baseCoordinateExponent := by
    norm_num only [Nat.cast_max, Nat.cast_one]
    exact max_le honePower hY
  have hproduct :
      (K : ℝ) * (((max 1 Y : ℕ) : ℝ) ^ E) ≤
        H ^ (K + baseCoordinateExponent * E) := by
    calc
      (K : ℝ) * (((max 1 Y : ℕ) : ℝ) ^ E) ≤
          H ^ K * (H ^ baseCoordinateExponent) ^ E := by
        exact mul_le_mul hK
          (pow_le_pow_left₀ (by positivity) hmaxY E)
          (by positivity) (by positivity)
      _ = H ^ (K + baseCoordinateExponent * E) := by ring
  have honeTarget : (1 : ℝ) ≤
      H ^ (K + baseCoordinateExponent * E) := one_le_pow₀ honeH
  change ((max 1 (K * max 1 Y ^ E) : ℕ) : ℝ) ≤
    H ^ (K + baseCoordinateExponent * E)
  norm_num only [Nat.cast_max, Nat.cast_one, Nat.cast_mul, Nat.cast_pow]
  exact max_le honeTarget
    (by simpa only [Nat.cast_max, Nat.cast_one] using hproduct)

theorem specializedMonicIntegralParameterRelation_coeff_natAbs_le
    {M L D Y : ℕ}
    (coefficient : Fin L → Fin D → MvPolynomial (Fin M) ℤ)
    (u : Fin M → ℤ) (hu : ∀ i, (u i).natAbs ≤ Y)
    (j : Fin L) (k : ℕ) :
    ((specializedMonicIntegralParameterRelation coefficient u j).coeff k).natAbs ≤
      monicIntegralParameterRelationSpecializationBound coefficient Y := by
  classical
  let f := monicIntegralParameterRelationCoefficientFamily coefficient
  let B := finiteIntegralPolynomialSupportBound f *
    finiteIntegralPolynomialCoefficientBound f *
    max 1 Y ^ finiteIntegralPolynomialDegreeBound f
  by_cases hkD : k < D
  · let kD : Fin D := ⟨k, hkD⟩
    have heval : (MvPolynomial.eval u (coefficient j kD)).natAbs ≤ B := by
      simpa only [f, B, monicIntegralParameterRelationCoefficientFamily] using
        finiteIntegralPolynomialFamily_eval_natAbs_le f u hu (j, kD)
    rw [← specializedMonicIntegralParameterRelation_coeff_lt
      coefficient u j kD] at heval
    exact heval.trans (Nat.le_max_right 1 B)
  · have hDk : D ≤ k := Nat.le_of_not_gt hkD
    by_cases hEq : k = D
    · have hmonic := specializedMonicIntegralParameterRelation_monic
        coefficient u j
      have hdegree :
          (specializedMonicIntegralParameterRelation coefficient u j).natDegree = D := by
        apply le_antisymm
        · apply natDegree_le_of_degree_le
          unfold specializedMonicIntegralParameterRelation
          exact (degree_add_le _ _).trans (max_le (degree_X_pow_le D)
            (le_of_lt (degree_sum_fin_lt _)))
        · have hcoeffD :
              (specializedMonicIntegralParameterRelation coefficient u j).coeff D = 1 := by
            unfold specializedMonicIntegralParameterRelation
            rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
              Polynomial.coeff_eq_zero_of_degree_lt (degree_sum_fin_lt _), add_zero]
          exact le_natDegree_of_ne_zero (by simpa [hcoeffD])
      have hcoeff :
          (specializedMonicIntegralParameterRelation coefficient u j).coeff k = 1 := by
        calc
          _ = (specializedMonicIntegralParameterRelation coefficient u j).coeff D :=
            congrArg
              (specializedMonicIntegralParameterRelation coefficient u j).coeff hEq
          _ = (specializedMonicIntegralParameterRelation coefficient u j).coeff
                (specializedMonicIntegralParameterRelation coefficient u j).natDegree :=
            congrArg
              (specializedMonicIntegralParameterRelation coefficient u j).coeff
              hdegree.symm
          _ = 1 := hmonic.coeff_natDegree
      rw [hcoeff, Int.natAbs_one]
      exact Nat.le_max_left 1 B
    · have hDlt : D < k := lt_of_le_of_ne hDk (Ne.symm hEq)
      have hdegree :
          (specializedMonicIntegralParameterRelation coefficient u j).degree ≤ D := by
        unfold specializedMonicIntegralParameterRelation
        exact (degree_add_le _ _).trans (max_le (degree_X_pow_le D)
          (le_of_lt (degree_sum_fin_lt _)))
      rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_le_of_lt hdegree (by exact_mod_cast hDlt)), Int.natAbs_zero]
      exact Nat.zero_le _

/-- Every integral specialization of the fixed monic-equation table has a
single polynomial root bound. -/
theorem specializedMonicIntegralParameterRelation_root_natAbs_le
    {M L D Y : ℕ}
    (coefficient : Fin L → Fin D → MvPolynomial (Fin M) ℤ)
    (u : Fin M → ℤ) (hu : ∀ i, (u i).natAbs ≤ Y)
    (j : Fin L) (root : ℤ)
    (hroot : Polynomial.eval root
      (specializedMonicIntegralParameterRelation coefficient u j) = 0) :
    root.natAbs ≤
      monicIntegralParameterRelationSpecializationBound coefficient Y := by
  refine (monic_integral_root_natAbs_le_coefficientMax
    (specializedMonicIntegralParameterRelation coefficient u j)
    (specializedMonicIntegralParameterRelation_monic coefficient u j)
    root hroot).trans ?_
  apply Finset.sup_le
  intro k hk
  exact specializedMonicIntegralParameterRelation_coeff_natAbs_le
    coefficient u hu j k

end

end TranslatedDepthSeven
