import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import TranslatedDepthSeven.JacobianCertificatePolynomialHeight

/-!
# Avoiding a nonzero integral polynomial on a bounded grid

This file extracts the deterministic existence consequence of the
Schwartz--Zippel lemma over `ℤ`: a nonzero polynomial of total degree at most
`D` cannot vanish on the whole grid `{0, ..., D}^N`.  The selected point and
the value of the polynomial at that point have literal height bounds.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset Fintype MvPolynomial

/-- The finite subset `{0, ..., D}` of `ℤ`, represented without an interval
normalization convention. -/
def nonnegativeIntegerGrid (D : ℕ) : Finset ℤ :=
  (Finset.range (D + 1)).map
    ⟨fun k : ℕ ↦ (k : ℤ), Int.ofNat_injective⟩

@[simp]
theorem card_nonnegativeIntegerGrid (D : ℕ) :
    (nonnegativeIntegerGrid D).card = D + 1 := by
  simp [nonnegativeIntegerGrid]

@[simp]
theorem mem_nonnegativeIntegerGrid_iff {D : ℕ} {z : ℤ} :
    z ∈ nonnegativeIntegerGrid D ↔ 0 ≤ z ∧ z ≤ D := by
  constructor
  · intro hz
    rw [nonnegativeIntegerGrid, Finset.mem_map] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    simp only [Finset.mem_range] at hk
    constructor
    · change 0 ≤ (k : ℤ)
      exact Int.natCast_nonneg k
    · change (k : ℤ) ≤ (D : ℤ)
      exact_mod_cast Nat.le_of_lt_succ hk
  · rintro ⟨hz0, hzD⟩
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
    rw [nonnegativeIntegerGrid, Finset.mem_map]
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (by exact_mod_cast hzD)

/-- A nonzero integral polynomial of total degree at most `D` has a nonzero
value at an integral point of the box `{0, ..., D}^N`. -/
theorem exists_nonzero_eval_on_nonnegativeIntegerGrid
    {N D : ℕ} (f : MvPolynomial (Fin N) ℤ)
    (hf : f ≠ 0) (hdegree : f.totalDegree ≤ D) :
    ∃ x : Fin N → ℤ,
      (∀ i, 0 ≤ x i ∧ x i ≤ D) ∧ MvPolynomial.eval x f ≠ 0 := by
  let S := nonnegativeIntegerGrid D
  by_contra h
  push_neg at h
  have hall : ∀ x ∈ Fintype.piFinset (fun _ : Fin N ↦ S),
      MvPolynomial.eval x f = 0 := by
    intro x hx
    apply h x
    intro i
    exact mem_nonnegativeIntegerGrid_iff.mp (Fintype.mem_piFinset.mp hx i)
  have hfilter :
      (Fintype.piFinset (fun _ : Fin N ↦ S)).filter
          (fun x ↦ MvPolynomial.eval x f = 0) =
        Fintype.piFinset (fun _ : Fin N ↦ S) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, hall x hx⟩
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hf S
  rw [hfilter, Fintype.card_piFinset, card_nonnegativeIntegerGrid] at hsz
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_pow] at hsz
  have hpos : (0 : ℚ≥0) < (D + 1 : ℕ) ^ N := by positivity
  have hone :
      (((D + 1 : ℕ) ^ N : ℚ≥0) / ((D + 1 : ℕ) ^ N : ℚ≥0)) = 1 := by
    exact div_self (ne_of_gt hpos)
  rw [hone] at hsz
  have hdegreeCast : (f.totalDegree : ℚ≥0) ≤ D := by exact_mod_cast hdegree
  have hlt : ((D : ℚ≥0) / (D + 1 : ℕ)) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast Nat.lt_succ_self D
  have hfrac :
      (f.totalDegree : ℚ≥0) / (D + 1 : ℕ) ≤
        (D : ℚ≥0) / (D + 1 : ℕ) :=
    div_le_div_of_nonneg_right hdegreeCast (by positivity)
  exact (hsz.trans hfrac).not_gt hlt

/-- Literal support, coefficient, degree and point bounds give a direct
bound for the value of an integral multivariable polynomial. -/
theorem eval_natAbs_le_support_mul_coeff_mul_pow
    {N e C Y : ℕ} (f : MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (hcoeff : ∀ m ∈ f.support, (f.coeff m).natAbs ≤ C)
    (hdegree : f.totalDegree ≤ e)
    (hy : ∀ i, (y i).natAbs ≤ Y) :
    (MvPolynomial.eval y f).natAbs ≤
      f.support.card * C * max 1 Y ^ e := by
  classical
  conv_lhs => rw [f.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  calc
    (∑ m ∈ f.support,
        f.coeff m * m.prod (fun i exponent ↦ y i ^ exponent)).natAbs ≤
        ∑ m ∈ f.support,
          (f.coeff m *
            m.prod (fun i exponent ↦ y i ^ exponent)).natAbs :=
      int_natAbs_sum_le_sum_natAbs _ _
    _ ≤ ∑ _m ∈ f.support, C * max 1 Y ^ e := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hcoeff m hm)
        (int_natAbs_finsupp_prod_pow_le y m hy
          ((MvPolynomial.le_totalDegree hm).trans hdegree))
    _ = f.support.card * C * max 1 Y ^ e := by
      simp [mul_assoc]

/-- Grid avoidance together with a literal bound for the selected nonzero
integer. -/
theorem exists_bounded_nonzero_eval_on_nonnegativeIntegerGrid
    {N D S C : ℕ} (f : MvPolynomial (Fin N) ℤ)
    (hf : f ≠ 0)
    (hdegree : f.totalDegree ≤ D)
    (hsupport : f.support.card ≤ S)
    (hcoeff : ∀ m ∈ f.support, (f.coeff m).natAbs ≤ C) :
    ∃ x : Fin N → ℤ,
      (∀ i, 0 ≤ x i ∧ x i ≤ D) ∧
      MvPolynomial.eval x f ≠ 0 ∧
      (MvPolynomial.eval x f).natAbs ≤
        S * C * max 1 D ^ D := by
  obtain ⟨x, hx, hfx⟩ :=
    exists_nonzero_eval_on_nonnegativeIntegerGrid f hf hdegree
  refine ⟨x, hx, hfx, ?_⟩
  have hy : ∀ i, (x i).natAbs ≤ D := by
    intro i
    have hcast : ((x i).natAbs : ℤ) ≤ (D : ℤ) := by
      rw [Int.natAbs_of_nonneg (hx i).1]
      exact (hx i).2
    exact_mod_cast hcast
  calc
    (MvPolynomial.eval x f).natAbs ≤
        f.support.card * C * max 1 D ^ D :=
      eval_natAbs_le_support_mul_coeff_mul_pow f x hcoeff hdegree hy
    _ ≤ S * C * max 1 D ^ D := by
      simpa [mul_assoc] using
        Nat.mul_le_mul_right (C * max 1 D ^ D) hsupport

end

end TranslatedDepthSeven
