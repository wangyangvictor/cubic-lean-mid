import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Field.ZMod

/-!
# A literal finite-field Schwartz--Zippel count

This file specializes Mathlib's Schwartz--Zippel inequality to the full
affine space over `ZMod p` and records it as a cardinality estimate for a
literal `Finset` of zeros.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset

/-- The literal zero set of a multivariable polynomial on the full affine
space `(ZMod p)^N`. -/
def mvPolynomialZeroSet (p N : ℕ) (hp : p.Prime)
    (f : MvPolynomial (Fin N) (ZMod p)) :
    Finset (Fin N → ZMod p) :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  Finset.univ.filter fun x ↦ MvPolynomial.eval x f = 0

@[simp]
theorem mem_mvPolynomialZeroSet_iff
    {p N : ℕ} (hp : p.Prime) (f : MvPolynomial (Fin N) (ZMod p))
    (x : Fin N → ZMod p) :
    x ∈ mvPolynomialZeroSet p N hp f ↔ MvPolynomial.eval x f = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  simp [mvPolynomialZeroSet]

/-- The literal common zero set of a finite family of polynomials on the
full affine space `(ZMod p)^N`.  In particular, the empty family has the
whole affine space as its common zero set. -/
def mvPolynomialCommonZeroSet (p N : ℕ) (hp : p.Prime)
    (family : Finset (MvPolynomial (Fin N) (ZMod p))) :
    Finset (Fin N → ZMod p) :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  Finset.univ.filter fun x ↦
    ∀ f ∈ family, MvPolynomial.eval x f = 0

@[simp]
theorem mem_mvPolynomialCommonZeroSet_iff
    {p N : ℕ} (hp : p.Prime)
    (family : Finset (MvPolynomial (Fin N) (ZMod p)))
    (x : Fin N → ZMod p) :
    x ∈ mvPolynomialCommonZeroSet p N hp family ↔
      ∀ f ∈ family, MvPolynomial.eval x f = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  simp [mvPolynomialCommonZeroSet]

/-- Mathlib's probability inequality, specialized to all elements of the
prime field `ZMod p`. -/
theorem mvPolynomialZeroSet_ratio_le_totalDegree_div
    {p N : ℕ} (hp : p.Prime) (f : MvPolynomial (Fin N) (ZMod p))
    (hf : f ≠ 0) :
    ((mvPolynomialZeroSet p N hp f).card : ℚ≥0) / p ^ N ≤
      (f.totalDegree : ℚ≥0) / p := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa [mvPolynomialZeroSet, ZMod.card] using
    (MvPolynomial.schwartz_zippel_totalDegree hf
      (Finset.univ : Finset (ZMod p)))

/-- A nonzero polynomial of total degree `e` in `N` variables over `ZMod p`
has at most `e * p^(N-1)` zeros.  The exponent is natural-number
subtraction, so this statement also covers `N = 0`; in that case the zero
set of a nonzero constant polynomial is empty. -/
theorem card_mvPolynomialZeroSet_le_totalDegree_mul
    {p N : ℕ} (hp : p.Prime) (f : MvPolynomial (Fin N) (ZMod p))
    (hf : f ≠ 0) :
    (mvPolynomialZeroSet p N hp f).card ≤ f.totalDegree * p ^ (N - 1) := by
  by_cases hN : N = 0
  · subst N
    have hratio := mvPolynomialZeroSet_ratio_le_totalDegree_div hp f hf
    have hdegree : f.totalDegree = 0 := by
      rw [f.eq_C_of_isEmpty, MvPolynomial.totalDegree_C]
    simp only [hdegree, Nat.cast_zero, zero_div, pow_zero, div_one,
      nonpos_iff_eq_zero] at hratio
    simpa [hdegree] using hratio
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
    have hratio := mvPolynomialZeroSet_ratio_le_totalDegree_div hp f hf
    have hpNN : (p : ℚ≥0) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpPowNN : (p : ℚ≥0) ^ (n + 1) ≠ 0 := pow_ne_zero _ hpNN
    have hbound :
        ((mvPolynomialZeroSet p (n + 1) hp f).card : ℚ≥0) ≤
          (f.totalDegree : ℚ≥0) * p ^ n := by
      calc
        ((mvPolynomialZeroSet p (n + 1) hp f).card : ℚ≥0) =
            (((mvPolynomialZeroSet p (n + 1) hp f).card : ℚ≥0) /
              p ^ (n + 1)) * p ^ (n + 1) :=
          (div_mul_cancel₀ _ hpPowNN).symm
        _ ≤ ((f.totalDegree : ℚ≥0) / p) * p ^ (n + 1) :=
          mul_le_mul_left hratio _
        _ = (f.totalDegree : ℚ≥0) * p ^ n := by
          rw [pow_succ]
          calc
            (f.totalDegree : ℚ≥0) / p * (p ^ n * p) =
                ((f.totalDegree : ℚ≥0) / p * p) * p ^ n := by ac_rfl
            _ = (f.totalDegree : ℚ≥0) * p ^ n := by
              rw [div_mul_cancel₀ _ hpNN]
    exact_mod_cast hbound

/-- The degree-at-most-`e` form of the literal finite-field zero-set bound. -/
theorem card_mvPolynomialZeroSet_le_degree_mul
    {p N e : ℕ} (hp : p.Prime) (f : MvPolynomial (Fin N) (ZMod p))
    (hf : f ≠ 0) (hdegree : f.totalDegree ≤ e) :
    (mvPolynomialZeroSet p N hp f).card ≤ e * p ^ (N - 1) := by
  exact (card_mvPolynomialZeroSet_le_totalDegree_mul hp f hf).trans
    (Nat.mul_le_mul_right (p ^ (N - 1)) hdegree)

/-- If one member of a finite family is nonzero, then the literal common
zero set is contained in the zero set of that member. -/
theorem mvPolynomialCommonZeroSet_subset_zeroSet_of_mem
    {p N : ℕ} (hp : p.Prime)
    (family : Finset (MvPolynomial (Fin N) (ZMod p)))
    {f : MvPolynomial (Fin N) (ZMod p)} (hfmem : f ∈ family) :
    mvPolynomialCommonZeroSet p N hp family ⊆
      mvPolynomialZeroSet p N hp f := by
  intro x hx
  rw [mem_mvPolynomialZeroSet_iff]
  exact (mem_mvPolynomialCommonZeroSet_iff hp family x).mp hx f hfmem

/-- A single explicitly chosen nonzero member bounds the common zero set of
the whole finite family. -/
theorem card_mvPolynomialCommonZeroSet_le_degree_mul_of_mem
    {p N e : ℕ} (hp : p.Prime)
    (family : Finset (MvPolynomial (Fin N) (ZMod p)))
    {f : MvPolynomial (Fin N) (ZMod p)}
    (hfmem : f ∈ family) (hf : f ≠ 0) (hdegree : f.totalDegree ≤ e) :
    (mvPolynomialCommonZeroSet p N hp family).card ≤
      e * p ^ (N - 1) := by
  exact (Finset.card_le_card
    (mvPolynomialCommonZeroSet_subset_zeroSet_of_mem hp family hfmem)).trans
      (card_mvPolynomialZeroSet_le_degree_mul hp f hf hdegree)

end

end TranslatedDepthSeven
