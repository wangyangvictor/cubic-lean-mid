import TranslatedDepthSeven.StarEquations
import TranslatedDepthSeven.JacobianCertificatePolynomialHeight
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Explicit size bounds for the equations of a star of lines

This file records literal algebraic bounds for the coefficient polynomials
constructed in `StarEquations`.  The bounds use only the monomial support,
total degree, and integral coefficients of the input polynomial, together
with coordinate bounds for the fixed point of the star.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

open MvPolynomial Polynomial

variable {σ : Type*}

/-- The same symbolic line restriction as one multivariable polynomial: the
variable `none` is the line parameter and `some i` is the `i`-th direction
coordinate. -/
def symbolicLineMvPolynomial (f : MvPolynomial σ ℤ) (h : σ → ℤ) :
    MvPolynomial (Option σ) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ MvPolynomial.C (h i) +
      MvPolynomial.X none * MvPolynomial.X (some i)) f

@[simp]
theorem symbolicLineMvPolynomial_C (a : ℤ) (h : σ → ℤ) :
    symbolicLineMvPolynomial (MvPolynomial.C a) h = MvPolynomial.C a := by
  simp [symbolicLineMvPolynomial]

theorem symbolicLineMvPolynomial_add
    (f g : MvPolynomial σ ℤ) (h : σ → ℤ) :
    symbolicLineMvPolynomial (f + g) h =
      symbolicLineMvPolynomial f h + symbolicLineMvPolynomial g h := by
  simp [symbolicLineMvPolynomial]

theorem symbolicLineMvPolynomial_mul
    (f g : MvPolynomial σ ℤ) (h : σ → ℤ) :
    symbolicLineMvPolynomial (f * g) h =
      symbolicLineMvPolynomial f h * symbolicLineMvPolynomial g h := by
  simp [symbolicLineMvPolynomial]

@[simp]
theorem symbolicLineMvPolynomial_X (i : σ) (h : σ → ℤ) :
    symbolicLineMvPolynomial (MvPolynomial.X i) h =
      MvPolynomial.C (h i) +
        MvPolynomial.X none * MvPolynomial.X (some i) := by
  simp [symbolicLineMvPolynomial]

/-- Splitting off the `none` variable recovers `symbolicLinePolynomial`
definitionally on constants and variables, hence on every polynomial. -/
theorem optionEquivLeft_symbolicLineMvPolynomial
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) :
    MvPolynomial.optionEquivLeft ℤ σ (symbolicLineMvPolynomial f h) =
      symbolicLinePolynomial f h := by
  let lhs : MvPolynomial σ ℤ →+* Polynomial (MvPolynomial σ ℤ) :=
    (MvPolynomial.optionEquivLeft ℤ σ).toRingEquiv.toRingHom.comp
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i ↦ MvPolynomial.C (h i) +
          MvPolynomial.X none * MvPolynomial.X (some i)))
  let rhs : MvPolynomial σ ℤ →+* Polynomial (MvPolynomial σ ℤ) :=
    MvPolynomial.eval₂Hom
      (Polynomial.C.comp MvPolynomial.C)
      (fun i ↦ Polynomial.C (MvPolynomial.C (h i)) +
        Polynomial.X * Polynomial.C (MvPolynomial.X i))
  change lhs f = rhs f
  apply DFunLike.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [lhs, rhs]
  · intro i
    simp [lhs, rhs, MvPolynomial.optionEquivLeft_X_none,
      MvPolynomial.optionEquivLeft_X_some]

/-- A coefficient of the polynomial split along `none` is literally the
corresponding star equation. -/
theorem coeff_optionEquivLeft_symbolicLineMvPolynomial
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k : ℕ) :
    (MvPolynomial.optionEquivLeft ℤ σ
      (symbolicLineMvPolynomial f h)).coeff k =
        starCoefficient f h k := by
  rw [optionEquivLeft_symbolicLineMvPolynomial]
  rfl

/-- A coefficient of a star equation is the coefficient with line exponent
`k` in the single polynomial on `Option σ`. -/
theorem coeff_starCoefficient_eq_coeff_symbolicLineMvPolynomial
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k : ℕ) (μ : σ →₀ ℕ) :
    (starCoefficient f h k).coeff μ =
      (symbolicLineMvPolynomial f h).coeff (μ.optionElim k) := by
  rw [← coeff_optionEquivLeft_symbolicLineMvPolynomial]
  simpa using
    (MvPolynomial.optionEquivLeft_coeff_coeff ℤ σ (μ.optionElim k)
      (symbolicLineMvPolynomial f h))

/-- The support of any one star equation injects into the support of the
single polynomial carrying the line parameter and all direction variables. -/
theorem starCoefficient_support_card_le_symbolicLineMvPolynomial
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k : ℕ) :
    (starCoefficient f h k).support.card ≤
      (symbolicLineMvPolynomial f h).support.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun μ : σ →₀ ℕ ↦ μ.optionElim k)
  · intro μ hμ
    change μ.optionElim k ∈ (symbolicLineMvPolynomial f h).support
    rw [← MvPolynomial.mem_support_coeff_optionEquivLeft]
    simpa [coeff_optionEquivLeft_symbolicLineMvPolynomial] using hμ
  · intro μ _ ν _ hμν
    apply Finsupp.ext
    intro i
    have := congrArg (fun q : Option σ →₀ ℕ ↦ q (some i)) hμν
    simpa using this

/-- The degree in the line-parameter variable does not increase under the
substitution `X_i ↦ h_i + X_none X_(some i)`. -/
theorem symbolicLineMvPolynomial_degreeOf_none_le
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) :
    (symbolicLineMvPolynomial f h).degreeOf none ≤ f.totalDegree := by
  classical
  unfold symbolicLineMvPolynomial
  change
    (MvPolynomial.eval₂ MvPolynomial.C
      (fun i ↦ MvPolynomial.C (h i) +
        MvPolynomial.X none * MvPolynomial.X (some i)) f).degreeOf none ≤
      f.totalDegree
  rw [MvPolynomial.eval₂_eq]
  apply (MvPolynomial.degreeOf_sum_le none _ _).trans
  apply Finset.sup_le
  intro m hm
  apply (MvPolynomial.degreeOf_mul_le none _ _).trans
  rw [MvPolynomial.degreeOf_C, zero_add]
  calc
    (∏ i ∈ m.support,
        (MvPolynomial.C (h i) +
          MvPolynomial.X none * MvPolynomial.X (some i)) ^ m i).degreeOf none
        ≤ ∑ i ∈ m.support,
            ((MvPolynomial.C (h i) +
              MvPolynomial.X none * MvPolynomial.X (some i)) ^ m i).degreeOf none :=
          MvPolynomial.degreeOf_prod_le none _ _
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i _hi
      apply (MvPolynomial.degreeOf_pow_le none _ _).trans
      have hlinear :
          (MvPolynomial.C (h i) +
            MvPolynomial.X none * MvPolynomial.X (some i) :
              MvPolynomial (Option σ) ℤ).degreeOf none ≤ 1 := by
        apply (MvPolynomial.degreeOf_add_le none _ _).trans
        apply max_le
        · rw [MvPolynomial.degreeOf_C]
          exact Nat.zero_le 1
        · apply (MvPolynomial.degreeOf_mul_le none _ _).trans
          simp [MvPolynomial.degreeOf_X]
      simpa using Nat.mul_le_mul_left (m i) hlinear
    _ = m.sum (fun _ exponent ↦ exponent) := rfl
    _ ≤ f.totalDegree := MvPolynomial.le_totalDegree hm

theorem starCoefficient_mul_X_zero
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (i : σ) :
    starCoefficient (f * MvPolynomial.X i) h 0 =
      MvPolynomial.C (h i) * starCoefficient f h 0 := by
  unfold starCoefficient
  rw [symbolicLinePolynomial_mul, symbolicLinePolynomial_X, mul_add,
    Polynomial.coeff_add, Polynomial.coeff_mul_C]
  have hshift :
      (symbolicLinePolynomial f h *
          (Polynomial.X * Polynomial.C (MvPolynomial.X i))).coeff 0 = 0 := by
    rw [show symbolicLinePolynomial f h *
          (Polynomial.X * Polynomial.C (MvPolynomial.X i)) =
        (symbolicLinePolynomial f h * Polynomial.X) *
          Polynomial.C (MvPolynomial.X i) by ring]
    rw [Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_zero, zero_mul]
  rw [hshift, add_zero, mul_comm]

theorem starCoefficient_mul_X_succ
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (i : σ) (k : ℕ) :
    starCoefficient (f * MvPolynomial.X i) h (k + 1) =
      MvPolynomial.C (h i) * starCoefficient f h (k + 1) +
        MvPolynomial.X i * starCoefficient f h k := by
  unfold starCoefficient
  rw [symbolicLinePolynomial_mul, symbolicLinePolynomial_X, mul_add,
    Polynomial.coeff_add, Polynomial.coeff_mul_C]
  rw [show symbolicLinePolynomial f h *
        (Polynomial.X * Polynomial.C (MvPolynomial.X i)) =
      (symbolicLinePolynomial f h * Polynomial.X) *
        Polynomial.C (MvPolynomial.X i) by ring]
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_mul_X]
  ring

@[simp]
theorem starCoefficient_zero (h : σ → ℤ) (k : ℕ) :
    starCoefficient (0 : MvPolynomial σ ℤ) h k = 0 := by
  simp [starCoefficient, symbolicLinePolynomial]

theorem starCoefficient_add
    (f g : MvPolynomial σ ℤ) (h : σ → ℤ) (k : ℕ) :
    starCoefficient (f + g) h k =
      starCoefficient f h k + starCoefficient g h k := by
  simp [starCoefficient, symbolicLinePolynomial_add]

/-- Every displayed equation of order `k` is homogeneous of degree `k` in
the direction vector. -/
theorem starCoefficient_isHomogeneous
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k : ℕ) :
    (starCoefficient f h k).IsHomogeneous k := by
  induction f using MvPolynomial.induction_on generalizing k with
  | C a =>
      unfold starCoefficient
      rw [symbolicLinePolynomial_C]
      cases k with
      | zero =>
          simpa using (MvPolynomial.isHomogeneous_C (σ := σ) a)
      | succ k =>
          rw [Polynomial.coeff_C]
          simp only [Nat.succ_ne_zero, ↓reduceIte]
          exact (MvPolynomial.homogeneousSubmodule σ ℤ (k + 1)).zero_mem
  | add f g hf hg =>
      simpa [starCoefficient, symbolicLinePolynomial_add] using
        (hf k).add (hg k)
  | mul_X f i hf =>
      cases k with
      | zero =>
          rw [starCoefficient_mul_X_zero]
          exact (hf 0).C_mul _
      | succ k =>
          rw [starCoefficient_mul_X_succ]
          apply ((hf (k + 1)).C_mul _).add
          simpa [Nat.add_comm] using
            ((MvPolynomial.isHomogeneous_X (R := ℤ) i).mul (hf k))

/-- In particular, the total degree in the direction variables is at most
the coefficient index. -/
theorem starCoefficient_totalDegree_le
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k : ℕ) :
    (starCoefficient f h k).totalDegree ≤ k :=
  (starCoefficient_isHomogeneous f h k).totalDegree_le

/-- There are no coefficient equations above the total degree of the input
polynomial. -/
theorem starCoefficient_eq_zero_of_totalDegree_lt
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) {k : ℕ}
    (hk : f.totalDegree < k) :
    starCoefficient f h k = 0 := by
  rw [← coeff_optionEquivLeft_symbolicLineMvPolynomial]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc
    (MvPolynomial.optionEquivLeft ℤ σ
      (symbolicLineMvPolynomial f h)).natDegree
        = (symbolicLineMvPolynomial f h).degreeOf none := by
          apply MvPolynomial.natDegree_optionEquivLeft
    _ ≤ f.totalDegree := symbolicLineMvPolynomial_degreeOf_none_le f h
    _ < k := hk

/-- The star coefficient has both its intrinsic homogeneous bound `k` and
the inherited degree bound from `f`. -/
theorem starCoefficient_totalDegree_le_min
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k : ℕ) :
    (starCoefficient f h k).totalDegree ≤ min k f.totalDegree := by
  by_cases hk : k ≤ f.totalDegree
  · exact le_min (starCoefficient_totalDegree_le f h k)
      ((starCoefficient_totalDegree_le f h k).trans hk)
  · have hk' : f.totalDegree < k := Nat.lt_of_not_ge hk
    rw [starCoefficient_eq_zero_of_totalDegree_lt f h hk']
    simp

/-- The support estimate for one substituted monomial does not require any
bound on the coordinates of the fixed point. -/
theorem symbolicLineMvPolynomial_monomial_support_card_le
    (h : σ → ℤ) (m : σ →₀ ℕ) (a : ℤ) :
    (symbolicLineMvPolynomial (MvPolynomial.monomial m a) h).support.card ≤
      2 ^ Finsupp.degree m := by
  classical
  induction hdeg : Finsupp.degree m using Nat.strong_induction_on generalizing m with
  | _ D ih =>
      by_cases hD : D = 0
      · have hm : m = 0 :=
          (Finsupp.degree_eq_zero_iff m).mp (hdeg.trans hD)
        subst m
        subst D
        rw [← MvPolynomial.C_apply, symbolicLineMvPolynomial_C, pow_zero]
        exact (Finset.card_le_card MvPolynomial.support_monomial_subset).trans_eq
          (Finset.card_singleton 0)
      · have hm0 : m ≠ 0 := by
          intro hm
          subst m
          exact hD (by simpa using hdeg.symm)
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
        let m' : σ →₀ ℕ := m - Finsupp.single i 1
        have hdegree : Finsupp.degree m' + 1 = D := by
          calc
            Finsupp.degree m' + 1 = Finsupp.degree m := by
              simpa only [Finsupp.degree_eq_weight_one, m'] using
                (Finsupp.weight_sub_single_add (w := fun _ : σ ↦ 1) hi)
            _ = D := hdeg
        have hlt : Finsupp.degree m' < D := by omega
        have hm_add : m' + Finsupp.single i 1 = m :=
          Finsupp.sub_add_single_one_cancel hi
        have hmonomial :
            MvPolynomial.monomial m a =
              MvPolynomial.monomial m' a * MvPolynomial.X i := by
          rw [← hm_add, MvPolynomial.monomial_add_single, pow_one]
        rw [hmonomial, symbolicLineMvPolynomial_mul,
          symbolicLineMvPolynomial_X, ← hdegree, pow_succ]
        calc
          (symbolicLineMvPolynomial (MvPolynomial.monomial m' a) h *
              (MvPolynomial.C (h i) +
                MvPolynomial.X none * MvPolynomial.X (some i))).support.card ≤
              (symbolicLineMvPolynomial
                  (MvPolynomial.monomial m' a) h).support.card *
                (MvPolynomial.C (h i) +
                  MvPolynomial.X none * MvPolynomial.X (some i) :
                    MvPolynomial (Option σ) ℤ).support.card := by
            exact (Finset.card_le_card (MvPolynomial.support_mul _ _)).trans
              Finset.card_add_le
          _ ≤ 2 ^ Finsupp.degree m' * 2 := by
            apply Nat.mul_le_mul (ih (Finsupp.degree m') hlt m' rfl)
            calc
              (MvPolynomial.C (h i) +
                  MvPolynomial.X none * MvPolynomial.X (some i) :
                    MvPolynomial (Option σ) ℤ).support.card ≤
                  (MvPolynomial.C (h i) :
                    MvPolynomial (Option σ) ℤ).support.card +
                    (MvPolynomial.X none * MvPolynomial.X (some i) :
                      MvPolynomial (Option σ) ℤ).support.card := by
                exact (Finset.card_le_card MvPolynomial.support_add).trans
                  (Finset.card_union_le _ _)
              _ ≤ 2 := by
                change _ ≤ 1 + 1
                apply Nat.add_le_add
                · rw [MvPolynomial.C_apply]
                  exact
                    (Finset.card_le_card
                      MvPolynomial.support_monomial_subset).trans_eq
                        (Finset.card_singleton 0)
                · rw [show
                      (MvPolynomial.X none * MvPolynomial.X (some i) :
                          MvPolynomial (Option σ) ℤ) =
                        MvPolynomial.monomial
                          (Finsupp.single none 1 + Finsupp.single (some i) 1) 1 by
                      simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
                  exact
                    (Finset.card_le_card
                      MvPolynomial.support_monomial_subset).trans_eq
                        (Finset.card_singleton _)

/-- A source monomial of degree `D` produces at most `2^D` monomials after
the literal substitution `X_i ↦ h_i + T z_i`.  Every resulting integer
coefficient has the displayed elementary height bound. -/
theorem symbolicLineMvPolynomial_monomial_bounds
    (h : σ → ℤ) (H : ℕ) (hy : ∀ i, (h i).natAbs ≤ H)
    (m : σ →₀ ℕ) (a : ℤ) :
    (symbolicLineMvPolynomial (MvPolynomial.monomial m a) h).support.card ≤
        2 ^ Finsupp.degree m ∧
      ∀ v : Option σ →₀ ℕ,
        ((symbolicLineMvPolynomial (MvPolynomial.monomial m a) h).coeff v).natAbs ≤
          a.natAbs * (2 * max 1 H) ^ Finsupp.degree m := by
  classical
  induction hdeg : Finsupp.degree m using Nat.strong_induction_on generalizing m with
  | _ D ih =>
      by_cases hD : D = 0
      · have hm : m = 0 :=
          (Finsupp.degree_eq_zero_iff m).mp (hdeg.trans hD)
        subst m
        subst D
        constructor
        · rw [← MvPolynomial.C_apply, symbolicLineMvPolynomial_C, pow_zero]
          exact (Finset.card_le_card MvPolynomial.support_monomial_subset).trans_eq
            (Finset.card_singleton 0)
        · intro v
          rw [← MvPolynomial.C_apply, symbolicLineMvPolynomial_C,
            MvPolynomial.coeff_C, pow_zero, mul_one]
          split_ifs <;> simp
      · have hm0 : m ≠ 0 := by
          intro hm
          subst m
          exact hD (by simpa using hdeg.symm)
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
        let m' : σ →₀ ℕ := m - Finsupp.single i 1
        have hdegree : Finsupp.degree m' + 1 = D := by
          calc
            Finsupp.degree m' + 1 = Finsupp.degree m := by
              simpa only [Finsupp.degree_eq_weight_one, m'] using
                (Finsupp.weight_sub_single_add (w := fun _ : σ ↦ 1) hi)
            _ = D := hdeg
        have hlt : Finsupp.degree m' < D := by omega
        have hm_add : m' + Finsupp.single i 1 = m :=
          Finsupp.sub_add_single_one_cancel hi
        have hmonomial :
            MvPolynomial.monomial m a =
              MvPolynomial.monomial m' a * MvPolynomial.X i := by
          rw [← hm_add, MvPolynomial.monomial_add_single, pow_one]
        let P : MvPolynomial (Option σ) ℤ :=
          symbolicLineMvPolynomial (MvPolynomial.monomial m' a) h
        let L : MvPolynomial (Option σ) ℤ :=
          MvPolynomial.C (h i) +
            MvPolynomial.X none * MvPolynomial.X (some i)
        have hrewrite :
            symbolicLineMvPolynomial (MvPolynomial.monomial m a) h = P * L := by
          rw [hmonomial, symbolicLineMvPolynomial_mul,
            symbolicLineMvPolynomial_X]
        have hIH := ih (Finsupp.degree m') hlt m' rfl
        have hLsupport : L.support.card ≤ 2 := by
          calc
            L.support.card ≤
                (MvPolynomial.C (h i) : MvPolynomial (Option σ) ℤ).support.card +
                  (MvPolynomial.X none * MvPolynomial.X (some i) :
                    MvPolynomial (Option σ) ℤ).support.card := by
              exact (Finset.card_le_card MvPolynomial.support_add).trans
                (Finset.card_union_le _ _)
            _ ≤ 2 := by
              change _ ≤ 1 + 1
              apply Nat.add_le_add
              · rw [MvPolynomial.C_apply]
                exact
                  (Finset.card_le_card MvPolynomial.support_monomial_subset).trans_eq
                    (Finset.card_singleton 0)
              · rw [show
                    (MvPolynomial.X none * MvPolynomial.X (some i) :
                        MvPolynomial (Option σ) ℤ) =
                      MvPolynomial.monomial
                        (Finsupp.single none 1 + Finsupp.single (some i) 1) 1 by
                    simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
                exact
                  (Finset.card_le_card MvPolynomial.support_monomial_subset).trans_eq
                    (Finset.card_singleton _)
        constructor
        · rw [hrewrite, ← hdegree, pow_succ]
          calc
            (P * L).support.card ≤ P.support.card * L.support.card := by
              exact (Finset.card_le_card (MvPolynomial.support_mul P L)).trans
                Finset.card_add_le
            _ ≤ 2 ^ Finsupp.degree m' * 2 :=
              Nat.mul_le_mul hIH.1 hLsupport
        · intro v
          rw [hrewrite, ← hdegree]
          let e : Option σ →₀ ℕ :=
            Finsupp.single none 1 + Finsupp.single (some i) 1
          have hX :
              (MvPolynomial.X none * MvPolynomial.X (some i) :
                  MvPolynomial (Option σ) ℤ) =
                MvPolynomial.monomial e 1 := by
            simp [e, MvPolynomial.X, MvPolynomial.monomial_mul]
          have hfirst :
              ((P * MvPolynomial.C (h i)).coeff v).natAbs ≤
                (a.natAbs * (2 * max 1 H) ^ Finsupp.degree m') *
                  max 1 H := by
            rw [mul_comm P, MvPolynomial.coeff_C_mul, Int.natAbs_mul]
            simpa [mul_comm] using
              Nat.mul_le_mul ((hy i).trans (Nat.le_max_right 1 H)) (hIH.2 v)
          have hsecond :
              ((P * MvPolynomial.monomial e 1).coeff v).natAbs ≤
                a.natAbs * (2 * max 1 H) ^ Finsupp.degree m' := by
            rw [MvPolynomial.coeff_mul_monomial']
            split_ifs
            · simpa using hIH.2 (v - e)
            · simp
          rw [show P * L =
              P * MvPolynomial.C (h i) +
                P * MvPolynomial.monomial e 1 by
            simp [L, hX, mul_add], MvPolynomial.coeff_add]
          calc
            (((P * MvPolynomial.C (h i)).coeff v +
                (P * MvPolynomial.monomial e 1).coeff v)).natAbs ≤
                ((P * MvPolynomial.C (h i)).coeff v).natAbs +
                  ((P * MvPolynomial.monomial e 1).coeff v).natAbs :=
              Int.natAbs_add_le _ _
            _ ≤
                (a.natAbs * (2 * max 1 H) ^ Finsupp.degree m') * max 1 H +
                  a.natAbs * (2 * max 1 H) ^ Finsupp.degree m' :=
              Nat.add_le_add hfirst hsecond
            _ ≤ a.natAbs * (2 * max 1 H) ^ (Finsupp.degree m' + 1) := by
              have hM : 1 ≤ max 1 H := Nat.le_max_left 1 H
              rw [pow_succ]
              let B := a.natAbs * (2 * max 1 H) ^ Finsupp.degree m'
              have hB : B ≤ B * max 1 H := by
                calc
                  B = B * 1 := (Nat.mul_one B).symm
                  _ ≤ B * max 1 H := Nat.mul_le_mul_left B hM
              calc
                B * max 1 H + B ≤
                    B * max 1 H + B * max 1 H := Nat.add_le_add_left hB _
                _ = a.natAbs *
                    ((2 * max 1 H) ^ Finsupp.degree m' *
                      (2 * max 1 H)) := by
                  dsimp [B]
                  ring

/-- The symbolic line polynomial is the sum of the substituted source
monomials indexed by the literal support of `f`. -/
theorem symbolicLineMvPolynomial_as_sum
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) :
    symbolicLineMvPolynomial f h =
      ∑ m ∈ f.support,
        symbolicLineMvPolynomial (MvPolynomial.monomial m (f.coeff m)) h := by
  classical
  calc
    symbolicLineMvPolynomial f h =
        symbolicLineMvPolynomial
          (∑ m ∈ f.support, MvPolynomial.monomial m (f.coeff m)) h := by
      exact congrArg (fun g ↦ symbolicLineMvPolynomial g h) f.as_sum
    _ = ∑ m ∈ f.support,
          symbolicLineMvPolynomial (MvPolynomial.monomial m (f.coeff m)) h := by
      induction f.support using Finset.induction_on with
      | empty => simp [symbolicLineMvPolynomial]
      | @insert m s hm ih =>
          rw [Finset.sum_insert hm, symbolicLineMvPolynomial_add,
            Finset.sum_insert hm, ih]

/-- Literal source support and total-degree bounds give an explicit support
bound for the single polynomial carrying the line and direction variables. -/
theorem symbolicLineMvPolynomial_support_card_le
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (d : ℕ)
    (hdegree : f.totalDegree ≤ d) :
    (symbolicLineMvPolynomial f h).support.card ≤
      f.support.card * 2 ^ d := by
  classical
  rw [symbolicLineMvPolynomial_as_sum]
  calc
    (∑ m ∈ f.support,
        symbolicLineMvPolynomial (MvPolynomial.monomial m (f.coeff m)) h).support.card ≤
        (f.support.biUnion fun m ↦
          (symbolicLineMvPolynomial
            (MvPolynomial.monomial m (f.coeff m)) h).support).card :=
      Finset.card_le_card MvPolynomial.support_sum
    _ ≤ ∑ m ∈ f.support,
        (symbolicLineMvPolynomial
          (MvPolynomial.monomial m (f.coeff m)) h).support.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ f.support, 2 ^ d := by
      apply Finset.sum_le_sum
      intro m hm
      have hmdegree : Finsupp.degree m ≤ d := by
        simpa [Finsupp.degree_eq_weight_one, Finsupp.weight_apply] using
          (MvPolynomial.le_totalDegree hm).trans hdegree
      exact (symbolicLineMvPolynomial_monomial_support_card_le h m
        (f.coeff m)).trans (pow_le_pow_right₀ (by omega) hmdegree)
    _ = f.support.card * 2 ^ d := by simp

/-- Consequently every individual star equation has the same literal
source-sensitive support bound. -/
theorem starCoefficient_support_card_le
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k d : ℕ)
    (hdegree : f.totalDegree ≤ d) :
    (starCoefficient f h k).support.card ≤ f.support.card * 2 ^ d :=
  (starCoefficient_support_card_le_symbolicLineMvPolynomial f h k).trans
    (symbolicLineMvPolynomial_support_card_le f h d hdegree)

/-- A homogeneous polynomial of degree `k` in a finite set of variables has
at most `(k+1)^N` monomials.  This elementary box bound deliberately avoids
any stars-and-bars infrastructure. -/
theorem support_card_le_pow_succ_of_isHomogeneous
    [Fintype σ] (p : MvPolynomial σ ℤ) (k : ℕ)
    (hp : p.IsHomogeneous k) :
    p.support.card ≤ (k + 1) ^ Fintype.card σ := by
  classical
  let Φ : {μ // μ ∈ p.support} → (σ → Fin (k + 1)) := fun μ i ↦
    ⟨μ.1 i, Nat.lt_succ_iff.mpr <| by
      have hdegree : Finsupp.degree μ.1 = k := by
        rw [Finsupp.degree_eq_weight_one]
        exact hp (MvPolynomial.mem_support_iff.mp μ.2)
      exact (Finsupp.le_degree i μ.1).trans_eq hdegree⟩
  have hΦ : Function.Injective Φ := by
    intro μ ν hμν
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg Fin.val (congrFun hμν i)
  simpa [Φ] using Fintype.card_le_of_injective Φ hΦ

/-- Combining the intrinsic homogeneous box bound with the source-sensitive
expansion bound gives a convenient minimum for each star equation. -/
theorem starCoefficient_support_card_le_min
    [Fintype σ] (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k d : ℕ)
    (hdegree : f.totalDegree ≤ d) :
    (starCoefficient f h k).support.card ≤
      min ((k + 1) ^ Fintype.card σ) (f.support.card * 2 ^ d) := by
  exact le_min
    (support_card_le_pow_succ_of_isHomogeneous _ _
      (starCoefficient_isHomogeneous f h k))
    (starCoefficient_support_card_le f h k d hdegree)

/-- Every integer coefficient in every star equation satisfies a completely
literal bound in terms of source support, source coefficients, source degree,
and the coordinate bound for the fixed point. -/
theorem starCoefficient_coeff_natAbs_le
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k : ℕ) (μ : σ →₀ ℕ)
    (d C H : ℕ)
    (hcoeff : ∀ m ∈ f.support, (f.coeff m).natAbs ≤ C)
    (hdegree : f.totalDegree ≤ d)
    (hy : ∀ i, (h i).natAbs ≤ H) :
    ((starCoefficient f h k).coeff μ).natAbs ≤
      f.support.card * C * (2 * max 1 H) ^ d := by
  classical
  rw [coeff_starCoefficient_eq_coeff_symbolicLineMvPolynomial,
    symbolicLineMvPolynomial_as_sum, MvPolynomial.coeff_sum]
  calc
    (∑ m ∈ f.support,
        (symbolicLineMvPolynomial
          (MvPolynomial.monomial m (f.coeff m)) h).coeff
            (μ.optionElim k)).natAbs ≤
        ∑ m ∈ f.support,
          ((symbolicLineMvPolynomial
            (MvPolynomial.monomial m (f.coeff m)) h).coeff
              (μ.optionElim k)).natAbs :=
      int_natAbs_sum_le_sum_natAbs _ _
    _ ≤ ∑ _m ∈ f.support, C * (2 * max 1 H) ^ d := by
      apply Finset.sum_le_sum
      intro m hm
      have hmdegree : Finsupp.degree m ≤ d := by
        simpa [Finsupp.degree_eq_weight_one, Finsupp.weight_apply] using
          (MvPolynomial.le_totalDegree hm).trans hdegree
      calc
        ((symbolicLineMvPolynomial
          (MvPolynomial.monomial m (f.coeff m)) h).coeff
            (μ.optionElim k)).natAbs ≤
            (f.coeff m).natAbs *
              (2 * max 1 H) ^ Finsupp.degree m :=
          (symbolicLineMvPolynomial_monomial_bounds h H hy m
            (f.coeff m)).2 _
        _ ≤ C * (2 * max 1 H) ^ d :=
          Nat.mul_le_mul (hcoeff m hm)
            (pow_le_pow_right₀ (by omega) hmdegree)
    _ = f.support.card * C * (2 * max 1 H) ^ d := by
      simp [mul_assoc]

/-- The coefficient of highest possible order in the restriction of one
monomial to `h + T z` is the same monomial in `z`. -/
theorem starCoefficient_monomial_degree
    (h : σ → ℤ) (m : σ →₀ ℕ) (a : ℤ) :
    starCoefficient (MvPolynomial.monomial m a) h (Finsupp.degree m) =
      MvPolynomial.monomial m a := by
  classical
  induction hdeg : Finsupp.degree m using Nat.strong_induction_on generalizing m with
  | _ D ih =>
      by_cases hD : D = 0
      · have hm : m = 0 :=
          (Finsupp.degree_eq_zero_iff m).mp (hdeg.trans hD)
        subst m
        simp [hD, starCoefficient, symbolicLinePolynomial]
      · have hm0 : m ≠ 0 := by
          intro hm
          subst m
          exact hD (by simpa using hdeg.symm)
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
        let m' : σ →₀ ℕ := m - Finsupp.single i 1
        have hdegree : Finsupp.degree m' + 1 = D := by
          calc
            Finsupp.degree m' + 1 = Finsupp.degree m := by
              simpa only [Finsupp.degree_eq_weight_one, m'] using
                (Finsupp.weight_sub_single_add (w := fun _ : σ ↦ 1) hi)
            _ = D := hdeg
        have hlt : Finsupp.degree m' < D := by omega
        have hm_add : m' + Finsupp.single i 1 = m := by
          exact Finsupp.sub_add_single_one_cancel hi
        have hmonomial :
            MvPolynomial.monomial m a =
              MvPolynomial.monomial m' a * MvPolynomial.X i := by
          rw [← hm_add, MvPolynomial.monomial_add_single, pow_one]
        rw [← hdegree, hmonomial, starCoefficient_mul_X_succ]
        have hzero :
            starCoefficient (MvPolynomial.monomial m' a) h
                (Finsupp.degree m' + 1) = 0 := by
          apply starCoefficient_eq_zero_of_totalDegree_lt
          exact lt_of_le_of_lt
            (MvPolynomial.totalDegree_monomial_le m' a) (Nat.lt_succ_self _)
        rw [hzero, mul_zero, zero_add, ih (Finsupp.degree m') hlt m' rfl]
        simp [mul_comm]

/-- For a homogeneous polynomial, the equation of top order in the line
parameter is exactly the original polynomial in the direction variables.
In particular it is independent of the fixed point `h`. -/
theorem starCoefficient_eq_of_isHomogeneous
    (f : MvPolynomial σ ℤ) (h : σ → ℤ) (d : ℕ)
    (hf : f.IsHomogeneous d) :
    starCoefficient f h d = f := by
  classical
  calc
    starCoefficient f h d =
        starCoefficient
          (∑ m ∈ f.support, MvPolynomial.monomial m (f.coeff m)) h d := by
      exact congrArg (fun g ↦ starCoefficient g h d) f.as_sum
    _ = ∑ m ∈ f.support,
          starCoefficient (MvPolynomial.monomial m (f.coeff m)) h d := by
      induction f.support using Finset.induction_on with
      | empty => simp
      | @insert m s hm ih =>
          rw [Finset.sum_insert hm, starCoefficient_add,
            Finset.sum_insert hm, ih]
    _ = ∑ m ∈ f.support, MvPolynomial.monomial m (f.coeff m) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmdeg : Finsupp.degree m = d := by
        rw [Finsupp.degree_eq_weight_one]
        exact hf (MvPolynomial.mem_support_iff.mp hm)
      simpa [hmdeg] using starCoefficient_monomial_degree h m (f.coeff m)
    _ = f := f.as_sum.symm

/-- If an integral affine line lies on a homogeneous cone, then its direction
lies on the cone.  This is the direct geometric consequence of the preceding
top-coefficient identity. -/
theorem eval_direction_eq_zero_of_isHomogeneous_of_eval_line_zero
    (f : MvPolynomial σ ℤ) (h z : σ → ℤ) (d : ℕ)
    (hf : f.IsHomogeneous d)
    (hline : ∀ t : ℤ, MvPolynomial.eval (fun i ↦ h i + t * z i) f = 0) :
    MvPolynomial.eval z f = 0 := by
  have hpzero : linePolynomial f h z = 0 :=
    Polynomial.zero_of_eval_zero _ fun t ↦ by
      rw [linePolynomial_eval]
      exact hline t
  have htop := eval_starCoefficient f h z d
  rw [hpzero, Polynomial.coeff_zero,
    starCoefficient_eq_of_isHomogeneous f h d hf] at htop
  exact htop

/-- The first star equation is the ordinary tangent-space equation at the
fixed point.  Thus this identification is coefficientwise and does not rely
on a geometric smoothness package. -/
theorem eval_starCoefficient_one_eq_directionalDerivative
    [Fintype σ] [DecidableEq σ]
    (f : MvPolynomial σ ℤ) (h z : σ → ℤ) :
    MvPolynomial.eval z (starCoefficient f h 1) =
      ∑ i, MvPolynomial.eval h (MvPolynomial.pderiv i f) * z i := by
  rw [eval_starCoefficient]
  rw [← linePolynomial_derivative_eval_zero f h z]
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  norm_num

/-- Every direction of an integral affine line on `f = 0` satisfies the
literal tangent equation at its base point. -/
theorem eval_starCoefficient_one_eq_zero_of_eval_line_zero
    [Fintype σ] [DecidableEq σ]
    (f : MvPolynomial σ ℤ) (h z : σ → ℤ)
    (hline : ∀ t : ℤ, MvPolynomial.eval (fun i ↦ h i + t * z i) f = 0) :
    ∑ i, MvPolynomial.eval h (MvPolynomial.pderiv i f) * z i = 0 := by
  rw [← eval_starCoefficient_one_eq_directionalDerivative f h z]
  have hpzero : linePolynomial f h z = 0 :=
    Polynomial.zero_of_eval_zero _ fun t ↦ by
      rw [linePolynomial_eval]
      exact hline t
  rw [eval_starCoefficient, hpzero]
  simp

/-- Finite-family form: a direction of a line lying on every displayed
equation is annihilated by every row of the integral Jacobian at the base
point. -/
theorem all_directionalDerivatives_eq_zero_of_eval_line_zero
    {c N : ℕ} (F : Fin c → MvPolynomial (Fin N) ℤ)
    (h z : Fin N → ℤ)
    (hline : ∀ r t, MvPolynomial.eval
      (fun i ↦ h i + t * z i) (F r) = 0) :
    ∀ r, ∑ i, MvPolynomial.eval h (MvPolynomial.pderiv i (F r)) * z i = 0 := by
  intro r
  exact eval_starCoefficient_one_eq_zero_of_eval_line_zero
    (F r) h z (hline r)

end

end TranslatedDepthSeven
