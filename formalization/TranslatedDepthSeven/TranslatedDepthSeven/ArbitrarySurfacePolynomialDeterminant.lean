import Mathlib
import TranslatedDepthSeven.SmoothPointPadicDeterminant

/-!
# Arbitrary polynomial families in a two-dimensional residue disc

This file proves the finite-dimensional algebraic core of the
multiplicity-one surface case of the p-adic determinant method.

For any `r` integral bivariate polynomials, evaluated at `r` integral points
in one residue class modulo `p`, the evaluation determinant is divisible by
the product of the first `r` powers in the bivariate monomial filtration.
Concretely, if

`r = affinePlaneMonomialCount k + s`,

then the exponent is at least

`affinePlaneMonomialWeight k + (k + 1) * s`.

Unlike the literal monomial-block result in
`SmoothPointPadicDeterminant`, the polynomials here are completely
arbitrary.  The proof factors their evaluation matrix through the finite
union of their monomial supports and uses a rectangular determinant
expansion.  Every injective choice of `r` distinct monomials has at least the
sum of the first `r` bivariate total degrees.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped BigOperators

/-! ## A rectangular determinant expansion with weighted columns -/

private theorem rectangular_det_noninjective_sum_eq_zero
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι κ ℤ) (N : Matrix κ ι ℤ)
    {f : ι → κ} (hf : ¬ Function.Injective f) :
    (∑ σ : Equiv.Perm ι,
      Equiv.Perm.sign σ * ∏ i, M (σ i) (f i) * N (f i) i) = 0 := by
  rw [Function.Injective] at hf
  push_neg at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  exact Finset.sum_involution (fun σ _ ↦ σ * Equiv.swap i j)
    (fun σ _ ↦ by
      have hprod : (∏ x, M (σ x) (f x)) =
          ∏ x, M ((σ * Equiv.swap i j) x) (f x) :=
        Fintype.prod_equiv (Equiv.swap i j) _ _
          (by simp [Equiv.apply_swap_eq_self hij])
      simp [hprod, Equiv.Perm.sign_swap hne, -Equiv.Perm.sign_swap',
        Finset.prod_mul_distrib])
    (fun σ _ _ ↦ (not_congr Equiv.mul_swap_eq_iff).mpr hne)
    (fun _ _ ↦ Finset.mem_univ _) fun σ _ ↦
      Equiv.mul_swap_involutive i j σ

/-- The determinant of a square matrix factored through an arbitrary finite
middle index, written so that each term chooses one middle index for every
column.  Non-injective choices cancel in pairs. -/
theorem det_rectangular_mul_expansion
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix ι κ ℤ) (N : Matrix κ ι ℤ) :
    (M * N).det =
      ∑ f : ι → κ, ∑ σ : Equiv.Perm ι,
        Equiv.Perm.sign σ * ∏ i, M (σ i) (f i) * N (f i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  rfl

/-- If the row indexed by `a` of the right rectangular factor is divisible
by `p ^ weight a`, and every injective choice of middle indices has total
weight at least `exponent`, then `p ^ exponent` divides the determinant. -/
theorem pow_dvd_det_rectangular_mul_of_injective_weight
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ ℤ) (N : Matrix κ ι ℤ)
    (p : ℤ) (weight : κ → ℕ) (exponent : ℕ)
    (hN : ∀ a j, p ^ weight a ∣ N a j)
    (hweight : ∀ f : ι → κ, Function.Injective f →
      exponent ≤ ∑ i, weight (f i)) :
    p ^ exponent ∣ (M * N).det := by
  rw [det_rectangular_mul_expansion]
  apply Finset.dvd_sum
  intro f hf
  by_cases hinj : Function.Injective f
  · apply Finset.dvd_sum
    intro σ hσ
    have hprod : p ^ (∑ i, weight (f i)) ∣
        ∏ i, N (f i) i := by
      have h := Finset.prod_dvd_prod_of_dvd
        (s := Finset.univ)
        (fun i ↦ p ^ weight (f i)) (fun i ↦ N (f i) i)
        (fun i hi ↦ hN (f i) i)
      simpa only [Finset.prod_pow_eq_pow_sum Finset.univ
        (fun i ↦ weight (f i)) p] using h
    have hsmall : p ^ exponent ∣ p ^ (∑ i, weight (f i)) :=
      pow_dvd_pow p (hweight f hinj)
    have hterm : p ^ exponent ∣ ∏ i, N (f i) i := hsmall.trans hprod
    rw [Finset.prod_mul_distrib]
    simpa only [mul_assoc] using dvd_mul_of_dvd_right hterm
      (Equiv.Perm.sign σ * ∏ i, M (σ i) (f i))
  · rw [rectangular_det_noninjective_sum_eq_zero M N hinj]
    exact dvd_zero _

/-! ## The sum of the first bivariate monomial weights -/

private theorem affinePlaneMonomialCount_mono {a b : ℕ} (hab : a ≤ b) :
    affinePlaneMonomialCount a ≤ affinePlaneMonomialCount b := by
  unfold affinePlaneMonomialCount
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hab 1)
  · simp

private theorem sum_count_complement_eq_weight_add
    (k s : ℕ) :
    (∑ d ∈ Finset.range (k + 1),
      (affinePlaneMonomialCount k + s - affinePlaneMonomialCount d)) =
      affinePlaneMonomialWeight k + (k + 1) * s := by
  induction k with
  | zero => simp [affinePlaneMonomialCount, affinePlaneMonomialWeight]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have hcount : affinePlaneMonomialCount (k + 1) =
          affinePlaneMonomialCount k + (k + 2) := by
        simp [affinePlaneMonomialCount, Finset.sum_range_succ]
      have hweight : affinePlaneMonomialWeight (k + 1) =
          affinePlaneMonomialWeight k + (k + 1) * (k + 2) := by
        simp [affinePlaneMonomialWeight, Finset.sum_range_succ]
      rw [hcount, hweight]
      have hterm (d : ℕ) (hd : d ∈ Finset.range (k + 1)) :
          affinePlaneMonomialCount k + (k + 2) + s -
              affinePlaneMonomialCount d =
            (affinePlaneMonomialCount k + s - affinePlaneMonomialCount d) +
              (k + 2) := by
        have hdk : d ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
        have hle := affinePlaneMonomialCount_mono hdk
        omega
      rw [Finset.sum_congr rfl hterm]
      rw [Finset.sum_add_distrib, ih]
      simp
      ring

/-- A finite multiset of natural-number weights containing at most
`affinePlaneMonomialCount d` entries of weight at most `d` has at least the
sum of the first bivariate monomial weights. -/
theorem sum_weight_ge_first_affinePlaneJetWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℕ) (k s : ℕ)
    (hcard : Fintype.card ι = affinePlaneMonomialCount k + s)
    (hlow : ∀ d ≤ k,
      (Finset.univ.filter fun i ↦ weight i ≤ d).card ≤
        affinePlaneMonomialCount d) :
    affinePlaneMonomialWeight k + (k + 1) * s ≤ ∑ i, weight i := by
  have hpoint (i : ι) :
      (∑ d ∈ Finset.range (k + 1), if d < weight i then 1 else 0) ≤
        weight i := by
    rw [Finset.sum_boole]
    have hsubset : (Finset.range (k + 1)).filter (fun d ↦ d < weight i) ⊆
        Finset.range (weight i) := by
      intro d hd
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hd).2
    exact (Finset.card_le_card hsubset).trans_eq (Finset.card_range _)
  have hsum :
      (∑ i, ∑ d ∈ Finset.range (k + 1),
        if d < weight i then 1 else 0) ≤ ∑ i, weight i :=
    Finset.sum_le_sum fun i _ ↦ hpoint i
  have hhigh (d : ℕ) (hd : d ∈ Finset.range (k + 1)) :
      Fintype.card ι - affinePlaneMonomialCount d ≤
        (Finset.univ.filter fun i ↦ d < weight i).card := by
    have hdle : d ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    have hlo := hlow d hdle
    have hpart := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset ι)) (fun i ↦ weight i ≤ d)
    simp only [Finset.card_univ, not_le] at hpart
    omega
  calc
    affinePlaneMonomialWeight k + (k + 1) * s =
        ∑ d ∈ Finset.range (k + 1),
          (Fintype.card ι - affinePlaneMonomialCount d) := by
      rw [hcard, sum_count_complement_eq_weight_add]
    _ ≤ ∑ d ∈ Finset.range (k + 1),
        (Finset.univ.filter fun i ↦ d < weight i).card := by
      exact Finset.sum_le_sum hhigh
    _ = ∑ i, ∑ d ∈ Finset.range (k + 1),
        if d < weight i then 1 else 0 := by
      calc
        (∑ d ∈ Finset.range (k + 1),
            (Finset.univ.filter fun i ↦ d < weight i).card) =
            ∑ d ∈ Finset.range (k + 1),
              ∑ i ∈ Finset.univ, if d < weight i then 1 else 0 := by
          congr 1
          funext d
          exact (Finset.sum_boole (fun i ↦ d < weight i) Finset.univ).symm
        _ = ∑ i ∈ Finset.univ, ∑ d ∈ Finset.range (k + 1),
            if d < weight i then 1 else 0 := by rw [Finset.sum_comm]
        _ = _ := by simp
    _ ≤ ∑ i, weight i := hsum

private def pairOfWeightLeToAffinePlaneMonomialIndex
    {κ : Type*} (coord : κ → ℕ × ℕ) (d : ℕ)
    (a : {a : κ // (coord a).1 + (coord a).2 ≤ d}) :
    AffinePlaneMonomialIndex d :=
  ⟨⟨(coord a).1 + (coord a).2, Nat.lt_succ_iff.mpr a.property⟩,
    ⟨(coord a).1, by
      change (coord (a : κ)).1 <
        (coord (a : κ)).1 + (coord (a : κ)).2 + 1
      omega⟩⟩

private theorem pairOfWeightLeToAffinePlaneMonomialIndex_injective
    {κ : Type*} (coord : κ → ℕ × ℕ) (hcoord : Function.Injective coord)
    (d : ℕ) :
    Function.Injective (pairOfWeightLeToAffinePlaneMonomialIndex coord d) := by
  intro a b hab
  apply Subtype.ext
  apply hcoord
  apply Prod.ext
  · exact congrArg (fun u : AffinePlaneMonomialIndex d ↦ u.2.val) hab
  · have hsum := congrArg
      (fun u : AffinePlaneMonomialIndex d ↦ u.1.val) hab
    have hfirst := congrArg
      (fun u : AffinePlaneMonomialIndex d ↦ u.2.val) hab
    dsimp [pairOfWeightLeToAffinePlaneMonomialIndex] at hsum hfirst
    omega

private theorem card_pair_weight_le_affinePlaneMonomialCount
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (coord : κ → ℕ × ℕ) (hcoord : Function.Injective coord) (d : ℕ) :
    (Finset.univ.filter fun a ↦ (coord a).1 + (coord a).2 ≤ d).card ≤
      affinePlaneMonomialCount d := by
  have hcard := Fintype.card_le_of_injective
    (pairOfWeightLeToAffinePlaneMonomialIndex coord d)
    (pairOfWeightLeToAffinePlaneMonomialIndex_injective coord hcoord d)
  rw [card_affinePlaneMonomialIndex] at hcard
  rw [Fintype.card_subtype] at hcard
  exact hcard

/-- Among any injectively selected family of distinct bivariate monomials,
the total degree is at least the sum of the first monomial weights. -/
theorem sum_pair_weight_ge_first_affinePlaneJetWeight
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (coord : κ → ℕ × ℕ) (hcoord : Function.Injective coord)
    (f : ι → κ) (hf : Function.Injective f)
    (k s : ℕ)
    (hcard : Fintype.card ι = affinePlaneMonomialCount k + s) :
    affinePlaneMonomialWeight k + (k + 1) * s ≤
      ∑ i, ((coord (f i)).1 + (coord (f i)).2) := by
  apply sum_weight_ge_first_affinePlaneJetWeight
    (fun i ↦ (coord (f i)).1 + (coord (f i)).2) k s hcard
  intro d hd
  let low : {i : ι // (coord (f i)).1 + (coord (f i)).2 ≤ d} →
      {a : κ // (coord a).1 + (coord a).2 ≤ d} :=
    fun i ↦ ⟨f i, i.property⟩
  have hlow : Function.Injective low := by
    intro i j hij
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hij
  have hcardLow := Fintype.card_le_of_injective low hlow
  have hpair := card_pair_weight_le_affinePlaneMonomialCount coord hcoord d
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcardLow
  exact hcardLow.trans hpair

/-! ## Factorization of an arbitrary polynomial evaluation matrix -/

/-- Translation by the integral point `y`, so that evaluation in the
residue disc is expressed in the two differences `X i - y i`. -/
def translateBivariatePolynomial (y : Fin 2 → ℤ)
    (f : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.aeval (fun i ↦ C (y i) + X i) f

/-- Exact evaluation identity for translation by `y`. -/
theorem eval_translateBivariatePolynomial (y z : Fin 2 → ℤ)
    (f : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial.eval z (translateBivariatePolynomial y f) =
      MvPolynomial.eval (fun i ↦ y i + z i) f := by
  change MvPolynomial.aeval z
      (MvPolynomial.aeval (fun i ↦ C (y i) + X i) f) =
    MvPolynomial.aeval (fun i ↦ y i + z i) f
  rw [MvPolynomial.comp_aeval_apply]
  apply DFunLike.congr_fun
  ext i
  simp

/-- The finite union of the monomial supports of a translated family. -/
def translatedBivariateCommonSupport {ι : Type*} [Fintype ι]
    (y : Fin 2 → ℤ) (F : ι → MvPolynomial (Fin 2) ℤ) :
    Finset (Fin 2 →₀ ℕ) :=
  Finset.univ.biUnion fun i ↦ (translateBivariatePolynomial y (F i)).support

/-- The monomials which occur in at least one member of the translated
family. -/
abbrev TranslatedBivariateCommonSupportIndex {ι : Type*} [Fintype ι]
    (y : Fin 2 → ℤ) (F : ι → MvPolynomial (Fin 2) ℤ) :=
  {d : Fin 2 →₀ ℕ // d ∈ translatedBivariateCommonSupport y F}

private theorem support_translateBivariatePolynomial_subset_commonSupport
    {ι : Type*} [Fintype ι]
    (y : Fin 2 → ℤ) (F : ι → MvPolynomial (Fin 2) ℤ) (i : ι) :
    (translateBivariatePolynomial y (F i)).support ⊆
      translatedBivariateCommonSupport y F := by
  intro d hd
  rw [translatedBivariateCommonSupport, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ _, hd⟩

/-- The pair of exponents of a monomial in the common bivariate support. -/
def translatedBivariateCommonSupportCoord
    {ι : Type*} [Fintype ι]
    (y : Fin 2 → ℤ) (F : ι → MvPolynomial (Fin 2) ℤ) :
    TranslatedBivariateCommonSupportIndex y F → ℕ × ℕ :=
  fun d ↦ (d.val 0, d.val 1)

theorem translatedBivariateCommonSupportCoord_injective
    {ι : Type*} [Fintype ι]
    (y : Fin 2 → ℤ) (F : ι → MvPolynomial (Fin 2) ℤ) :
    Function.Injective (translatedBivariateCommonSupportCoord y F) := by
  intro a b hab
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact congrArg Prod.fst hab
  · exact congrArg Prod.snd hab

/-- Coefficients of the translated family, restricted to its finite common
support. -/
def translatedBivariateCoefficientMatrix
    {ι : Type*} [Fintype ι]
    (y : Fin 2 → ℤ) (F : ι → MvPolynomial (Fin 2) ℤ) :
    Matrix ι (TranslatedBivariateCommonSupportIndex y F) ℤ :=
  fun i d ↦ coeff d.val (translateBivariatePolynomial y (F i))

/-- Evaluation of the common-support monomials in the two coordinate
differences from `y`. -/
def translatedBivariateMonomialEvaluationMatrix
    {ι : Type*} [Fintype ι]
    (y : Fin 2 → ℤ) (F : ι → MvPolynomial (Fin 2) ℤ)
    (x : ι → Fin 2 → ℤ) :
    Matrix (TranslatedBivariateCommonSupportIndex y F) ι ℤ :=
  fun d j ↦
    (x j 0 - y 0) ^ d.val 0 * (x j 1 - y 1) ^ d.val 1

/-- An arbitrary bivariate polynomial evaluation matrix factors through
the finite common monomial support of the translated polynomials. -/
theorem bivariatePolynomialEvaluation_eq_coefficient_mul_monomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : Fin 2 → ℤ) (F : ι → MvPolynomial (Fin 2) ℤ)
    (x : ι → Fin 2 → ℤ) :
    Matrix.of (fun i j ↦ MvPolynomial.eval (x j) (F i)) =
      translatedBivariateCoefficientMatrix y F *
        translatedBivariateMonomialEvaluationMatrix y F x := by
  ext i j
  rw [Matrix.mul_apply]
  let z : Fin 2 → ℤ := fun q ↦ x j q - y q
  have hpoint : (fun q ↦ y q + z q) = x j := by
    funext q
    simp [z]
  change MvPolynomial.eval (x j) (F i) = _
  rw [← hpoint, ← eval_translateBivariatePolynomial]
  rw [MvPolynomial.eval_eq']
  simp only [translatedBivariateCoefficientMatrix,
    translatedBivariateMonomialEvaluationMatrix, Fin.prod_univ_two]
  change
    (∑ d ∈ (translateBivariatePolynomial y (F i)).support,
      coeff d (translateBivariatePolynomial y (F i)) *
        ((x j 0 - y 0) ^ d 0 * (x j 1 - y 1) ^ d 1)) =
      ∑ d : TranslatedBivariateCommonSupportIndex y F,
        coeff d.val (translateBivariatePolynomial y (F i)) *
          ((x j 0 - y 0) ^ d.val 0 * (x j 1 - y 1) ^ d.val 1)
  rw [← Finset.sum_subtype (translatedBivariateCommonSupport y F)
    (fun _ ↦ Iff.rfl)
    (fun d ↦ coeff d (translateBivariatePolynomial y (F i)) *
      ((x j 0 - y 0) ^ d 0 * (x j 1 - y 1) ^ d 1))]
  apply Finset.sum_subset
  · exact support_translateBivariatePolynomial_subset_commonSupport y F i
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul]

/-- Every translated support monomial has the p-adic divisibility given by
its total degree throughout one residue class. -/
theorem pow_totalDegree_dvd_translatedBivariateMonomialEvaluation
    {ι : Type*} [Fintype ι]
    (p : ℤ) (y : Fin 2 → ℤ)
    (F : ι → MvPolynomial (Fin 2) ℤ)
    (x : ι → Fin 2 → ℤ)
    (hx : ∀ j i, p ∣ x j i - y i)
    (d : TranslatedBivariateCommonSupportIndex y F) (j : ι) :
    p ^ ((translatedBivariateCommonSupportCoord y F d).1 +
        (translatedBivariateCommonSupportCoord y F d).2) ∣
      translatedBivariateMonomialEvaluationMatrix y F x d j := by
  change p ^ (d.val 0 + d.val 1) ∣
    (x j 0 - y 0) ^ d.val 0 * (x j 1 - y 1) ^ d.val 1
  rw [pow_add]
  exact mul_dvd_mul (pow_dvd_pow_of_dvd (hx j 0) _)
    (pow_dvd_pow_of_dvd (hx j 1) _)

/-! ## The arbitrary-family local determinant theorem -/

/-- The exact first-layer p-adic exponent for an arbitrary finite family of
bivariate integral polynomials evaluated at points in one residue class.

When `s ≤ k + 2`, the displayed exponent is exactly the sum of the first
`card ι` total degrees in `ℤ[X₁,X₂]`.  The divisibility itself remains true
without that restriction. -/
theorem arbitraryBivariatePolynomialEvaluation_det_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k s : ℕ)
    (hcard : Fintype.card ι = affinePlaneMonomialCount k + s)
    (p : ℤ) (y : Fin 2 → ℤ)
    (x : ι → Fin 2 → ℤ)
    (F : ι → MvPolynomial (Fin 2) ℤ)
    (hx : ∀ j i, p ∣ x j i - y i) :
    p ^ (affinePlaneMonomialWeight k + (k + 1) * s) ∣
      (filteredPolynomialEvaluationMatrix F x).det := by
  rw [show filteredPolynomialEvaluationMatrix F x =
      Matrix.of (fun i j ↦ MvPolynomial.eval (x j) (F i)) by rfl]
  rw [bivariatePolynomialEvaluation_eq_coefficient_mul_monomial]
  apply pow_dvd_det_rectangular_mul_of_injective_weight
    (translatedBivariateCoefficientMatrix y F)
    (translatedBivariateMonomialEvaluationMatrix y F x)
    p
    (fun d ↦ (translatedBivariateCommonSupportCoord y F d).1 +
      (translatedBivariateCommonSupportCoord y F d).2)
    (affinePlaneMonomialWeight k + (k + 1) * s)
  · exact pow_totalDegree_dvd_translatedBivariateMonomialEvaluation
      p y F x hx
  · intro f hf
    exact sum_pair_weight_ge_first_affinePlaneJetWeight
      (translatedBivariateCommonSupportCoord y F)
      (translatedBivariateCommonSupportCoord_injective y F)
      f hf k s hcard

/-- Literal vanishing modulo `p^a` of the arbitrary-family determinant at
every exponent `a` not exceeding the first-layer bivariate weight. -/
theorem arbitraryBivariatePolynomialEvaluation_det_eq_zero_zmod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (a k s : ℕ)
    (hcard : Fintype.card ι = affinePlaneMonomialCount k + s)
    (ha : a ≤ affinePlaneMonomialWeight k + (k + 1) * s)
    (y : Fin 2 → ℤ) (x : ι → Fin 2 → ℤ)
    (F : ι → MvPolynomial (Fin 2) ℤ)
    (hx : ∀ j i, (p : ℤ) ∣ x j i - y i) :
    (((filteredPolynomialEvaluationMatrix F x).det : ℤ) : ZMod (p ^ a)) =
      0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsmall : (p : ℤ) ^ a ∣
      (p : ℤ) ^ (affinePlaneMonomialWeight k + (k + 1) * s) :=
    pow_dvd_pow (p : ℤ) ha
  exact hsmall.trans
    (arbitraryBivariatePolynomialEvaluation_det_dvd
      k s hcard (p : ℤ) y x F hx)

end

end TranslatedDepthSeven
