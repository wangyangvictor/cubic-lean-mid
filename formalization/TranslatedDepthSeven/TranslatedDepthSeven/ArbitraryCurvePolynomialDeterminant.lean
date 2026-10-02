import TranslatedDepthSeven.ArbitrarySurfacePolynomialDeterminant

/-!
# Arbitrary polynomial families in a one-dimensional residue disc

For `r` integral univariate polynomials evaluated at `r` integral points in
one residue class modulo `p`, the evaluation determinant is divisible by

`p ^ (0 + 1 + ... + (r - 1))`.

The proof factors the evaluation matrix through the finite union of the
translated monomial supports.  Every injective choice of `r` distinct
univariate monomials has total degree at least the displayed exponent.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped BigOperators

/-- Sum of the first `r` univariate jet weights. -/
def affineLineJetWeight (r : ℕ) : ℕ :=
  ∑ j : Fin r, j.1

theorem affineLineJetWeight_eq_sum_range (r : ℕ) :
    affineLineJetWeight r = ∑ j ∈ Finset.range r, j := by
  exact Fin.sum_univ_eq_sum_range (fun j ↦ j) r

theorem two_mul_affineLineJetWeight (r : ℕ) :
    2 * affineLineJetWeight r = r * (r - 1) := by
  rw [affineLineJetWeight_eq_sum_range, mul_comm,
    Finset.sum_range_id_mul_two]

private theorem sum_range_complement_eq_affineLineJetWeight (r : ℕ) :
    (∑ d ∈ Finset.range r, (r - (d + 1))) = affineLineJetWeight r := by
  rw [affineLineJetWeight_eq_sum_range]
  have hterm : ∀ d ∈ Finset.range r,
      r - (d + 1) = r - 1 - d := by
    intro d hd
    omega
  rw [Finset.sum_congr rfl hterm]
  exact Finset.sum_range_reflect (fun d ↦ d) r

/-- A finite family of natural weights with at most `d+1` entries of
weight at most `d` has total weight at least `0+⋯+(r-1)`. -/
theorem affineLineJetWeight_le_sum_of_low_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℕ)
    (hlow : ∀ d,
      (Finset.univ.filter fun i ↦ weight i ≤ d).card ≤ d + 1) :
    affineLineJetWeight (Fintype.card ι) ≤ ∑ i, weight i := by
  let r := Fintype.card ι
  have hpoint (i : ι) :
      (∑ d ∈ Finset.range r, if d < weight i then 1 else 0) ≤
        weight i := by
    rw [Finset.sum_boole]
    have hsubset :
        (Finset.range r).filter (fun d ↦ d < weight i) ⊆
          Finset.range (weight i) := by
      intro d hd
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hd).2
    exact (Finset.card_le_card hsubset).trans_eq (Finset.card_range _)
  have hsum :
      (∑ i, ∑ d ∈ Finset.range r,
        if d < weight i then 1 else 0) ≤ ∑ i, weight i :=
    Finset.sum_le_sum fun i _ ↦ hpoint i
  have hhigh (d : ℕ) (hd : d ∈ Finset.range r) :
      r - (d + 1) ≤
        (Finset.univ.filter fun i ↦ d < weight i).card := by
    have hlo := hlow d
    have hpart := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset ι)) (fun i ↦ weight i ≤ d)
    simp only [Finset.card_univ, not_le] at hpart
    dsimp only [r]
    omega
  calc
    affineLineJetWeight r =
        ∑ d ∈ Finset.range r, (r - (d + 1)) :=
      (sum_range_complement_eq_affineLineJetWeight r).symm
    _ ≤ ∑ d ∈ Finset.range r,
        (Finset.univ.filter fun i ↦ d < weight i).card := by
      exact Finset.sum_le_sum hhigh
    _ = ∑ i, ∑ d ∈ Finset.range r,
        if d < weight i then 1 else 0 := by
      calc
        (∑ d ∈ Finset.range r,
            (Finset.univ.filter fun i ↦ d < weight i).card) =
            ∑ d ∈ Finset.range r,
              ∑ i ∈ Finset.univ, if d < weight i then 1 else 0 := by
          congr 1
          funext d
          exact (Finset.sum_boole
            (fun i ↦ d < weight i) Finset.univ).symm
        _ = ∑ i ∈ Finset.univ, ∑ d ∈ Finset.range r,
            if d < weight i then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = _ := by simp
    _ ≤ ∑ i, weight i := hsum

/-- Injectively selected distinct univariate monomials have total degree at
least the first `card ι` jet weight. -/
theorem affineLineJetWeight_le_sum_coord_comp
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (coord : κ → ℕ) (hcoord : Function.Injective coord)
    (f : ι → κ) (hf : Function.Injective f) :
    affineLineJetWeight (Fintype.card ι) ≤ ∑ i, coord (f i) := by
  apply affineLineJetWeight_le_sum_of_low_card
  intro d
  let low : {i : ι // coord (f i) ≤ d} → Fin (d + 1) := fun i ↦
    ⟨coord (f i), Nat.lt_succ_iff.mpr i.property⟩
  have hinj : Function.Injective low := by
    intro i j hij
    apply Subtype.ext
    apply hf
    apply hcoord
    exact congrArg Fin.val hij
  have hcard := Fintype.card_le_of_injective low hinj
  simpa [Fintype.card_subtype] using hcard

/-! ## Factorization through translated monomials -/

/-- Translation by an integral center. -/
def translateUnivariatePolynomial (y : Fin 1 → ℤ)
    (f : MvPolynomial (Fin 1) ℤ) : MvPolynomial (Fin 1) ℤ :=
  MvPolynomial.aeval (fun i ↦ C (y i) + X i) f

theorem eval_translateUnivariatePolynomial (y z : Fin 1 → ℤ)
    (f : MvPolynomial (Fin 1) ℤ) :
    MvPolynomial.eval z (translateUnivariatePolynomial y f) =
      MvPolynomial.eval (fun i ↦ y i + z i) f := by
  change MvPolynomial.aeval z
      (MvPolynomial.aeval (fun i ↦ C (y i) + X i) f) =
    MvPolynomial.aeval (fun i ↦ y i + z i) f
  rw [MvPolynomial.comp_aeval_apply]
  apply DFunLike.congr_fun
  ext i
  simp

def translatedUnivariateCommonSupport {ι : Type*} [Fintype ι]
    (y : Fin 1 → ℤ) (F : ι → MvPolynomial (Fin 1) ℤ) :
    Finset (Fin 1 →₀ ℕ) :=
  Finset.univ.biUnion fun i ↦ (translateUnivariatePolynomial y (F i)).support

abbrev TranslatedUnivariateCommonSupportIndex
    {ι : Type*} [Fintype ι]
    (y : Fin 1 → ℤ) (F : ι → MvPolynomial (Fin 1) ℤ) :=
  {d : Fin 1 →₀ ℕ // d ∈ translatedUnivariateCommonSupport y F}

private theorem support_translateUnivariatePolynomial_subset_commonSupport
    {ι : Type*} [Fintype ι]
    (y : Fin 1 → ℤ) (F : ι → MvPolynomial (Fin 1) ℤ) (i : ι) :
    (translateUnivariatePolynomial y (F i)).support ⊆
      translatedUnivariateCommonSupport y F := by
  intro d hd
  rw [translatedUnivariateCommonSupport, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ _, hd⟩

def translatedUnivariateCommonSupportCoord
    {ι : Type*} [Fintype ι]
    (y : Fin 1 → ℤ) (F : ι → MvPolynomial (Fin 1) ℤ) :
    TranslatedUnivariateCommonSupportIndex y F → ℕ :=
  fun d ↦ d.val 0

theorem translatedUnivariateCommonSupportCoord_injective
    {ι : Type*} [Fintype ι]
    (y : Fin 1 → ℤ) (F : ι → MvPolynomial (Fin 1) ℤ) :
    Function.Injective (translatedUnivariateCommonSupportCoord y F) := by
  intro a b hab
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  fin_cases i
  exact hab

def translatedUnivariateCoefficientMatrix
    {ι : Type*} [Fintype ι]
    (y : Fin 1 → ℤ) (F : ι → MvPolynomial (Fin 1) ℤ) :
    Matrix ι (TranslatedUnivariateCommonSupportIndex y F) ℤ :=
  fun i d ↦ coeff d.val (translateUnivariatePolynomial y (F i))

def translatedUnivariateMonomialEvaluationMatrix
    {ι : Type*} [Fintype ι]
    (y : Fin 1 → ℤ) (F : ι → MvPolynomial (Fin 1) ℤ)
    (x : ι → Fin 1 → ℤ) :
    Matrix (TranslatedUnivariateCommonSupportIndex y F) ι ℤ :=
  fun d j ↦ (x j 0 - y 0) ^ d.val 0

theorem univariatePolynomialEvaluation_eq_coefficient_mul_monomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : Fin 1 → ℤ) (F : ι → MvPolynomial (Fin 1) ℤ)
    (x : ι → Fin 1 → ℤ) :
    Matrix.of (fun i j ↦ MvPolynomial.eval (x j) (F i)) =
      translatedUnivariateCoefficientMatrix y F *
        translatedUnivariateMonomialEvaluationMatrix y F x := by
  ext i j
  rw [Matrix.mul_apply]
  let z : Fin 1 → ℤ := fun q ↦ x j q - y q
  have hpoint : (fun q ↦ y q + z q) = x j := by
    funext q
    simp [z]
  change MvPolynomial.eval (x j) (F i) = _
  rw [← hpoint, ← eval_translateUnivariatePolynomial]
  rw [MvPolynomial.eval_eq']
  simp only [translatedUnivariateCoefficientMatrix,
    translatedUnivariateMonomialEvaluationMatrix, Fin.prod_univ_one]
  change
    (∑ d ∈ (translateUnivariatePolynomial y (F i)).support,
      coeff d (translateUnivariatePolynomial y (F i)) *
        (x j 0 - y 0) ^ d 0) =
      ∑ d : TranslatedUnivariateCommonSupportIndex y F,
        coeff d.val (translateUnivariatePolynomial y (F i)) *
          (x j 0 - y 0) ^ d.val 0
  rw [← Finset.sum_subtype (translatedUnivariateCommonSupport y F)
    (fun _ ↦ Iff.rfl)
    (fun d ↦ coeff d (translateUnivariatePolynomial y (F i)) *
      (x j 0 - y 0) ^ d 0)]
  apply Finset.sum_subset
  · exact support_translateUnivariatePolynomial_subset_commonSupport y F i
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul]

theorem pow_degree_dvd_translatedUnivariateMonomialEvaluation
    {ι : Type*} [Fintype ι]
    (p : ℤ) (y : Fin 1 → ℤ)
    (F : ι → MvPolynomial (Fin 1) ℤ)
    (x : ι → Fin 1 → ℤ)
    (hx : ∀ j i, p ∣ x j i - y i)
    (d : TranslatedUnivariateCommonSupportIndex y F) (j : ι) :
    p ^ translatedUnivariateCommonSupportCoord y F d ∣
      translatedUnivariateMonomialEvaluationMatrix y F x d j := by
  change p ^ d.val 0 ∣ (x j 0 - y 0) ^ d.val 0
  exact pow_dvd_pow_of_dvd (hx j 0) _

/-- Exact first-layer divisibility for an arbitrary family on a univariate
residue disc. -/
theorem arbitraryUnivariatePolynomialEvaluation_det_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℤ) (y : Fin 1 → ℤ)
    (x : ι → Fin 1 → ℤ)
    (F : ι → MvPolynomial (Fin 1) ℤ)
    (hx : ∀ j i, p ∣ x j i - y i) :
    p ^ affineLineJetWeight (Fintype.card ι) ∣
      (filteredPolynomialEvaluationMatrix F x).det := by
  rw [show filteredPolynomialEvaluationMatrix F x =
      Matrix.of (fun i j ↦ MvPolynomial.eval (x j) (F i)) by rfl]
  rw [univariatePolynomialEvaluation_eq_coefficient_mul_monomial]
  apply pow_dvd_det_rectangular_mul_of_injective_weight
    (translatedUnivariateCoefficientMatrix y F)
    (translatedUnivariateMonomialEvaluationMatrix y F x)
    p (translatedUnivariateCommonSupportCoord y F)
    (affineLineJetWeight (Fintype.card ι))
  · exact pow_degree_dvd_translatedUnivariateMonomialEvaluation
      p y F x hx
  · intro f hf
    exact affineLineJetWeight_le_sum_coord_comp
      (translatedUnivariateCommonSupportCoord y F)
      (translatedUnivariateCommonSupportCoord_injective y F) f hf

theorem arbitraryUnivariatePolynomialEvaluation_det_eq_zero_zmod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (a : ℕ)
    (ha : a ≤ affineLineJetWeight (Fintype.card ι))
    (y : Fin 1 → ℤ) (x : ι → Fin 1 → ℤ)
    (F : ι → MvPolynomial (Fin 1) ℤ)
    (hx : ∀ j i, (p : ℤ) ∣ x j i - y i) :
    (((filteredPolynomialEvaluationMatrix F x).det : ℤ) : ZMod (p ^ a)) =
      0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsmall : (p : ℤ) ^ a ∣
      (p : ℤ) ^ affineLineJetWeight (Fintype.card ι) :=
    pow_dvd_pow (p : ℤ) ha
  exact hsmall.trans
    (arbitraryUnivariatePolynomialEvaluation_det_dvd
      (p : ℤ) y x F hx)

end

end TranslatedDepthSeven
