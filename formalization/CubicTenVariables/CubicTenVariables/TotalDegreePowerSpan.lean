import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Finite spanning from coordinate-power relations with lower total degree

If each X_i^d_i is congruent modulo an ideal to a polynomial of total degree
strictly less than d_i, the quotient is spanned by monomials with every
coordinate exponent less than d_i. The proof uses total-degree induction;
no independence, properness, geometric or point-counting premise is needed.
-/

noncomputable section
namespace CubicTenVariables.TotalDegreePowerSpan
open MvPolynomial
open scoped BigOperators

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Exponent vector for the finite box of coordinate exponents. -/
def boundedExponent (d : Fin n → ℕ) (b : ∀ i, Fin (d i)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (b i).val)

@[simp] theorem boundedExponent_apply (d : Fin n → ℕ) (b : ∀ i, Fin (d i))
    (i : Fin n) : boundedExponent d b i = (b i).val := by
  simp [boundedExponent]

/-- The actual residue of a monomial in the coordinate exponent box. -/
def boundedMonomial (I : Ideal (MvPolynomial (Fin n) R))
    (d : Fin n → ℕ) (b : ∀ i, Fin (d i)) : MvPolynomial (Fin n) R ⧸ I :=
  Ideal.Quotient.mk I (monomial (boundedExponent d b) 1)

/-- Reduction by a coordinate-power relation strictly lowers total degree,
so the bounded monomials span the entire quotient over the coefficient ring. -/
theorem span_boundedMonomials_eq_top
    (I : Ideal (MvPolynomial (Fin n) R)) (d : Fin n → ℕ)
    (g : Fin n → MvPolynomial (Fin n) R)
    (hrel : ∀ i, X i ^ d i - g i ∈ I)
    (hdeg : ∀ i, (g i).totalDegree < d i) :
    Submodule.span R (Set.range (boundedMonomial I d)) = ⊤ := by
  classical
  let q := Ideal.Quotient.mkₐ R I
  let S := Submodule.span R (Set.range (boundedMonomial I d))
  have hbounded (e : Fin n →₀ ℕ) (he : ∀ i, e i < d i) (c : R) :
      q (monomial e c) ∈ S := by
    let b : ∀ i, Fin (d i) := fun i => ⟨e i, he i⟩
    have hb : boundedExponent d b = e := by ext i; simp [b]
    have hm : q (monomial e 1) ∈ S :=
      Submodule.subset_span ⟨b, by simp only [boundedMonomial, hb]; rfl⟩
    simpa only [← map_smul, smul_monomial, smul_eq_mul, mul_one] using S.smul_mem c hm
  have hmon : ∀ (e : Fin n →₀ ℕ) (c : R), q (monomial e c) ∈ S := by
    intro e
    refine ((measure (fun e : Fin n →₀ ℕ => e.degree)).wf).induction
      (C := fun e => ∀ c : R, q (monomial e c) ∈ S) e ?_
    intro e ih c
    by_cases he : ∀ i, e i < d i
    · exact hbounded e he c
    obtain ⟨i, hi⟩ : ∃ i, d i ≤ e i := by push_neg at he; exact he
    let e' := e - Finsupp.single i (d i)
    have hsplit : e' + Finsupp.single i (d i) = e :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
    have hdegree : e'.degree + d i = e.degree := by
      rw [← Finsupp.degree_single i (d i), ← map_add, hsplit]
    have hfactor : (monomial e c : MvPolynomial (Fin n) R) =
        monomial e' c * X i ^ d i := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, hsplit]
    have hq : q (X i ^ d i) = q (g i) := by
      exact Ideal.Quotient.eq.mpr (hrel i)
    rw [hfactor, map_mul, hq, ← map_mul]
    let P : MvPolynomial (Fin n) R := monomial e' c * g i
    have hP : P.totalDegree < e.degree := by
      have hm := totalDegree_monomial_le e' c
      have hmul := totalDegree_mul (monomial e' c) (g i)
      have hgi := hdeg i
      change (monomial e' c * g i).totalDegree < e.degree
      change (monomial e' c).totalDegree ≤ e'.degree at hm
      omega
    change q P ∈ S
    rw [P.as_sum, map_sum]
    apply S.sum_mem
    intro f hf
    exact ih f ((le_totalDegree hf).trans_lt hP) _
  apply top_unique
  intro x _
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  change q P ∈ S
  rw [P.as_sum, map_sum]
  exact S.sum_mem (fun e _ => hmon e _)

/-- The quotient is a finite module over any commutative coefficient ring. -/
theorem finite_quotient
    (I : Ideal (MvPolynomial (Fin n) R)) (d : Fin n → ℕ)
    (g : Fin n → MvPolynomial (Fin n) R)
    (hrel : ∀ i, X i ^ d i - g i ∈ I)
    (hdeg : ∀ i, (g i).totalDegree < d i) :
    Module.Finite R (MvPolynomial (Fin n) R ⧸ I) := by
  classical
  apply Module.finite_def.mpr
  rw [← span_boundedMonomials_eq_top I d g hrel hdeg]
  exact Submodule.fg_span (Set.finite_range _)

/-- Over a field, the dimension is at most the number of monomials in
the coordinate exponent box. The ideal may be arbitrary, including top. -/
theorem finrank_quotient_le {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (d : Fin n → ℕ)
    (g : Fin n → MvPolynomial (Fin n) K)
    (hrel : ∀ i, X i ^ d i - g i ∈ I)
    (hdeg : ∀ i, (g i).totalDegree < d i) :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ I) ≤ ∏ i, d i := by
  classical
  have h := finrank_le_of_span_eq_top (span_boundedMonomials_eq_top I d g hrel hdeg)
  simpa only [Fintype.card_pi, Fintype.card_fin] using h

end CubicTenVariables.TotalDegreePowerSpan
