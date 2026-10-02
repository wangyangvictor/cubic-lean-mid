import TranslatedDepthSeven.TangentPacketSpan
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# An auxiliary form from vanishing evaluation determinants

This is the final linear-algebra step of the determinant method.  If every
maximal minor of the evaluation matrix vanishes, its rows satisfy a
nontrivial rational relation.  Applied to forms which are linearly
independent modulo a homogeneous ideal, that relation produces a polynomial
which vanishes at every displayed point but does not belong to the ideal.

The statement is entirely concrete: there is no auxiliary-hypersurface
predicate and no geometric counting interface.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators
open MvPolynomial

/-- If every maximal minor of a rational matrix is zero, then its rows have a
nontrivial linear relation.  The assertion also covers the case where there
are fewer columns than rows. -/
theorem exists_nonzero_row_relation_of_all_maximal_minors_eq_zero
    {s S : ℕ} (A : Matrix (Fin s) (Fin S) ℚ)
    (hminor : ∀ cols : Fin s → Fin S, Function.Injective cols →
      (A.submatrix id cols).det = 0) :
    ∃ c : Fin s → ℚ, c ≠ 0 ∧
      ∀ j : Fin S, ∑ i, c i * A i j = 0 := by
  have hdependent : ¬ LinearIndependent ℚ A.row := by
    intro hindependent
    obtain ⟨cols, hcols, hdet⟩ :=
      TangentPacketSpan.exists_selectedMinor_ne_zero_of_linearIndependent_rows
        A hindependent
    exact hdet (hminor cols hcols)
  obtain ⟨c, hrelation, i, hi⟩ :=
    Fintype.not_linearIndependent_iff.mp hdependent
  refine ⟨c, ?_, ?_⟩
  · intro hc
    subst c
    exact hi (Pi.zero_apply i)
  · intro j
    have hj := congrFun hrelation j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.row_apply, Pi.zero_apply] using hj

/-- Vanishing maximal evaluation minors produce an actual auxiliary
polynomial.  Linear independence in the quotient proves that the polynomial
does not vanish identically on the closed subscheme defined by `I`. -/
theorem exists_auxiliaryPolynomial_of_all_evaluation_minors_eq_zero
    {σ : Type*} {s S : ℕ}
    (I : Ideal (MvPolynomial σ ℚ))
    (F : Fin s → MvPolynomial σ ℚ)
    (x : Fin S → σ → ℚ)
    (hF : LinearIndependent ℚ
      (fun i ↦ Ideal.Quotient.mk I (F i)))
    (hminor : ∀ cols : Fin s → Fin S, Function.Injective cols →
      ((Matrix.of (fun i j ↦ MvPolynomial.eval (x j) (F i))).submatrix
          id cols).det = 0) :
    ∃ c : Fin s → ℚ, c ≠ 0 ∧
      let G : MvPolynomial σ ℚ := ∑ i, c i • F i
      G ∉ I ∧ ∀ j : Fin S, MvPolynomial.eval (x j) G = 0 := by
  let A : Matrix (Fin s) (Fin S) ℚ :=
    Matrix.of (fun i j ↦ MvPolynomial.eval (x j) (F i))
  obtain ⟨c, hc, hrows⟩ :=
    exists_nonzero_row_relation_of_all_maximal_minors_eq_zero A (by
      intro cols hcols
      exact hminor cols hcols)
  refine ⟨c, hc, ?_, ?_⟩
  · intro hmem
    have hquotient :
        ∑ i, c i • Ideal.Quotient.mk I (F i) = 0 := by
      have hmk :
          (Ideal.Quotient.mkₐ ℚ I) (∑ i, c i • F i) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 hmem
      simpa only [map_sum, map_smul] using hmk
    have hczero : ∀ i, c i = 0 :=
      Fintype.linearIndependent_iff.mp hF c hquotient
    apply hc
    funext i
    exact hczero i
  · intro j
    simpa [Algebra.smul_def, A] using hrows j

/-- If the independent input forms all have degree `k`, the auxiliary
polynomial furnished by the same determinant argument is homogeneous of
degree `k`. -/
theorem exists_auxiliaryHomogeneousPolynomial_of_all_evaluation_minors_eq_zero
    {σ : Type*} {s S k : ℕ}
    (I : Ideal (MvPolynomial σ ℚ))
    (F : Fin s → MvPolynomial σ ℚ)
    (x : Fin S → σ → ℚ)
    (hF : LinearIndependent ℚ
      (fun i ↦ Ideal.Quotient.mk I (F i)))
    (hhomogeneous : ∀ i, (F i).IsHomogeneous k)
    (hminor : ∀ cols : Fin s → Fin S, Function.Injective cols →
      ((Matrix.of (fun i j ↦ MvPolynomial.eval (x j) (F i))).submatrix
          id cols).det = 0) :
    ∃ G : MvPolynomial σ ℚ,
      G.IsHomogeneous k ∧ G ∉ I ∧
        ∀ j : Fin S, MvPolynomial.eval (x j) G = 0 := by
  obtain ⟨c, hc, hnotmem, heval⟩ :=
    exists_auxiliaryPolynomial_of_all_evaluation_minors_eq_zero
      I F x hF hminor
  let G : MvPolynomial σ ℚ := ∑ i, c i • F i
  refine ⟨G, ?_, hnotmem, heval⟩
  simpa only [G, Algebra.smul_def] using
    (IsHomogeneous.sum Finset.univ
      (fun i ↦ MvPolynomial.C (c i) * F i) k
      (fun i _ ↦ (hhomogeneous i).C_mul (c i)))

end

end TranslatedDepthSeven
