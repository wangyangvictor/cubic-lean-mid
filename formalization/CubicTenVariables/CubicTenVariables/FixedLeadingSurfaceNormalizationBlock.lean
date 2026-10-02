import TranslatedDepthSeven.NormalizationSurfaceBlockEvaluation
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Coordinate normalization blocks independent of lower coefficients

For a hypersurface whose degree in the last variable is `d`, use the fixed
forms `L_j = X_j` and `G_i = X_3^i X_0^(d-1-i)`. The auxiliary forms have
common degree `d-1` and evaluation constant one. Independence modulo the
hypersurface is an elementary degree obstruction, with no normalization,
prime-ideal, or coefficient-height assumption.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceNormalizationBlock
open MvPolynomial TranslatedDepthSeven
open scoped BigOperators

/-- A pure power in the leading part forces the corresponding variable
degree. Only a total-degree upper bound is required. -/
theorem degreeOf_eq_of_pure_power_coeff_ne_zero
    {σ K : Type*} [Field K] (j : σ) {d : ℕ} {F : MvPolynomial σ K}
    (htotal : F.totalDegree ≤ d)
    (hcoeff : F.coeff (Finsupp.single j d) ≠ 0) :
    F.degreeOf j = d := by
  classical
  apply Nat.le_antisymm ((degreeOf_le_totalDegree F j).trans htotal)
  simpa using monomial_le_degreeOf j (mem_support_iff.mpr hcoeff)

/-- Fixing a projective leading form with a nonzero pure-power coefficient
fixes the variable degree, uniformly over all nonzero scalars and lower
coefficients. -/
theorem degreeOf_eq_of_scalar_leading_form
    {σ K : Type*} [Field K] (j : σ) {d : ℕ}
    {F H : MvPolynomial σ K} {c : K}
    (htotal : F.totalDegree ≤ d) (hc : c ≠ 0)
    (htop : homogeneousComponent d F = C c * H)
    (hcoeff : H.coeff (Finsupp.single j d) ≠ 0) :
    F.degreeOf j = d := by
  classical
  apply degreeOf_eq_of_pure_power_coeff_ne_zero j htotal
  have he := congrArg (MvPolynomial.coeff (Finsupp.single j d)) htop
  have he' : F.coeff (Finsupp.single j d) = c * H.coeff (Finsupp.single j d) := by
    simpa [MvPolynomial.coeff_homogeneousComponent] using he
  rw [he']
  exact mul_ne_zero hc hcoeff

/-- A nonzero multiple cannot have smaller degree in a chosen variable. -/
theorem degreeOf_le_of_dvd {σ : Type*} {K : Type*} [Field K]
    (j : σ) {F P : MvPolynomial σ K} (hP : P ≠ 0) (hdiv : F ∣ P) :
    F.degreeOf j ≤ P.degreeOf j := by
  classical
  let e : MvPolynomial σ K ≃ₐ[K] Polynomial (MvPolynomial {i // i ≠ j} K) :=
    (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe j).symm).trans
      (MvPolynomial.optionEquivLeft K {i // i ≠ j})
  have heP : e P ≠ 0 := fun hz => hP (e.injective (by simpa using hz))
  have hediv : e F ∣ e P := map_dvd e.toRingHom hdiv
  simpa only [MvPolynomial.degreeOf_eq_natDegree, e, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply] using Polynomial.natDegree_le_of_dvd hediv heP

/-- Every class represented by a lower-last-degree polynomial is faithful. -/
theorem eq_zero_of_mem_span_singleton_of_degreeOf_lt
    {σ : Type*} {K : Type*} [Field K] (j : σ)
    {F P : MvPolynomial σ K}
    (hmem : P ∈ Ideal.span {F}) (hdegree : P.degreeOf j < F.degreeOf j) :
    P = 0 := by
  by_contra hP
  exact hdegree.not_ge (degreeOf_le_of_dvd j hP (Ideal.mem_span_singleton.mp hmem))

/-- Distinct monomials of last-variable degree below that of the defining
equation remain linearly independent in its literal quotient. -/
theorem linearIndependent_quotient_monomials
    {σ ι K : Type*} [Field K] [Fintype ι]
    (j : σ) (F : MvPolynomial σ K) (e : ι → σ →₀ ℕ)
    (he : Function.Injective e) (hdegree : ∀ i, e i j < F.degreeOf j) :
    LinearIndependent K (fun i => Ideal.Quotient.mk (Ideal.span {F})
      (MvPolynomial.monomial (e i) (1 : K))) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => exact linearIndependent_empty_type
  | inr h =>
    letI : Nonempty ι := h
    have hpos : 0 < F.degreeOf j := Nat.zero_lt_of_lt (hdegree (Classical.choice h))
    have hLI : LinearIndependent K (fun i => MvPolynomial.monomial (e i) (1 : K)) := by
      simpa using (MvPolynomial.basisMonomials σ K).linearIndependent.comp e he
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply Fintype.linearIndependent_iff.mp hLI c
    have hmem : (∑ i, c i • MvPolynomial.monomial (e i) (1 : K)) ∈
        Ideal.span {F} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sum, map_smul] using hc
    apply eq_zero_of_mem_span_singleton_of_degreeOf_lt j hmem
    refine (degreeOf_sum_le j Finset.univ _).trans_lt ?_
    apply Finset.sup_lt_iff hpos |>.mpr
    intro i _
    rw [MvPolynomial.smul_monomial]
    by_cases hi : c i = 0
    · simpa [hi] using hpos
    · simpa [MvPolynomial.degreeOf_monomial_eq, hi] using hdegree i

def coordinateForms : Fin 3 → MvPolynomial (Fin 4) ℤ :=
  fun i => X i.castSucc

def auxiliaryForms (d : ℕ) : Fin d → MvPolynomial (Fin 4) ℤ :=
  fun i => X 3 ^ i.val * X 0 ^ (d - 1 - i.val)

theorem coordinateForms_first : coordinateForms 0 = X 0 := rfl

theorem coordinateForms_isHomogeneous (i : Fin 3) :
    (coordinateForms i).IsHomogeneous 1 := isHomogeneous_X _ _

theorem coordinateForms_eval_natAbs_le (B : ℕ) (y : Fin 4 → ℤ)
    (hy : ∀ j, (y j).natAbs ≤ B) (i : Fin 3) :
    (MvPolynomial.eval y (coordinateForms i)).natAbs ≤ B := by
  simpa only [coordinateForms, eval_X] using hy i.castSucc

theorem auxiliaryForms_isHomogeneous (d : ℕ) (i : Fin d) :
    (auxiliaryForms d i).IsHomogeneous (d - 1) := by
  have hi : i.val ≤ d - 1 := by omega
  have h := ((isHomogeneous_X ℤ (3 : Fin 4)).pow i.val).mul
    ((isHomogeneous_X ℤ (0 : Fin 4)).pow (d - 1 - i.val))
  simpa only [auxiliaryForms, one_mul, Nat.add_sub_of_le hi] using h

theorem auxiliaryForms_eval_natAbs_le (d B : ℕ) (y : Fin 4 → ℤ)
    (hy : ∀ j, (y j).natAbs ≤ B) (i : Fin d) :
    (MvPolynomial.eval y (auxiliaryForms d i)).natAbs ≤ B ^ (d - 1) := by
  have hi : i.val ≤ d - 1 := by omega
  simp only [auxiliaryForms, map_mul, map_pow, eval_X, Int.natAbs_mul, Int.natAbs_pow]
  calc
    (y 3).natAbs ^ i.val * (y 0).natAbs ^ (d - 1 - i.val) ≤
        B ^ i.val * B ^ (d - 1 - i.val) := Nat.mul_le_mul
          (Nat.pow_le_pow_left (hy 3) _) (Nat.pow_le_pow_left (hy 0) _)
    _ = B ^ (d - 1) := by rw [← pow_add, Nat.add_sub_of_le hi]

def blockExponent (d k : ℕ) (p : Fin d × AffinePlaneMonomialIndex k) :
    Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![d - 1 - p.1.val + affinePlaneMonomialExponent k p.2 0,
      affinePlaneMonomialExponent k p.2 1,
      affinePlaneMonomialExponent k p.2 2, p.1.val]

theorem blockExponent_last (d k : ℕ) (p : Fin d × AffinePlaneMonomialIndex k) :
    blockExponent d k p 3 = p.1.val := by simp [blockExponent]

theorem blockExponent_injective (d k : ℕ) : Function.Injective (blockExponent d k) := by
  intro p q hpq
  have hi : p.1 = q.1 := Fin.ext (by
    simpa [blockExponent] using congrArg (fun e => e 3) hpq)
  apply Prod.ext hi
  apply affinePlaneMonomialExponent_injective k
  ext j
  fin_cases j
  · have he := congrArg (fun e => e 0) hpq
    simp only [blockExponent, Finsupp.equivFunOnFinite_symm_apply_toFun,
      Matrix.cons_val_zero] at he
    rw [hi] at he
    exact Nat.add_left_cancel he
  · simpa [blockExponent] using congrArg (fun e => e 1) hpq
  · simpa [blockExponent] using congrArg (fun e => e 2) hpq

theorem blockForm_eq_monomial (d k : ℕ)
    (p : Fin d × AffinePlaneMonomialIndex k) :
    normalizationSurfaceBlockForm coordinateForms (auxiliaryForms d) k p =
      MvPolynomial.monomial (blockExponent d k p) (1 : ℤ) := by
  unfold normalizationSurfaceBlockForm affinePlaneHomogeneousMonomial
  rw [MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_three]
    simp only [coordinateForms, auxiliaryForms]
    simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
    apply congrArg (fun e : Fin 4 →₀ ℕ => MvPolynomial.monomial e (1 : ℤ))
    ext j
    fin_cases j <;> simp [blockExponent]
  · intro i
    simp

/-- The same integer monomial block works for every defining equation with
the displayed last-variable degree, uniformly in all lower coefficients. -/
theorem linearIndependent_fixed_coordinate_block
    (d k : ℕ) (F : MvPolynomial (Fin 4) ℚ) (hdegree : F.degreeOf 3 = d) :
    LinearIndependent ℚ (fun p : Fin d × AffinePlaneMonomialIndex k =>
      Ideal.Quotient.mk (Ideal.span {F})
        (MvPolynomial.map (Int.castRingHom ℚ)
          (normalizationSurfaceBlockForm coordinateForms (auxiliaryForms d) k p))) := by
  simp only [blockForm_eq_monomial, MvPolynomial.map_monomial, map_one]
  apply linearIndependent_quotient_monomials 3 F _ (blockExponent_injective d k)
  intro p
  simpa only [blockExponent_last, hdegree] using p.1.isLt

end CubicTenVariables.FixedLeadingSurfaceNormalizationBlock
