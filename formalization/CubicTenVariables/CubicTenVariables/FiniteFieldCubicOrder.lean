import CubicTenVariables.CubicSingularVariableElimination
import CubicTenVariables.Literature.Pleasants
import HessianTheorem11.PolynomialWeightTransport
import Mathlib.FieldTheory.ChevalleyWarning

/-!
# Finite-field cubics without smooth zeros use at most three linear forms

Chevalley--Warning supplies a nonzero zero in more than three variables.
The division-free singular-direction argument then eliminates one variable,
and induction gives an exact polynomial pullback in at most three linear
forms.  This proves the finite-residue-field ingredient of Pleasants's
Theorem 2 uniformly, including the fields of two and three elements.
The p-adic descent and compactness step are not asserted here.
-/

noncomputable section
namespace CubicTenVariables.FiniteFieldCubicOrder
open MvPolynomial HessianTheorem11 PolynomialRestriction PolynomialWeightTransport
open CubicSingularVariableElimination
open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K]

/-- The homogeneous Chevalley--Warning consequence used in the cubic descent. -/
theorem exists_nonzero_zero {n : ℕ} (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous 3) (hn : 3 < n) :
    ∃ z : Fin n → K, z ≠ 0 ∧ eval z F = 0 := by
  classical
  have hz : eval (0 : Fin n → K) F = 0 := by
    rw [eval_zero]
    exact hF.coeff_eq_zero (by simp)
  by_contra! h
  letI : Unique {z : Fin n → K // eval z F = 0} := {
    default := ⟨0, hz⟩
    uniq := fun z => Subtype.ext (by
      by_contra hne
      exact h z.1 hne z.2) }
  have hc := char_dvd_card_solutions (K := K) (ringChar K)
    (f := F) (by simpa using hF.totalDegree_le.trans_lt hn)
  have hp : (ringChar K).Prime := CharP.prime_ringChar K
  have hd : ringChar K ∣ 1 := by simpa only [Fintype.card_unique] using hc
  exact hp.not_dvd_one hd

/-- Absence of smooth zeros forces an actual representation by a homogeneous
cubic in at most three linear forms, independently of the characteristic. -/
theorem exists_linearForms_of_no_nonsingular_zero (n : ℕ)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hno : ¬ ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0) :
    ∃ (m : ℕ), m ≤ 3 ∧ ∃ (A : Matrix (Fin m) (Fin n) K)
      (G : MvPolynomial (Fin m) K), G.IsHomogeneous 3 ∧
        F = aeval (linearForms A) G := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 3
    · exact ⟨n, hn, 1, F, hF, (restrict_one F).symm⟩
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      obtain ⟨z, hz, hzero⟩ := exists_nonzero_zero F hF (by omega)
      obtain ⟨A, G, hG, hFG, hnoG⟩ :=
        exists_one_fewer_variables F hF hno z hz hzero
      obtain ⟨m, hm, B, H, hH, hGH⟩ := ih k (by omega) G hG hnoG
      refine ⟨m, hm, B * A, H, hH, ?_⟩
      rw [hFG, hGH]
      exact restrict_restrict B A H

/-- Literal order at least four supplies a smooth nonzero finite-field zero.
No residue-characteristic or field-cardinality exclusion is needed. -/
theorem exists_nonsingular_zero_of_linearOrderAtLeast {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (horder : Literature.LinearOrderAtLeast 4 F) :
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0 := by
  by_contra hno
  obtain ⟨m, hm, A, G, _, hFG⟩ := exists_linearForms_of_no_nonsingular_zero n F hF hno
  exact horder m (by omega) A G hFG

/-- First-partial version matching the actual nonsingularity condition. -/
theorem exists_partial_ne_zero_of_linearOrderAtLeast {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (horder : Literature.LinearOrderAtLeast 4 F) :
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧
      ∃ i : Fin n, eval x (pderiv i F) ≠ 0 := by
  classical
  obtain ⟨x, hx, hzero, hgrad⟩ := exists_nonsingular_zero_of_linearOrderAtLeast F hF horder
  refine ⟨x, hx, hzero, ?_⟩
  by_contra! h
  apply hgrad
  exact funext h

end CubicTenVariables.FiniteFieldCubicOrder
