import CubicTenVariables.CubicSingularVariableElimination
import CubicTenVariables.Literature.Pleasants
import HessianTheorem11.PolynomialWeightTransport

/-! The nonsingular version of the p-adic cubic theorem follows from its
nonzero-zero version by literal variable elimination. This avoids any
implicit identification of order with a Hessian or vertex dimension. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PadicCubicOrder
open MvPolynomial HessianTheorem11 PolynomialRestriction PolynomialWeightTransport
open CubicSingularVariableElimination
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

/-- Assuming nonzero zeros for cubics in at least ten variables, absence
of a smooth zero forces an exact representation using at most nine forms. -/
theorem exists_linearForms_of_no_nonsingular_zero
    (hlocal : ∀ (m : ℕ) (F : MvPolynomial (Fin m) ℚ_[p]),
      F.IsHomogeneous 3 → 10 ≤ m → ∃ x : Fin m → ℚ_[p], x≠0 ∧ eval x F=0)
    (n : ℕ) (F : MvPolynomial (Fin n) ℚ_[p]) (hF : F.IsHomogeneous 3)
    (hno : ¬ ∃ x : Fin n → ℚ_[p], x≠0 ∧ eval x F=0 ∧ gradient F x≠0) :
    ∃ m : ℕ, m ≤ 9 ∧ ∃ (A : Matrix (Fin m) (Fin n) ℚ_[p])
      (G : MvPolynomial (Fin m) ℚ_[p]), G.IsHomogeneous 3 ∧
        F=aeval (linearForms A) G := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 9
    · exact ⟨n,hn,1,F,hF,(restrict_one F).symm⟩
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      obtain ⟨z,hz,hzero⟩ := hlocal (k+1) F hF (by omega)
      obtain ⟨A,G,hG,hFG,hnoG⟩ := exists_one_fewer_variables F hF hno z hz hzero
      obtain ⟨m,hm,B,H,hH,hGH⟩ := ih k (by omega) G hG hnoG
      refine ⟨m,hm,B*A,H,hH,?_⟩
      rw [hFG,hGH]
      exact restrict_restrict B A H

/-- The literal linear-order hypothesis upgrades local existence to
a nonzero zero with an actual nonzero first partial. -/
theorem nonsingular_zero_of_nonzero_zero
    (hlocal : ∀ (m : ℕ) (F : MvPolynomial (Fin m) ℚ_[p]),
      F.IsHomogeneous 3 → 10 ≤ m → ∃ x : Fin m → ℚ_[p], x≠0 ∧ eval x F=0)
    {n : ℕ} (F : MvPolynomial (Fin n) ℚ_[p]) (hF : F.IsHomogeneous 3)
    (horder : Literature.LinearOrderAtLeast 10 F) :
    ∃ x : Fin n → ℚ_[p], x≠0 ∧ eval x F=0 ∧ ∃ i,eval x (pderiv i F)≠0 := by
  classical
  have hx : ∃ x : Fin n → ℚ_[p], x≠0 ∧ eval x F=0 ∧ gradient F x≠0 := by
    by_contra hno
    obtain ⟨m,hm,A,G,_,he⟩ := exists_linearForms_of_no_nonsingular_zero hlocal n F hF hno
    exact horder m (by omega) A G he
  obtain ⟨x,hx,hzero,hgrad⟩ := hx
  refine ⟨x,hx,hzero,?_⟩
  by_contra! he
  exact hgrad (funext he)

end CubicTenVariables.PadicCubicOrder
