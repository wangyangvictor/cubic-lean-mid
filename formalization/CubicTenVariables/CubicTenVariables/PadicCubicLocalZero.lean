import CubicTenVariables.PadicCubicIteration
import CubicTenVariables.PadicCubicDescent
import CubicTenVariables.PadicSmoothResidueZero
import CubicTenVariables.PadicPolynomialIntegralMultiple

/-! Every cubic in at least ten variables over Qp has an actual nonzero
zero. Hensel lifting, finite-field variable elimination, exact integral
descent, determinant bounds, and compactness are all internal proofs.
No residue-characteristic exclusion or local-solubility input remains. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PadicCubicLocalZero
open MvPolynomial HessianTheorem11

variable {p n : ℕ} [Fact p.Prime]

/-- The integral-coefficient form of cubic local existence. -/
theorem exists_zero_integral (F : MvPolynomial (Fin n) ℤ_[p])
    (hF : F.IsHomogeneous 3) (hn : 10 ≤ n) :
    ∃ x : Fin n → ℚ_[p], x≠0 ∧ eval x (map PadicInt.Coe.ringHom F)=0 := by
  classical
  apply PadicCubicIteration.exists_zero_of_step F hF (by omega)
  intro G hG hno
  apply PadicCubicDescent.exists_step (by omega) G hG
  have hred := PadicSmoothResidueZero.reduction_no_smooth_zero G (by
    rintro ⟨x,hx,hzero⟩
    apply hx
    apply hno x
    simpa only [eval_map] using hzero)
  rintro ⟨z,hz,hzero,hgrad⟩
  apply hred
  refine ⟨z,hz,hzero,?_⟩
  by_contra! he
  exact hgrad (funext he)

/-- Literal local existence for arbitrary Qp coefficients and every prime. -/
theorem exists_zero (F : MvPolynomial (Fin n) ℚ_[p])
    (hF : F.IsHomogeneous 3) (hn : 10 ≤ n) :
    ∃ x : Fin n → ℚ_[p], x≠0 ∧ eval x F=0 := by
  obtain ⟨c,hc,G,hG,hmap⟩ :=
    PadicPolynomialIntegralMultiple.exists_homogeneous_integral_multiple F hF
  obtain ⟨x,hx,hzero⟩ := exists_zero_integral G hG hn
  have he : eval x (map (algebraMap ℤ_[p] ℚ_[p]) G)=0 := hzero
  rw [hmap,eval_mul,eval_C] at he
  exact ⟨x,hx,(mul_eq_zero.mp he).resolve_left hc⟩

end CubicTenVariables.PadicCubicLocalZero
