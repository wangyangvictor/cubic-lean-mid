import CubicTenVariables.CubicSingularQuotient
import HessianTheorem11.LocalCubicNormalForm

/-!
# Division-free cubic smoothness upgrade over every field

The algebraic step in Pleasants, *Forms over p-adic fields* (1971), Lemma 2,
printed p. 294.  A singular zero with a nonzero quadratic Taylor polynomial
produces an actual nonsingular zero.  This includes characteristics two and
three: neither the Hessian nor division by a factorial detects that quadratic
polynomial in all characteristics.

This does not prove local solubility or that every finite-field cubic of order
at least four has a nonsingular zero.  The residual case below is exact
translation invariance in the supplied singular direction.
-/

noncomputable section
namespace CubicTenVariables.CubicSingularPointUpgrade
open MvPolynomial HessianTheorem11 CubicTaylorExpansion CubicSingularQuotient
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- At a singular cubic point, translating along that direction preserves
its actual directional derivative.  No characteristic restriction is used. -/
theorem directional_translate_singular
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (z : Fin n → K) (hz : gradient F z = 0) (u : Fin n → K) (t : K) :
    directional F (u + t • z) z = quadraticAt F z u := by
  have hgz : gradient F (t • z) = 0 := by
    ext i
    have he := LocalCubicNormalForm.homogeneous_eval₂_common_scalar
      (pderiv i F) hF.pderiv (RingHom.id K) z t
    have hi : eval z (pderiv i F) = 0 := congrFun hz i
    change eval (fun j => t * z j) (pderiv i F) = 0
    simpa only [eval₂_id, hi, mul_zero] using he
  have hpolar : dotProduct z ((hessian F u).mulVec z) = 0 := by
    change polarization F z z u = 0
    rw [polarization_rotate hF, polarization, hessian_mulVec_self hF, hz]
    simp
  simp only [directional, quadraticAt, gradient_add F hF, hgz, add_zero,
    dotProduct_add, Matrix.mulVec_smul, dotProduct_smul, hpolar, smul_eq_mul,
    mul_zero, add_zero]

/-- The nonzero quadratic Taylor term at an actual singular zero gives a
nonzero nonsingular zero, including over the fields with two or three elements. -/
theorem exists_nonsingular_zero_of_quadratic_ne_zero
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (z : Fin n → K) (hzero : eval z F = 0) (hsing : gradient F z = 0)
    (hQ : quadraticPolynomial F z ≠ 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0 := by
  classical
  obtain ⟨u, hu⟩ : ∃ u : Fin n → K, eval u (quadraticPolynomial F z) ≠ 0 := by
    by_contra! h
    exact hQ ((homogeneous_quadraticPolynomial F hF z).eq_zero_of_forall_eval_eq_zero_of_le_card h
        (Cardinal.two_le_iff.mpr ⟨0, 1, zero_ne_one⟩))
  rw [eval_quadraticPolynomial] at hu
  let t : K := -eval u F / quadraticAt F z u
  let x : Fin n → K := u + t • z
  have hlinear : t * quadraticAt F z u = -eval u F := div_mul_cancel₀ _ hu
  have hzero' : eval x F = 0 := by
    rw [show x = u + t • z from rfl, eval_cubic_add_smul F hF]
    have hquad : quadraticAt F u z = 0 := by simp [quadraticAt, directional, hsing]
    rw [hquad, hzero]
    change eval u F + t * quadraticAt F z u + _ + _ = 0
    rw [hlinear]
    ring
  have hdir : directional F x z = quadraticAt F z u :=
    directional_translate_singular F hF z hsing u t
  have hgrad : gradient F x ≠ 0 := by
    intro hx
    apply hu
    rw [← hdir]
    simp [directional, hx]
  refine ⟨x, ?_, hzero', hgrad⟩
  intro hx
  apply hgrad
  rw [hx]
  ext i
  change eval 0 (pderiv i F) = 0
  rw [eval_zero]
  exact hF.pderiv.coeff_eq_zero (by simp)

/-- If no nonsingular zero exists, every actual singular zero has zero
quadratic Taylor polynomial, not merely a zero Hessian. -/
theorem quadratic_eq_zero_of_no_nonsingular_zero
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hno : ¬ ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0)
    (z : Fin n → K) (hzero : eval z F = 0) (hsing : gradient F z = 0) :
    quadraticPolynomial F z = 0 := by
  by_contra hQ
  exact hno (exists_nonsingular_zero_of_quadratic_ne_zero F hF z hzero hsing hQ)

/-- The exceptional direction is literally invisible along every affine line.
This is the algebraic variable-elimination step; no local zero is asserted. -/
theorem eval_translate_of_no_nonsingular_zero
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hno : ¬ ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0)
    (z : Fin n → K) (hzero : eval z F = 0) (hsing : gradient F z = 0)
    (u : Fin n → K) (t : K) : eval (u + t • z) F = eval u F := by
  have hQ := quadratic_eq_zero_of_no_nonsingular_zero F hF hno z hzero hsing
  have hdir : directional F u z = 0 := by
    have he := congrArg (eval u) hQ
    simpa only [eval_quadraticPolynomial, map_zero] using he
  have hquad : quadraticAt F u z = 0 := by simp [quadraticAt, directional, hsing]
  rw [eval_cubic_add_smul F hF, hdir, hquad, hzero]
  ring

set_option maxHeartbeats 800000 in
/-- The residual direction can be eliminated at polynomial level, so this
is stronger than equality of polynomial functions over a finite field.
The translating scalar is itself an arbitrary polynomial. -/
theorem polynomial_translate_of_no_nonsingular_zero
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hno : ¬ ∃ x : Fin n → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0)
    (z : Fin n → K) (hzero : eval z F = 0) (hsing : gradient F z = 0)
    (t : MvPolynomial (Fin n) K) :
    eval₂ C (fun i => X i + t * C (z i)) F = F := by
  have hQ := quadratic_eq_zero_of_no_nonsingular_zero F hF hno z hzero hsing
  have hconst (G : MvPolynomial (Fin n) K) :
      eval₂ C (fun i => C (z i)) G = (C (eval z G) : MvPolynomial (Fin n) K) := by
    simpa only [RingHom.comp_id] using
      (eval₂_comp_left C (RingHom.id K) z G).symm
  have hgrad (i : Fin n) : eval z (pderiv i F) = 0 := congrFun hsing i
  have hlin : (∑ i, C (z i) * pderiv i F) = 0 := hQ
  have hquad : (∑ i, (X i : MvPolynomial (Fin n) K) *
      eval₂ C (fun j => C (z j)) (pderiv i F)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hconst, hgrad, map_zero, mul_zero]
  have he := eval₂_cubic_add_smul (S := MvPolynomial (Fin n) K) F hF
    (C : K →+* MvPolynomial (Fin n) K)
    (X : Fin n → MvPolynomial (Fin n) K) (fun i => C (z i)) t
  simp only [Pi.add_def, Pi.smul_def, smul_eq_mul, eval₂_eta, dotProduct] at he
  rw [hlin, hquad, hconst, hzero, map_zero] at he
  simpa only [mul_zero, add_zero] using he

end CubicTenVariables.CubicSingularPointUpgrade
