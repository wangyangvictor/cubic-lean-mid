import HessianTheorem11.CubicIdentities

/-! The Hessian of a cubic is a linear matrix pencil. This file proves that
fact from formal derivatives, and proves rational injectivity using anisotropy. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

variable {K : Type*} [CommRing K] {n : ℕ}

theorem homogeneous_zero_eq_constant {p : MvPolynomial (Fin n) K}
    (hp : p.IsHomogeneous 0) : p = C (coeff 0 p) := by
  exact totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (Fin n)).mpr hp)

theorem homogeneous_one_expansion {p : MvPolynomial (Fin n) K}
    (hp : p.IsHomogeneous 1) :
    p = ∑ i, X i * C (coeff 0 (pderiv i p)) := by
  have hc (i : Fin n) : pderiv i p = C (coeff 0 (pderiv i p)) :=
    homogeneous_zero_eq_constant hp.pderiv
  calc
    p = ∑ i, X i * pderiv i p := by
      simpa only [one_smul] using hp.sum_X_mul_pderiv.symm
    _ = ∑ i, X i * C (coeff 0 (pderiv i p)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (X i * ·) (hc i)

theorem eval_homogeneous_one {p : MvPolynomial (Fin n) K}
    (hp : p.IsHomogeneous 1) (x : Fin n → K) :
    eval x p = ∑ i, x i * coeff 0 (pderiv i p) := by
  have he := congrArg (eval x) (homogeneous_one_expansion hp)
  simpa using he

theorem eval_add_homogeneous_one {p : MvPolynomial (Fin n) K}
    (hp : p.IsHomogeneous 1) (x y : Fin n → K) :
    eval (x + y) p = eval x p + eval y p := by
  simp only [eval_homogeneous_one hp, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem eval_smul_homogeneous_one {p : MvPolynomial (Fin n) K}
    (hp : p.IsHomogeneous 1) (a : K) (x : Fin n → K) :
    eval (a • x) p = a * eval x p := by
  simp only [eval_homogeneous_one hp, Pi.smul_apply, smul_eq_mul,
    mul_assoc, Finset.mul_sum]

theorem hessian_entry_homogeneous_one {F : MvPolynomial (Fin n) K}
    (hF : F.IsHomogeneous 3) (i j : Fin n) :
    (hessianPolynomial F i j).IsHomogeneous 1 :=
  hF.pderiv.pderiv

def hessianLinearMap (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) :
    (Fin n → K) →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun := hessian F
  map_add' x y := by
    ext i j
    exact eval_add_homogeneous_one (hessian_entry_homogeneous_one hF i j) x y
  map_smul' a x := by
    ext i j
    exact eval_smul_homogeneous_one (hessian_entry_homogeneous_one hF i j) a x

theorem hessian_zero {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3) :
    hessian F 0 = 0 := (hessianLinearMap F hF).map_zero

theorem hessian_add {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (x y : Fin n → K) : hessian F (x + y) = hessian F x + hessian F y :=
  (hessianLinearMap F hF).map_add x y

theorem hessian_smul {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (a : K) (x : Fin n → K) : hessian F (a • x) = a • hessian F x :=
  (hessianLinearMap F hF).map_smul a x

theorem hessian_sub {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (x y : Fin n → K) : hessian F (x - y) = hessian F x - hessian F y :=
  (hessianLinearMap F hF).map_sub x y

/-- Source §9's Hessian-map injectivity over the rational field, proved
directly without assuming a nonzero Hessian determinant. -/
theorem rational_hessian_injective {n : ℕ} (F : AnisotropicCubic n) :
    Function.Injective (hessian F.polynomial) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply anisotropic_hessian_zero_iff F
  rw [hessian_sub F.homogeneous, hxy, sub_self]

/-- The coefficient tensor makes the linearity of every Hessian entry explicit. -/
theorem hessian_entry_expansion {F : MvPolynomial (Fin n) K}
    (hF : F.IsHomogeneous 3) (x : Fin n → K) (i j : Fin n) :
    hessian F x i j = ∑ l, x l * coeff 0 (pderiv l (pderiv j (pderiv i F))) :=
  eval_homogeneous_one (hessian_entry_homogeneous_one hF i j) x

theorem hessian_polarization {F : MvPolynomial (Fin n) K}
    (hF : F.IsHomogeneous 3) (x y : Fin n → K) :
    (hessian F x).mulVec y = (hessian F y).mulVec x := by
  ext i
  simp only [Matrix.mulVec, dotProduct, hessian_entry_expansion hF,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  rw [partials_commute (pderiv i F) l j]
  ring

end HessianTheorem11
