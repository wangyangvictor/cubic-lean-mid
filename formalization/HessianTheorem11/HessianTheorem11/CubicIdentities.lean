import HessianTheorem11.Geometry

/-! Elementary identities in source §5, for the actual formal polynomial Hessian. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

variable {K : Type*} [CommRing K] {n : ℕ}

theorem partials_commute (F : MvPolynomial (Fin n) K) (i j : Fin n) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    by_cases hij : i = j
    · subst j; rfl
    · by_cases hik : k = i <;> by_cases hjk : k = j <;>
        simp_all [pderiv_X, Pi.single_apply, eq_comm] <;> ring

theorem hessian_symmetric (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    (hessian F x).transpose = hessian F x := by
  ext i j
  exact congrArg (eval x) (partials_commute F i j)

theorem euler_cubic {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (x : Fin n → K) : ∑ i, x i * gradient F x i = 3 * eval x F := by
  have h := congrArg (eval x) hF.sum_X_mul_pderiv
  simpa [gradient, nsmul_eq_mul] using h

theorem hessian_mulVec_self {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (x : Fin n → K) : (hessian F x).mulVec x = 2 • gradient F x := by
  ext i
  have hi : (pderiv i F).IsHomogeneous 2 := hF.pderiv
  have h := congrArg (eval x) hi.sum_X_mul_pderiv
  simpa [hessian, hessianPolynomial, gradient, Matrix.mulVec, dotProduct,
    nsmul_eq_mul, mul_comm] using h

theorem hessian_cubic_identity {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (x : Fin n → K) : dotProduct x ((hessian F x).mulVec x) = 6 * eval x F := by
  rw [hessian_mulVec_self hF]
  have he := euler_cubic hF x
  simp only [dotProduct, Pi.smul_apply, nsmul_eq_mul]
  calc
    ∑ i, x i * (2 * gradient F x i) = 2 * ∑ i, x i * gradient F x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 6 * eval x F := by rw [he]; ring

theorem singular_is_on_cubic {n : ℕ} (F : AnisotropicCubic n) :
    singularLocus F.polynomial ⊆ cubicLocus F.polynomial := by
  intro x hx
  have he := euler_cubic (geometric_homogeneous F.homogeneous) x
  have hg : gradient (geometricPolynomial F.polynomial) x = 0 := hx
  rw [hg] at he
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at he
  change eval x (geometricPolynomial F.polynomial) = 0
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

theorem anisotropic_hessian_zero_iff {n : ℕ} (F : AnisotropicCubic n)
    (x : Fin n → ℚ) : hessian F.polynomial x = 0 → x = 0 := by
  intro hx
  have h := hessian_cubic_identity F.homogeneous x
  rw [hx] at h
  have he : eval x F.polynomial = 0 := by
    have hz : 6 * eval x F.polynomial = 0 := by simpa using h.symm
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  exact F.anisotropic x he

end HessianTheorem11
