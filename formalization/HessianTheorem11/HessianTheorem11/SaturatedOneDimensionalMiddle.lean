import HessianTheorem11.SaturatedCubicResolvent
import HessianTheorem11.BasisWeightSum

/-! The one-dimensional middle block forces the mixed cubic tensor to
vanish, providing the codimension-three saturated incidence obstruction. -/
noncomputable section
namespace HessianTheorem11
open Matrix MvPolynomial Module
namespace CoisotropicBasis.Data
variable {n m d : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d 1)

theorem mixedGram_zero_of_moment_zero (a : GeometricPoint n)
    (hm : D.resolventMoment a 0 = 0) : D.mixedGramAt a = 0 := by
  have hB : (D.middleGram⁻¹).det ≠ 0 := by
    exact isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_right_inverse
      (Matrix.nonsing_inv_mul D.middleGram (isUnit_iff_ne_zero.mpr D.middleGram_det_ne_zero)))
  have h00 : D.middleGram⁻¹ 0 0 ≠ 0 := by
    simpa only [Matrix.det_unique] using hB
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  have h := congrFun (congrFun hm i) i
  simp only [resolventMoment, pow_zero, Matrix.mul_one, Matrix.zero_apply,
    Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply] at h
  have he : D.mixedGramAt a i 0 = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact (mul_eq_zero.mp h).resolve_right h00
    · exact h
  exact he

end CoisotropicBasis.Data
end HessianTheorem11
