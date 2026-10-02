import HessianTheorem11.QuadraticLowImage

/-! Equal actual polynomial image closures carry exactly the same
polynomial relations, including linear relations among coordinates. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module
variable {n m k : ℕ}

theorem aeval_eq_zero_iff_vanishes_image
    (P : Fin m → GeometricPolynomial n) (R : GeometricPolynomial m) :
    aeval P R = 0 ↔ R ∈ vanishingIdeal GeometricField (polynomialMap P '' Set.univ) := by
  constructor
  · intro h
    rintro _ ⟨x, _, rfl⟩
    have he := congrArg (eval x) h
    change aeval x (aeval P R) = aeval x 0 at he
    rw [comp_aeval_apply, map_zero] at he
    exact he
  · intro h
    apply MvPolynomial.funext
    intro x
    have he := h (polynomialMap P x) ⟨x, Set.mem_univ _, rfl⟩
    change aeval x (aeval P R) = aeval x 0
    rw [comp_aeval_apply, map_zero]
    exact he

theorem aeval_relation_iff_of_same_imageClosure
    (P : Fin m → GeometricPolynomial n) (Q : Fin m → GeometricPolynomial k)
    (h : geometricClosure (polynomialMap P '' Set.univ) =
      geometricClosure (polynomialMap Q '' Set.univ))
    (R : GeometricPolynomial m) : aeval P R = 0 ↔ aeval Q R = 0 := by
  rw [aeval_eq_zero_iff_vanishes_image, aeval_eq_zero_iff_vanishes_image,
    ← vanishingIdeal_geometricClosure (polynomialMap P '' Set.univ), h,
    vanishingIdeal_geometricClosure]

theorem linearIndependent_of_same_imageClosure
    (P : Fin m → GeometricPolynomial n) (Q : Fin m → GeometricPolynomial k)
    (h : geometricClosure (polynomialMap P '' Set.univ) =
      geometricClosure (polynomialMap Q '' Set.univ))
    (hP : LinearIndependent GeometricField P) : LinearIndependent GeometricField Q := by
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc
  apply hP c
  let R : GeometricPolynomial m := ∑ i, C (c i) * X i
  have hQR : aeval Q R = 0 := by
    simpa [R, MvPolynomial.smul_eq_C_mul] using hc
  have hPR := (aeval_relation_iff_of_same_imageClosure P Q h R).mpr hQR
  simpa [R, MvPolynomial.smul_eq_C_mul] using hPR

end HessianTheorem11
