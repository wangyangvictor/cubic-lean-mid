import CubicTenVariables.DegreeTwoSpan
import CubicTenVariables.DegreeSpanEightPlane

/-! The actual integral codimension-two plane used for degree-one and
 degree-two terminal components. No projective degree-span input is required. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.DegreeTwoEightPlane
open Matrix MvPolynomial TranslatedDepthSeven Module DegreeSpanEightPlane
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_integral_rows
    (I : Ideal (MvPolynomial (Fin 10) ℚ)) (r d : ℕ)
    (hprime : I.IsPrime)
    (hgeometric : (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree I r d)
    (hsmall : r + d ≤ 8) (hd : d ≤ 2) :
    ∃ A : Matrix (Fin 2) (Fin 10) ℤ,
      (A.map (Int.castRingHom ℚ)).rank = 2 ∧
      finrank ℚ (LinearMap.ker (A.map (Int.castRingHom ℚ)).mulVecLin) = 8 ∧
      ∀ j, map (Int.castRingHom ℚ) (rowPolynomial A j) ∈ I := by
  have hspan := DegreeTwoSpan.degree_le_two (N := 9) I hprime hgeometric hhom hdegree hd
  rw [← finrank_rationalLinearFormsInIdeal_eq_degreeOnePart I] at hspan
  have htwo : 2 ≤ finrank ℚ (rationalLinearFormsInIdeal I) := by omega
  obtain ⟨v, _, hrank, hrows⟩ :=
    exists_twoRow_rationalLinearFormMatrix_of_two_le_finrank I htwo
  let B := rationalLinearFormMatrix v
  obtain ⟨A, hker, hArows⟩ := exists_integral_rows_of_rational_rows I B hrows
  have hBdim : finrank ℚ (LinearMap.ker B.mulVecLin) = 8 := by
    have h := B.mulVecLin.finrank_range_add_finrank_ker
    change B.rank + finrank ℚ (LinearMap.ker B.mulVecLin) = _ at h
    rw [hrank] at h
    simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hAdim : finrank ℚ (LinearMap.ker (A.map (Int.castRingHom ℚ)).mulVecLin) = 8 := by
    rw [hker, hBdim]
  refine ⟨A, ?_, hAdim, hArows⟩
  have h := (A.map (Int.castRingHom ℚ)).mulVecLin.finrank_range_add_finrank_ker
  change (A.map (Int.castRingHom ℚ)).rank +
    finrank ℚ (LinearMap.ker (A.map (Int.castRingHom ℚ)).mulVecLin) = _ at h
  rw [hAdim] at h
  simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

end CubicTenVariables.DegreeTwoEightPlane
