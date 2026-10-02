import TranslatedDepthSeven.StrictRankAtMostSixStandardAG
import CubicTenVariables.RationalCodimensionTwoCoordinates

/-! The degree--span consequence needed for the two low-degree cones in
ten variables. The sole geometric input is the existing, explicit
`StandardAG.ProjectiveDegreeSpanInequality ℚ`. Its degree is defined by
the Hilbert polynomial and its dimension by the quotient's Krull dimension.

Reference for the input: J. Harris, *Algebraic Geometry: A First Course*,
GTM 133, Lecture 18, Corollary 18.12 (the chapter "Degree", pp. 224--238),
https://doi.org/10.1007/978-1-4757-2189-8_18 . The input is not proved here.
Everything extracting integral equations and an eight-dimensional plane
from that inequality is proved below. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.DegreeSpanEightPlane

open Matrix MvPolynomial TranslatedDepthSeven Module

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal linear polynomial associated to a matrix row. -/
def rowPolynomial {m n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin m) (Fin n) R) (j : Fin m) : MvPolynomial (Fin n) R :=
  ∑ i, C (A j i) * X i

@[simp] theorem map_rowPolynomial {m n : ℕ} {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin m) (Fin n) R) (j : Fin m) :
    map f (rowPolynomial A j) = rowPolynomial (A.map f) j := by
  simp [rowPolynomial]

@[simp] theorem eval_rowPolynomial {m n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin m) (Fin n) R) (j : Fin m) (x : Fin n → R) :
    eval x (rowPolynomial A j) = A.mulVec x j := by
  simp [rowPolynomial, Matrix.mulVec, dotProduct]

/-- Clearing a common denominator retains the row ideal and its kernel. -/
theorem exists_integral_rows_of_rational_rows {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ))
    (A : Matrix (Fin 2) (Fin n) ℚ)
    (hrows : ∀ j, rowPolynomial A j ∈ I) :
    ∃ B : Matrix (Fin 2) (Fin n) ℤ,
      LinearMap.ker (B.map (Int.castRingHom ℚ)).mulVecLin =
        LinearMap.ker A.mulVecLin ∧
      ∀ j, map (Int.castRingHom ℚ) (rowPolynomial B j) ∈ I := by
  have hden : (A.den : ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
  have hnum : A.num.map (Int.castRingHom ℚ) = (A.den : ℚ) • A := by
    ext i j
    exact (div_eq_iff hden).mp (A.num_div_den i j) |>.trans (mul_comm _ _)
  refine ⟨A.num, ?_, ?_⟩
  · ext x
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, hnum, Matrix.smul_mulVec]
    exact smul_eq_zero.trans (or_iff_right hden)
  · intro j
    rw [map_rowPolynomial, hnum]
    have hrow : rowPolynomial ((A.den : ℚ) • A) j =
        C (A.den : ℚ) * rowPolynomial A j := by
      simp [rowPolynomial, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [hrow]
    exact I.mul_mem_left _ (hrows j)

/-- The degree--span inequality gives a literal integral matrix whose
kernel is an eight-dimensional rational plane and whose equations belong
to the actual cone ideal. Here `r` is projective dimension, so the affine
cone has dimension `r + 1`. -/
theorem exists_integral_rows
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (I : Ideal (MvPolynomial (Fin 10) ℚ)) (r d : ℕ)
    (hprime : I.IsPrime)
    (hgeometric : (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree I r d)
    (hsmall : r + d ≤ 8) :
    ∃ A : Matrix (Fin 2) (Fin 10) ℤ,
      (A.map (Int.castRingHom ℚ)).rank = 2 ∧
      finrank ℚ (LinearMap.ker (A.map (Int.castRingHom ℚ)).mulVecLin) = 8 ∧
      ∀ j, map (Int.castRingHom ℚ) (rowPolynomial A j) ∈ I := by
  have hspan := degreeSpan 9 r d I hprime hgeometric hhom hdegree
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

/-- Every geometric point of the ideal lies in the plane after any
extension of the coefficient field. -/
theorem mulVec_eq_zero_of_ideal_zero {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ))
    (A : Matrix (Fin 2) (Fin n) ℤ)
    (hrows : ∀ j, map (Int.castRingHom ℚ) (rowPolynomial A j) ∈ I)
    {K : Type*} [Field K] [Algebra ℚ K] (x : Fin n → K)
    (hx : ∀ f ∈ I, eval₂ (algebraMap ℚ K) x f = 0) :
    (A.map (Int.castRingHom K)).mulVec x = 0 := by
  ext j
  have h := hx _ (hrows j)
  rw [map_rowPolynomial] at h
  have hcast (z : ℤ) : eval₂ (algebraMap ℚ K) x
      (z : MvPolynomial (Fin n) ℚ) = (z : K) :=
    map_intCast (eval₂Hom (algebraMap ℚ K) x) z
  simpa only [rowPolynomial, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X,
    Matrix.map_apply, Int.coe_castRingHom, map_intCast, Matrix.mulVec, dotProduct,
    Pi.zero_apply, hcast] using h

/-- The dimension-six, degree-at-most-three cone case. -/
theorem exists_integral_rows_dim_six
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (I : Ideal (MvPolynomial (Fin 10) ℚ)) (d : ℕ)
    (hprime : I.IsPrime)
    (hgeometric : (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree I 5 d) (hd : d ≤ 3) :
    ∃ A : Matrix (Fin 2) (Fin 10) ℤ,
      (A.map (Int.castRingHom ℚ)).rank = 2 ∧
      finrank ℚ (LinearMap.ker (A.map (Int.castRingHom ℚ)).mulVecLin) = 8 ∧
      ∀ j, map (Int.castRingHom ℚ) (rowPolynomial A j) ∈ I :=
  exists_integral_rows degreeSpan I 5 d hprime hgeometric hhom hdegree (by omega)

/-- The dimension-five, degree-at-most-four cone case. -/
theorem exists_integral_rows_dim_five
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (I : Ideal (MvPolynomial (Fin 10) ℚ)) (d : ℕ)
    (hprime : I.IsPrime)
    (hgeometric : (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree I 4 d) (hd : d ≤ 4) :
    ∃ A : Matrix (Fin 2) (Fin 10) ℤ,
      (A.map (Int.castRingHom ℚ)).rank = 2 ∧
      finrank ℚ (LinearMap.ker (A.map (Int.castRingHom ℚ)).mulVecLin) = 8 ∧
      ∀ j, map (Int.castRingHom ℚ) (rowPolynomial A j) ∈ I :=
  exists_integral_rows degreeSpan I 4 d hprime hgeometric hhom hdegree (by omega)

end CubicTenVariables.DegreeSpanEightPlane
