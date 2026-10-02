import HessianTheorem11.ReducedBigCellMatrices
import HessianTheorem11.ReducedWeightCurve
import HessianTheorem11.ReducedOrbitCoordinates

/-! Proof of the former specialized orbit/big-cell factorization from the
ordinary matrix big cell and openness of orbit maps. The polynomial curve,
its specialization, coefficient continuity and all conjugations are proved.
The two general textbook inputs remain explicit and are not asserted proved. -/
noncomputable section
namespace HessianTheorem11.ReducedBigCell
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
open ReducedWeightCurve ReducedOrbitCoordinates
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem slOrbit_trans {F G H : MvPolynomial (Fin n) K}
    (hHG : H ∈ slOrbit G) (hGF : G ∈ slOrbit F) : H ∈ slOrbit F := by
  obtain ⟨A,hA,rfl⟩ := hHG
  obtain ⟨B,hB,rfl⟩ := hGF
  exact ⟨B*A, by rw [Matrix.det_mul, hB, hA, mul_one], restrict_restrict B A F⟩

theorem slOrbit_symm {F G : MvPolynomial (Fin n) K}
    (hGF : G ∈ slOrbit F) : F ∈ slOrbit G := by
  obtain ⟨A,hA,rfl⟩ := hGF
  have hu : IsUnit A.det := by rw [hA]; exact isUnit_one
  refine ⟨A⁻¹, ?_, ?_⟩
  · have h : A.det * A⁻¹.det = 1 := by
      rw [← Matrix.det_mul, Matrix.mul_nonsing_inv A hu, Matrix.det_one]
    simpa only [hA, one_mul] using h
  · rw [restrict_restrict, Matrix.mul_nonsing_inv A hu, restrict_one]

/-- The exact old factorization package, proved from the two ordinary
textbook statements. Neither input mentions an existing weight-limit curve. -/
theorem orbitBigCellInput (BC : SpecialLinearBigCellInput) (OP : FormOrbitOpenMapInput) :
    TextbookOrbitBigCellInput where
  decompose F hF hclosed B hB w hsum hW := by
    classical
    let G := restrict B F
    let G₀ := zeroWeightPart G w
    have hGh := homogeneous_restrict B F hF
    have hGclosed : ClosedSLOrbit G := closedSLOrbit_restrict F hF hclosed B hB
    have hG₀ : G₀ ∈ slOrbit G :=
      hGclosed (zeroWeightPart_mem_slOrbitClosure G w hsum hW)
    obtain ⟨q,hq,hcell⟩ := BC.principal_neighborhood w
    obtain ⟨p,hp,hopen⟩ := OP.principal_image G₀ (zeroWeightPart_homogeneous hGh w) q hq
    obtain ⟨t,ht,hpt⟩ := exists_nonzero_curve_test G w hW p hp
    have hct : curve G w t ∈ slOrbit G₀ :=
      slOrbit_trans ⟨diagonalWeight w t, diagonalWeight_det w hsum t ht,
        curve_eq_restrict G w hW t ht⟩ (slOrbit_symm hG₀)
    obtain ⟨A,hA,hqA,hcurve⟩ := hopen (curve G w t) hct hpt
    obtain ⟨U,V,P,hAeq,hUV,hVdet,hU,hV,hP⟩ := hcell A hA hqA
    let a : Fin _ → GeometricField := fun i => t ^ w i
    have ha : ∀ i, a i ≠ 0 := fun i => zpow_ne_zero _ ht
    refine ⟨diagonalConjugate a U, diagonalConjugate a V,
      diagonalConjugate a P, ?_, ?_, diagonalConjugate_upper a ha w U hU,
      diagonalConjugate_upper a ha w V hV, diagonalConjugate_lower a w P hP, ?_⟩
    · rw [diagonalConjugate_mul a ha, hUV, diagonalConjugate_one a ha]
    · rw [diagonalConjugate_det a ha, hVdet]
    · have hfixed : restrict (Matrix.diagonal a) G₀ = G₀ :=
        diagonal_fixes_zeroWeightPart G w t ht
      have hconj : restrict (diagonalConjugate a A) G₀ = G := by
        unfold diagonalConjugate
        rw [← restrict_restrict, ← restrict_restrict, hfixed, ← hcurve,
          curve_eq_restrict G w hW t ht, restrict_restrict]
        change restrict (Matrix.diagonal a * Matrix.diagonal (fun i => (a i)⁻¹)) G = G
        rw [diagonal_mul_inverse a ha, restrict_one]
      change G = restrict (diagonalConjugate a U) (restrict (diagonalConjugate a P) G₀)
      rw [restrict_restrict, diagonalConjugate_mul a ha, ← hAeq]
      exact hconj.symm

end HessianTheorem11.ReducedBigCell
