import HessianTheorem11.UnconditionalPolynomialOrbit
import HessianTheorem11.UnconditionalGenericPointOpen
import HessianTheorem11.UnconditionalSpecialLinear
import HessianTheorem11.ReducedBigCellMatrices

/-! Openness of the actual special-linear orbit map on homogeneous forms.
The proof first obtains one open source point by generic smoothness, then
translates it to the identity. All maps and coefficient tests are explicit
polynomials; no orbit-openness or group-variety input is assumed. -/
noncomputable section
namespace HessianTheorem11.UnconditionalFormOrbitOpen
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
  UnconditionalPolynomialOrbit UnconditionalOrbitIdeal UnconditionalGenericPointOpen
  ReducedBigCell

/-- Every principal matrix neighborhood of the identity maps onto a
principal coefficient neighborhood in the actual SL orbit. -/
theorem principal_image {n d : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous d)
    (q : MvPolynomial (Fin n × Fin n) GeometricField)
    (hq : eval (matrixPoint (1 : Matrix (Fin n) (Fin n) GeometricField)) q ≠ 0) :
    ∃ p : MvPolynomial (Fin n →₀ ℕ) GeometricField,
      eval (fun e => coeff e F) p ≠ 0 ∧
      ∀ G ∈ slOrbit F, eval (fun e => coeff e G) p ≠ 0 →
        ∃ A : Matrix (Fin n) (Fin n) GeometricField,
          A.det = 1 ∧ eval (matrixPoint A) q ≠ 0 ∧ G = restrict A F := by
  classical
  let Z := UnconditionalSpecialLinear.specialLinearLocus n
  let P := orbitPolynomials (d := d) F
  obtain ⟨x, hx, hopen⟩ := exists_open_point P Z
    (UnconditionalSpecialLinear.specialLinearLocus_closed n)
    (UnconditionalSpecialLinear.specialLinearLocus_irreducible n)
  let A₀ := pointMatrix x
  have hA₀ : A₀.det = 1 := hx
  have hu : IsUnit A₀.det := hA₀ ▸ isUnit_one
  have hAinv : (A₀⁻¹).det = 1 := by rw [Matrix.det_nonsing_inv,hA₀,Ring.inverse_one]
  let b := rightTranslatePolynomial A₀⁻¹ q
  have hbx : eval x b ≠ 0 := by
    simpa only [b,eval_rightTranslatePolynomial,show pointMatrix x = A₀ from rfl,
      Matrix.mul_nonsing_inv A₀ hu] using hq
  obtain ⟨g, hg, hsub⟩ := hopen b hbx
  refine ⟨translatedCoefficientTest A₀ g, ?_, ?_⟩
  · rw [eval_translatedCoefficientTest A₀ g F hF]
    simpa only [P,polynomialMap_orbitPolynomials] using hg
  · intro G hG hpG
    obtain ⟨B, hB, rfl⟩ := hG
    have hGF : (restrict B F).IsHomogeneous d := homogeneous_restrict B F hF
    rw [eval_translatedCoefficientTest A₀ g (restrict B F) hGF] at hpG
    have hy : coefficientVector (d := d) (restrict A₀ (restrict B F)) ∈
        geometricClosure (polynomialMap P '' Z) := by
      apply subset_geometricClosure
      refine ⟨matrixPoint (B * A₀), ?_, ?_⟩
      · change (B * A₀).det = 1
        rw [Matrix.det_mul,hB,hA₀,one_mul]
      · simp only [P,polynomialMap_orbitPolynomials,pointMatrix_matrixPoint,restrict_restrict]
    obtain ⟨z, ⟨hz, hbz⟩, hez⟩ := hsub _ hy hpG
    have hform : restrict (pointMatrix z) F = restrict A₀ (restrict B F) := by
      have he := congrArg (decode (d := d)) hez
      simpa only [P,polynomialMap_orbitPolynomials,
        decode_coefficientVector _ (homogeneous_restrict (pointMatrix z) F hF),
        decode_coefficientVector _ (homogeneous_restrict A₀ (restrict B F) hGF)] using he
    refine ⟨pointMatrix z * A₀⁻¹, ?_, ?_, ?_⟩
    · have hz' : (pointMatrix z).det = 1 := hz
      rw [Matrix.det_mul,hz',hAinv,one_mul]
    · simpa only [b,eval_rightTranslatePolynomial] using hbz
    · rw [← restrict_restrict,hform,restrict_restrict,
        Matrix.mul_nonsing_inv A₀ hu,restrict_one]

/-- The former orbit-openness package is constructed with no inputs. -/
def formOrbitOpenMapInput : FormOrbitOpenMapInput where
  principal_image := principal_image

end HessianTheorem11.UnconditionalFormOrbitOpen
