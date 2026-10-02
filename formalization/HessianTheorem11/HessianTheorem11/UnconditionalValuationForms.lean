import HessianTheorem11.UnconditionalValuationSpecialLinear
import HessianTheorem11.UnconditionalValuativeOrbit

/-! Integral form models on the two sides of the actual diagonal Cartan
factor. The outer factors are determinant-one over the valuation ring. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace HessianTheorem11.UnconditionalValuationForms
open MvPolynomial PolynomialRestriction PolynomialWeightTransport
  UnconditionalValuationMatrix UnconditionalOrbitIdeal

variable {K : Type*} [Field K] (V : ValuationSubring K)

/-- An integral orbit value can be pulled back through the integral right
SL factor. Both sides of the resulting diagonal degeneration are integral
forms, with the source related to the original form by an integral SL frame. -/
theorem exists_integral_diagonal_model {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.det = 1)
    (F E : MvPolynomial (Fin n) V)
    (hE : map V.subtype E = restrict M (map V.subtype F)) :
    ∃ (A B : Matrix (Fin n) (Fin n) V) (d : Fin n → K),
      A.det = 1 ∧ B.det = 1 ∧ (B⁻¹).det = 1 ∧
      (∀ i, d i ≠ 0) ∧ (∏ i, d i) = 1 ∧
      map V.subtype (restrict B⁻¹ E) =
        restrict (Matrix.diagonal d) (map V.subtype (restrict A F)) := by
  classical
  obtain ⟨A,B,d,hA,hB,hd,hprod,hfact⟩ := exists_specialLinear_factorization V hn M hM
  have hu : IsUnit B.det := hB ▸ isUnit_one
  have hBi : (B⁻¹).det = 1 := by
    have h := Matrix.det_nonsing_inv_mul_det B hu
    simpa [hB] using h
  have hcancel : matrixMap V B * matrixMap V B⁻¹ = 1 := by
    rw [← map_mul,Matrix.mul_nonsing_inv B hu,map_one]
  refine ⟨A,B,d,hA,hB,hBi,hd,hprod,?_⟩
  rw [map_restrict,hE,map_restrict]
  change restrict (matrixMap V B⁻¹) (restrict M (map V.subtype F)) =
    restrict (Matrix.diagonal d) (restrict (matrixMap V A) (map V.subtype F))
  rw [restrict_restrict,restrict_restrict,hfact,Matrix.mul_assoc,hcancel,Matrix.mul_one]

/-- Decode integral coefficient coordinates without requiring the
coefficient ring to be a field. -/
def integralForm {n d : ℕ} (a : DegreeIndex n d → V) : MvPolynomial (Fin n) V :=
  ∑ e, monomial e.val (a e)

theorem map_integralForm {n d : ℕ} (a : DegreeIndex n d → V) :
    map V.subtype (integralForm V a) = decode (fun e => (a e : K)) := by
  simp only [integralForm,decode,map_sum,map_monomial]
  rfl

theorem coeff_integralForm {n d : ℕ} (a : DegreeIndex n d → V) (e : DegreeIndex n d) :
    coeff e.val (integralForm V a) = a e := by
  apply Subtype.val_injective
  change V.subtype (coeff e.val (integralForm V a)) = V.subtype (a e)
  rw [← coeff_map,map_integralForm]
  exact congrFun (coefficientVector_decode (fun e => (a e : K))) e

theorem integralForm_homogeneous {n d : ℕ} (a : DegreeIndex n d → V) :
    (integralForm V a).IsHomogeneous d := by
  classical
  apply IsHomogeneous.sum
  intro e _
  apply isHomogeneous_monomial
  exact (Finset.mem_finsuppAntidiag'.mp e.property).1

theorem map_integralForm_of_coefficients {n d : ℕ}
    (a : DegreeIndex n d → V) (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (ha : ∀ e, (a e : K) = coeff e.val F) :
    map V.subtype (integralForm V a) = F := by
  rw [map_integralForm]
  have he : (fun e => (a e : K)) = coefficientVector (d := d) F := funext ha
  rw [he,decode_coefficientVector F hF]

end HessianTheorem11.UnconditionalValuationForms
