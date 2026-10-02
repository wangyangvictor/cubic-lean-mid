import HessianTheorem11.UnconditionalValuationForms
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! An actual coefficient-closure point yields integral forms on both
sides of a determinant-one diagonal degeneration. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace HessianTheorem11.UnconditionalIntegralOrbit
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
  UnconditionalOrbitIdeal UnconditionalValuativeOrbit UnconditionalValuationForms

/-- This is a valuative model of the literal orbit-closure specialization.
The source frame is integral SL, and every coefficient equation specializes
to its prescribed vanishing at G. No existence of a one-parameter subgroup
is yet asserted here. -/
theorem exists_integral_orbit_model {n d : ℕ} (hn : 0 < n)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous d)
    (G : GeometricPolynomial n) (hG : G ∈ slOrbitClosure F) :
    ∃ V : ValuationSubring (SLFunctionField n), ∃ c : GeometricField →+* V,
      ∃ (A B : Matrix (Fin n) (Fin n) V) (δ : Fin n → SLFunctionField n)
        (E : MvPolynomial (Fin n) V),
      (∀ z, (c z : SLFunctionField n) = algebraMap GeometricField (SLFunctionField n) z) ∧
      A.det = 1 ∧ B.det = 1 ∧ (B⁻¹).det = 1 ∧
      (∀ i, δ i ≠ 0) ∧ (∏ i, δ i) = 1 ∧ E.IsHomogeneous d ∧
      (∀ q : MvPolynomial (DegreeIndex n d) GeometricField,
        eval₂ c (fun e => coeff e.val E) q ∈ IsLocalRing.maximalIdeal V ↔
          eval (coefficientVector G) q = 0) ∧
      map V.subtype (restrict B⁻¹ E) =
        restrict (Matrix.diagonal δ) (map V.subtype (restrict A (map c F))) := by
  obtain ⟨V,c,a,hc,ha,hcenter⟩ := exists_orbit_valuation (d := d) F G hG
  let E := integralForm V a
  have hcm : V.subtype.comp c = algebraMap GeometricField (SLFunctionField n) := by
    ext z
    exact hc z
  have hE : map V.subtype E = restrict (genericSLMatrix n) (map V.subtype (map c F)) := by
    rw [MvPolynomial.map_map,hcm]
    exact map_integralForm_of_coefficients V a _
      (homogeneous_restrict (genericSLMatrix n) _ (hF.map _)) ha
  obtain ⟨A,B,δ,hA,hB,hBi,hδ,hprod,hdiag⟩ := exists_integral_diagonal_model V hn
    (genericSLMatrix n) (genericSLMatrix_det n) (map c F) E hE
  refine ⟨V,c,A,B,δ,E,hc,hA,hB,hBi,hδ,hprod,integralForm_homogeneous V a,?_,hdiag⟩
  intro q
  simpa only [E,coeff_integralForm] using hcenter q

/-- The residue form is exactly the chosen closure point after extending
the base coefficients. This upgrades the all-equations center description
to an equality of actual homogeneous polynomials. -/
theorem residue_form_eq {L : Type*} [Field L] (V : ValuationSubring L)
    (c : GeometricField →+* V) {n d : ℕ}
    (E : MvPolynomial (Fin n) V) (hE : E.IsHomogeneous d)
    (G : GeometricPolynomial n) (hG : G.IsHomogeneous d)
    (hcenter : ∀ q : MvPolynomial (DegreeIndex n d) GeometricField,
      eval₂ c (fun e => coeff e.val E) q ∈ IsLocalRing.maximalIdeal V ↔
        eval (coefficientVector G) q = 0) :
    map (IsLocalRing.residue V) E = map ((IsLocalRing.residue V).comp c) G := by
  classical
  have hcoeff : coefficientVector (d := d) (map (IsLocalRing.residue V) E) =
      coefficientVector (d := d) (map ((IsLocalRing.residue V).comp c) G) := by
    funext e
    have hz := (hcenter (X e - C (coeff e.val G))).mpr (by simp [coefficientVector])
    have hr := (IsLocalRing.residue_eq_zero_iff _).mpr hz
    have he : IsLocalRing.residue V (coeff e.val E) =
        IsLocalRing.residue V (c (coeff e.val G)) := by
      apply sub_eq_zero.mp
      simpa only [eval₂_sub,eval₂_X,eval₂_C,map_sub] using hr
    simpa only [coefficientVector,coeff_map,RingHom.comp_apply] using he
  have he := congrArg (decode (K := IsLocalRing.ResidueField V)) hcoeff
  simpa only [decode_coefficientVector _ (hE.map _),decode_coefficientVector _ (hG.map _)] using he

end HessianTheorem11.UnconditionalIntegralOrbit
