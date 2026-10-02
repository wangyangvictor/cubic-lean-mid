import HessianTheorem11.UnconditionalIntegralOrbit
import HessianTheorem11.UnconditionalAlgebraicExistenceTargetAction

/-! The two residue forms in the constructed valuation model have exactly
the required target membership and nonmembership. These are proved from
the actual source/target frames and the prescribed specialization point. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace HessianTheorem11.UnconditionalResidueTarget
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
  ReducedRelative UnconditionalAlgebraicExistence UnconditionalIntegralOrbit

variable {L : Type*} [Field L] (V : ValuationSubring L)
  [Algebra GeometricField (IsLocalRing.ResidueField V)]
  (c : GeometricField →+* V)
  (hc : (IsLocalRing.residue V).comp c =
    algebraMap GeometricField (IsLocalRing.ResidueField V)) {n d : ℕ}

include hc

theorem residue_restriction_map (A : Matrix (Fin n) (Fin n) V)
    (F : GeometricPolynomial n) :
    map (IsLocalRing.residue V) (restrict A (map c F)) =
      restrict (A.map (IsLocalRing.residue V))
        (map (algebraMap GeometricField (IsLocalRing.ResidueField V)) F) := by
  rw [map_restrict,MvPolynomial.map_map,hc]

theorem residue_source_notMem
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous d)
    (S : Set (GeometricPolynomial n)) (hclosed : coefficientClosed S)
    (hhom : ∀ H ∈ S, H.IsHomogeneous d) (hinv : slInvariant S) (hnot : F ∉ S)
    (A : Matrix (Fin n) (Fin n) V) (hA : A.det = 1) :
    map (IsLocalRing.residue V) (restrict A (map c F)) ∉ extendedTarget d S := by
  rw [residue_restriction_map V c hc]
  let Abar : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField V) :=
    A.map (IsLocalRing.residue V)
  have hAb : Abar.det = 1 := by
    exact ((IsLocalRing.residue V).map_det A).symm.trans (by rw [hA,map_one])
  have hu : IsUnit Abar.det := hAb ▸ isUnit_one
  have hAi : (Abar⁻¹).det = 1 := by
    rw [Matrix.det_nonsing_inv,hAb,Ring.inverse_one]
  intro hmem
  have he := extendedTarget_slInvariant d S hclosed hhom hinv Abar⁻¹ hAi _ hmem
  rw [restrict_restrict,Matrix.mul_nonsing_inv Abar hu,restrict_one] at he
  exact map_notMem_extendedTarget d S hclosed hhom F hF hnot he

theorem residue_target_mem
    (S : Set (GeometricPolynomial n)) (hclosed : coefficientClosed S)
    (hhom : ∀ H ∈ S, H.IsHomogeneous d) (hinv : slInvariant S)
    (G : GeometricPolynomial n) (hG : G ∈ S)
    (E : MvPolynomial (Fin n) V) (hE : E.IsHomogeneous d)
    (hcenter : ∀ q : MvPolynomial (UnconditionalOrbitIdeal.DegreeIndex n d) GeometricField,
      eval₂ c (fun e => coeff e.val E) q ∈ IsLocalRing.maximalIdeal V ↔
        eval (UnconditionalOrbitIdeal.coefficientVector G) q = 0)
    (B : Matrix (Fin n) (Fin n) V) (hB : B.det = 1) :
    map (IsLocalRing.residue V) (restrict B E) ∈ extendedTarget d S := by
  have he := residue_form_eq V c E hE G (hhom G hG) hcenter
  rw [hc] at he
  rw [map_restrict,he]
  apply extendedTarget_slInvariant d S hclosed hhom hinv
  · exact ((IsLocalRing.residue V).map_det B).symm.trans (by rw [hB,map_one])
  · exact map_mem_extendedTarget d S hhom G hG

end HessianTheorem11.UnconditionalResidueTarget
