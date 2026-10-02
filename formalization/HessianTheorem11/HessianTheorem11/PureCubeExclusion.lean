import HessianTheorem11.DeletedCubicGeometry
import HessianTheorem11.CubicRankIrreducibility
import HessianTheorem11.GeometricFirstNormal
import HessianTheorem11.AffineHypersurfaceDimension

/-! The defect-one split cannot support the exceptional incidence base:
deleting its pure-cube coordinate gives an actual irreducible twelve-variable
cubic with generic Hessian rank at most eight, contradicting the proved sieve. -/
noncomputable section
set_option maxRecDepth 2048
namespace HessianTheorem11
open MvPolynomial Module

theorem pure_cube_rank_eight_base_impossible
    (MR : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField) (AD : AffineHypersurfaceDimensionInput)
    (G : GeometricPolynomial 13) (hG : G.IsHomogeneous 3)
    (hdet : hessianDeterminantPolynomial G ≠ 0)
    (c : Fin 13) (κ : GeometricField)
    (hsplit : G = eraseCoordinate c G + C κ * X c ^ 3)
    (Z : Set (GeometricPoint 13)) (hclosed : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hdim : affineDimension Z = 11)
    (hzero : ∀ x ∈ Z, eval x G = 0)
    (hbound : ∀ x ∈ Z, (hessian G x).rank ≤ 8)
    (hwitness : ∃ x ∈ Z, x c = 0 ∧ (hessian G x).rank = 8) : False := by
  classical
  have hκ : κ ≠ 0 := by
    intro hk
    have he : G = eraseCoordinate c G := by simpa [hk] using hsplit
    apply hdet
    unfold hessianDeterminantPolynomial
    apply Matrix.det_eq_zero_of_row_eq_zero c
    intro j
    change pderiv j (pderiv c G) = 0
    rw [he, pderiv_eraseCoordinate]
    exact map_zero _
  have hc := pure_cube_coordinate_vanishes_on_base MR G c κ hsplit hκ Z hirred 8
    hbound (by obtain ⟨x, hx, hxc, hr⟩ := hwitness; exact ⟨x,hx,hxc,hr.ge⟩)
  let H := deleteCoordinate c G
  have hH : H.IsHomogeneous 3 := deleteCoordinate_homogeneous c G hG
  have hHd : hessianDeterminantPolynomial H ≠ 0 :=
    deleted_hessianDeterminant_ne_zero c G κ hsplit hdet
  obtain ⟨x, hx, hxc, hr⟩ := hwitness
  have hHx : eval (c.removeNth x) H = 0 := by
    rw [show H = deleteCoordinate c G from rfl, deleteCoordinate_eq_restrict,
      PolynomialRestriction.eval_restrict, coordinateDeletionMatrix_mulVec]
    rw [show c.insertNth 0 (c.removeNth x) = x by
      conv_lhs => arg 2; rw [← hxc]
      exact Fin.insertNth_self_removeNth c x]
    exact hzero x hx
  have hHr : (hessian H (c.removeNth x)).rank = 8 :=
    (hessian_deleted_rank_eq_of_coordinate_zero c G κ hsplit x hxc).trans hr
  have hHi : Irreducible H := cubic_irreducible_of_intermediate_hessian_rank H hH hHd
    (c.removeNth x) hHx (by omega) (by omega)
  have hsub : deletedBase c Z ⊆ polynomialHypersurface H := by
    intro v hv
    change eval v H = 0
    rw [show H = deleteCoordinate c G from rfl, deleteCoordinate_eq_restrict,
      PolynomialRestriction.eval_restrict, coordinateDeletionMatrix_mulVec]
    exact hzero _ hv
  have heq : deletedBase c Z = polynomialHypersurface H :=
    equal_hypersurface_of_dimension_ge AD H hHi (deletedBase c Z) (deletedBase_closed c Z hclosed)
      hsub (by rw [deletedBase_dimension c Z hc, hdim]; norm_num)
  have hsmall : ∀ v ∈ polynomialHypersurface H, (hessian H v).rank ≤ 8 := by
    intro v hv
    have hz : (coordinateDeletionMatrix c).mulVec v ∈ Z := by
      rw [coordinateDeletionMatrix_mulVec]
      change v ∈ deletedBase c Z
      rwa [heq]
    rw [show H = deleteCoordinate c G from rfl, deleteCoordinate_eq_restrict,
      PolynomialRestriction.hessian_restrict]
    exact (Restriction.rank_congruence_le _ _).trans (hbound _ hz)
  have hlarge := geometric_rank_twelve MR DT FI H hH hHi hHd
  obtain ⟨P⟩ := exists_cubicDivisorPoint MR H hH hHi hHd
  have hh := hsmall P.point P.on_cubic
  rw [P.rank_eq] at hh
  omega

end HessianTheorem11
