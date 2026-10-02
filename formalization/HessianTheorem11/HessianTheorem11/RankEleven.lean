import HessianTheorem11.CubicIrreducibility
import HessianTheorem11.GeometricFirstNormal
import HessianTheorem11.RadicalIncidenceExclusion
import HessianTheorem11.IntrinsicRadicalTransport

/-! The eleven-variable rank bound, via the intrinsic radical line and
singular rank-four equality splitting. No ten-variable classification,
ordinary-determinant classification, or arithmetic splitting is needed. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module LocalCubicNormalForm CubicNormalFormConstruction

/-- At every good divisor point of a hypothetical rank-nine cubic, the
actual intrinsic radical is a line and its vectors have Hessian rank ≤4. -/
theorem rank_nine_intrinsic_radical_at_divisor_point
    (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    (F : GeometricPolynomial 11) (hF : F.IsHomogeneous 3) (hirred : Irreducible F)
    (P : CubicDivisorPoint F) (hrank : geometricCubicGenericRank F = 9) :
    finrank GeometricField (intrinsicRadical F P.point) = 1 ∧
      ∀ v ∈ intrinsicRadical F P.point, (hessian F v).rank ≤ 4 := by
  classical
  obtain ⟨m, q, ⟨S⟩⟩ := exists_cubic_hyperbolic_splitting F hF P.point P.on_cubic P.smooth
  have hd := S.hessian_rank_dimensions
  rw [P.rank_eq, hrank] at hd
  have hm : m = 2 := by omega
  have hq : q = 7 := by omega
  let D := data hF S
  have hD : PolynomialRestriction.restrict (BasisHessianTransport.basisMatrix S.basis) F =
      polynomial D := restrict_eq_polynomial_of_geometric_generic_rank
        DT hF hirred P.on_cubic S P.maximal_rank
  have hbase : S.basis.equivFun.symm (basePoint m q) = P.point := by
    rw [← coordinateMatrix_mulVec_eq S, coordinateMatrix_basePoint]
  have hB0 : (quadraticMatrix D.Q0).det ≠ 0 := Q0_det_ne_zero hF S
  let C := firstNormalSieveAt DT FI F hF hirred P S
  have hρ : (quadraticMatrix D.QA).rank = 1 := by
    have hc := C.rank_eleven_alternative
    rcases hc with hc | hc
    · omega
    · exact hc.2.1
  constructor
  · have hh := finrank_intrinsicRadical_of_local D S.basis F hD hB0
    rw [hbase, hρ, hm] at hh
    exact hh
  · intro v hv
    apply intrinsicRadical_rank_le_four_of_local D S.basis F hD FI hirred hB0
    · intro x hx
      have hh := P.maximal_rank x hx
      rw [P.rank_eq, hrank] at hh
      simpa only [hq] using hh
    · omega
    · omega
    · rwa [hbase]

/-- The actual first-normal exception supplies its own line-family
premises, so the radical incidence contradiction has no bespoke input. -/
theorem anisotropic_rank_eleven
    (MR : GenericMatrixRankInput) (KA : KernelAnnihilatorGeometryInput)
    (AD : AffineHypersurfaceDimensionInput) (GR : GenericRankOpenInput)
    (GP : GenericConePointSelectionInput) (DT : SymmetricDeterminantalTangentInput)
    (FD : AffineFiberDimensionInput) (LS : LinearSectionDimensionInput)
    (boundary : NonzeroLimitTransport.RationalRelativeBoundaryInput)
    (bigCell : NonzeroLimitTransport.TextbookOrbitBigCellInput)
    (DTQ : DeterminantalTangentOver ℚ) (CI : CubicGeometricIrreducibility)
    (FI : FormalImplicitFunctionInput GeometricField)
    (F : AnisotropicCubic 11)
    (hsemi : WeightSemistable (geometricPolynomial F.polynomial)) :
    10 ≤ genericHessianRank F.polynomial := by
  have hirred := CI F (by norm_num)
  have hdet := geometric_hessianDeterminantPolynomial_ne_zero DTQ F
  let f := geometricPolynomial F.polynomial
  have hf : f.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  have hrank := geometricCubicGenericRank_geometricPolynomial MR F.polynomial hirred
  rw [← hrank]
  by_contra hsmall
  obtain ⟨C⟩ := exists_firstNormalSieve MR DT FI f hf hirred hdet
  have hr9 : geometricCubicGenericRank f = 9 := by
    rcases C.rank_eleven_alternative with h | h
    · exact False.elim (hsmall h)
    · exact h.1
  obtain ⟨O⟩ := exists_cubicRadicalOpen MR KA AD f hf hirred hdet
  have hlocal : ∀ x ∈ O.openSet,
      finrank GeometricField (intrinsicRadical f x) = 1 ∧
        ∀ v ∈ intrinsicRadical f x, (hessian f v).rank ≤ 4 := by
    intro x hx
    exact rank_nine_intrinsic_radical_at_divisor_point DT FI f hf hirred
      (O.divisorPointAt hf x hx) hr9
  have hline : O.nullity = 1 := by
    obtain ⟨x, hx⟩ := O.nonempty
    have hh := (hlocal x hx).1
    rwa [O.dimension_kernel x hx] at hh
  exact eleven_radical_line_exception_impossible MR GR GP DT FD LS boundary bigCell F
    hsemi hirred hdet O hline (fun x hx => (hlocal x hx).2) hr9

end HessianTheorem11
