import HessianTheorem11.UnconditionalWeightDescent
import HessianTheorem11.ReducedClosedOrbitZero
import HessianTheorem11.CubicIrreducibility
import HessianTheorem11.Completed
import HessianTheorem11.SingularExceptionalCoordinates
import HessianTheorem11.SingularNormalIndependence
import HessianTheorem11.SingularElevenReduction

/-! Exact eleven- and twelve-variable singular-locus bounds, assembled from
actual maximal components and the proved normal-tuple independence theorem. -/
noncomputable section
set_option maxRecDepth 4000
namespace HessianTheorem11
open Module MvPolynomial SingularRadialNormalForm NonzeroLimitTransport

namespace SingularRankFiveException

theorem eleven_impossible
    (KB : KernelBundleTangentImageInput) (SA : FormalSmoothArcInput)
    (AD : AffineHypersurfaceDimensionInput) (KI : KernelBundleInput)
    (MR : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (GR : GenericRankOpenInput) (F : AnisotropicCubic 11)
    (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hgeneric : 10 ≤ geometricCubicGenericRank (geometricPolynomial F.polynomial))
    (E : SingularRankFiveException F) : False := by
  obtain ⟨x,hx⟩ := E.generic.nonempty
  obtain ⟨A⟩ := E.adapted_basis x hx
  obtain ⟨C⟩ := E.graded_coordinates (by norm_num) x hx A
  obtain ⟨q,p,hq,hp,hqe,hpe⟩ := E.normal_data DT (by norm_num) x hx A
  have hlin := normal_tuple_independent SA _ (geometric_homogeneous F.homogeneous)
    hsemi E.base E.component.closed E.component.irreducible E.singular x
    (E.generic.subset hx) (E.smooth x hx) A (E.tangent_eq_kernel (by norm_num) x hx)
    (E.tensor DT x hx) (by rw [E.tangent_dimension x hx]; norm_num) C (by norm_num)
    q hq p hp hqe hpe
  have hfour := exists_tangent_rank_four_of_normal_independent SA GR AD _
    (geometric_homogeneous F.homogeneous) E.base E.component.closed E.component.irreducible
    E.singular x (E.generic.subset hx) (E.smooth x hx) A
    (E.tangent_eq_kernel (by norm_num) x hx) (E.tensor DT x hx) C q p hp hlin hqe hpe
  exact six_dimensional_singular_component_impossible_of_rank_four KB SA AD KI MR _
    (geometric_homogeneous F.homogeneous) hirred hgeneric E.base E.component.closed
    E.component.irreducible E.singular E.dimension E.generic E.rank_five ⟨x,hx,hfour⟩

theorem twelve_impossible
    (MR : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField)
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (SA : FormalSmoothArcInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 12)
    (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0)
    (E : SingularRankFiveException F) : False := by
  obtain ⟨x,hx⟩ := E.generic.nonempty
  obtain ⟨D⟩ := E.twelve_equality_data DT boundary bigCell hirred hdet x hx
  obtain ⟨C⟩ := D.twelve_coordinates
  obtain ⟨q,p,hq,hp,hqe,hpe⟩ := E.normal_data DT (by norm_num) x hx D.flag
  have hlin := normal_tuple_independent SA _ (geometric_homogeneous F.homogeneous)
    hsemi E.base E.component.closed E.component.irreducible E.singular x
    (E.generic.subset hx) (E.smooth x hx) D.flag (E.tangent_eq_kernel (by norm_num) x hx)
    (E.tensor DT x hx) (by rw [E.tangent_dimension x hx]; norm_num) C (by norm_num)
    q hq p hp hqe hpe
  have he : D.limit = zeroWeightPart
      (PolynomialRestriction.restrict (HessianTheorem11.basisMatrix D.flag.basis)
        (geometricPolynomial F.polynomial))
      (singularRadialWeight D.flag.radial D.flag.tangentIndices D.flag.tangentIndices) := by
    unfold EqualityData.limit
    rw [← D.twelve_indices_eq]
  apply D.twelve_impossible_of_independent_tuple MR DT FI GR AD SA
    (geometric_homogeneous F.homogeneous) E.base E.component.closed E.component.irreducible
    E.singular (E.generic.subset hx) (E.smooth x hx) (E.generic.maximal_rank x hx)
    q hq p hp _ _ hlin
  · rwa [he]
  · rwa [he]

end SingularRankFiveException

namespace Completed
open RationalDescent

/-- Theorem 1.1: the affine singular locus has dimension at most five in
eleven variables. Every exceptional-component and normal-span step is proved. -/
theorem S11
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (GR : GenericRankOpenInput) (DT : SymmetricDeterminantalTangentInput)
    (KB : KernelBundleTangentImageInput) (SA : FormalSmoothArcInput)
    (AD : AffineHypersurfaceDimensionInput) (KI : KernelBundleInput)
    (MR : GenericMatrixRankInput) (KA : KernelAnnihilatorGeometryInput)
    (FD : AffineFiberDimensionInput) (LS : LinearSectionDimensionInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (DTQ : DeterminantalTangentOver ℚ) (CI : CubicGeometricIrreducibility)
    (FI : FormalImplicitFunctionInput GeometricField)
    : Targets.S11 := by
  intro F
  by_contra hbad
  have hsemi := UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F (by norm_num)
  have hirred := CI F (by norm_num)
  obtain ⟨E⟩ := singular_violation_has_rank_five_exception AC GP GR DT F
    (Or.inl rfl) hsemi (lt_of_not_ge hbad)
  have hgeneric : 10 ≤ geometricCubicGenericRank (geometricPolynomial F.polynomial) := by
    rw [geometricCubicGenericRank_geometricPolynomial MR F.polynomial hirred]
    exact R11 MR KA AD GR GP DT FD LS boundary bigCell DTQ CI FI  F
  exact E.eleven_impossible KB SA AD KI MR DT GR F hsemi hirred hgeneric

/-- Theorem 1.1: the affine singular locus has dimension at most six in
twelve variables. The actual equality limit contradicts the completed rank bound. -/
theorem S12
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (GR : GenericRankOpenInput) (DT : SymmetricDeterminantalTangentInput)
    (MR : GenericMatrixRankInput) (AD : AffineHypersurfaceDimensionInput)
    (SA : FormalSmoothArcInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (DTQ : DeterminantalTangentOver ℚ) (CI : CubicGeometricIrreducibility)
    (FI : FormalImplicitFunctionInput GeometricField)
    : Targets.S12 := by
  intro F
  by_contra hbad
  have hsemi := UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F (by norm_num)
  have hirred := CI F (by norm_num)
  obtain ⟨E⟩ := singular_violation_has_rank_five_exception AC GP GR DT F
    (Or.inr rfl) hsemi (lt_of_not_ge hbad)
  exact E.twelve_impossible MR DT FI GR AD SA boundary bigCell F hsemi hirred
    (geometric_hessianDeterminantPolynomial_ne_zero DTQ F)

end Completed
end HessianTheorem11
