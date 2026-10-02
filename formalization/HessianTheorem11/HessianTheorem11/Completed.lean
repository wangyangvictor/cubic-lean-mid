import HessianTheorem11.UnconditionalWeightDescent
import HessianTheorem11.ReducedClosedOrbitZero
import HessianTheorem11.CubicIrreducibility
import HessianTheorem11.Targets
import HessianTheorem11.SingularGeometry
import HessianTheorem11.RationalDescent
import HessianTheorem11.IncidenceRadial
import HessianTheorem11.Concentration
import HessianTheorem11.GeometricFirstNormal
import HessianTheorem11.IncidenceEquality
import HessianTheorem11.RankEleven

/-! Completed numerical entries of the requested table.

The geometric arguments below are general textbook results, stated with their
full mathematical predicates in TextbookGeometry and RationalDescent. The
internal `CI` argument is a proved cubic lemma supplied by public aggregates.
In particular,
anisotropy implying geometric semistability and the singular radial bound are
proved in Lean, rather than supplied as inputs.
-/

namespace HessianTheorem11.Completed

open RationalDescent

/-- Theorem 1.1, thirteen-variable singular-locus column: its geometric
affine dimension is at most seven. The input boundary consists only of the
general textbook AG and relative Kempf theorems documented in the input audit. -/
theorem S13
    (AG : FiniteQuadraticConeCoverInput)
    (DT : SymmetricDeterminantalTangentInput)
    : Targets.S13 := by
  intro F
  exact singularDimension_thirteen_le_seven_of_semistable AG DT F.polynomial
    F.homogeneous (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F (by norm_num))

/-- Theorem 1.1, eleven-variable incidence column: the geometric affine
incidence dimension is at most thirteen. Concentration and both radial
branches are derived for the actual cubic; only general textbook AG and
relative Kempf inputs are retained as arguments. -/
theorem I11
    (AG : ConcentrationGeometryInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput)
    : Targets.I11 := by
  intro F
  obtain ⟨C⟩ := incidence_concentration AG DT (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous)
  exact incidence_eleven_le_thirteen_of_concentrated_base GP DT F.polynomial
    F.homogeneous (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F (by norm_num))
    C.base C.closed C.irreducible C.cone C.contained C.baseDimension C.rank C.nullity
    C.dimension_base C.dimension_incidence C.rank_nullity C.rank_attained C.maximal_rank

/-- Theorem 1.1, twelve-variable generic Hessian rank: at least ten.
All first-normal and Clifford calculations are proved in Lean. -/
theorem R12
    (AG : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (DTQ : DeterminantalTangentOver ℚ)
    (CI : CubicGeometricIrreducibility)
    (FI : FormalImplicitFunctionInput GeometricField) : Targets.R12 := by
  intro F
  have hi := CI F (by norm_num)
  have hr := geometric_rank_twelve AG DT FI (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous) hi
    (geometric_hessianDeterminantPolynomial_ne_zero DTQ F)
  rwa [geometricCubicGenericRank_geometricPolynomial AG F.polynomial hi] at hr

/-- Theorem 1.1, thirteen-variable generic Hessian rank: at least ten. -/
theorem R13
    (AG : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (DTQ : DeterminantalTangentOver ℚ)
    (CI : CubicGeometricIrreducibility)
    (FI : FormalImplicitFunctionInput GeometricField) : Targets.R13 := by
  intro F
  have hi := CI F (by norm_num)
  have hr := geometric_rank_thirteen AG DT FI (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous) hi
    (geometric_hessianDeterminantPolynomial_ne_zero DTQ F)
  rwa [geometricCubicGenericRank_geometricPolynomial AG F.polynomial hi] at hr

/-- Theorem 1.1, twelve-variable incidence dimension: at most fourteen.
The equality case is derived from actual radial weights and unipotent
transport, then excluded by the completed geometric rank theorem. -/
theorem I12
    (AG : ConcentrationGeometryInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput) (AD : AffineHypersurfaceDimensionInput)
    (boundary : NonzeroLimitTransport.RationalRelativeBoundaryInput)
    (bigCell : NonzeroLimitTransport.TextbookOrbitBigCellInput)
    (MR : GenericMatrixRankInput) (DTQ : DeterminantalTangentOver ℚ)
    (CI : CubicGeometricIrreducibility)
    (FI : FormalImplicitFunctionInput GeometricField)
    : Targets.I12 := by
  intro F
  by_contra hI
  have hirred := CI F (by norm_num)
  have hsemi := UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F (by norm_num)
  have hbad := incidence_twelve_violation_forces_generic_rank_eight
    AG GP DT AD boundary bigCell F hsemi hirred (lt_of_not_ge hI)
  have hgood := R12 MR DT DTQ CI FI F
  omega

/-- Theorem 1.1, eleven-variable generic Hessian rank: at least ten.
The remaining normal-rank-one case is excluded by the actual radical
incidence and singular equality split, without determinant classification. -/
theorem R11
    (MR : GenericMatrixRankInput) (KA : KernelAnnihilatorGeometryInput)
    (AD : AffineHypersurfaceDimensionInput) (GR : GenericRankOpenInput)
    (GP : GenericConePointSelectionInput) (DT : SymmetricDeterminantalTangentInput)
    (FD : AffineFiberDimensionInput) (LS : LinearSectionDimensionInput)
    (boundary : NonzeroLimitTransport.RationalRelativeBoundaryInput)
    (bigCell : NonzeroLimitTransport.TextbookOrbitBigCellInput)
    (DTQ : DeterminantalTangentOver ℚ) (CI : CubicGeometricIrreducibility)
    (FI : FormalImplicitFunctionInput GeometricField)
    : Targets.R11 := by
  intro F
  exact anisotropic_rank_eleven MR KA AD GR GP DT FD LS boundary bigCell DTQ CI FI F
    (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F (by norm_num))

end HessianTheorem11.Completed
