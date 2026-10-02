import HessianTheorem11
import CubicTenVariables.DimensionReduction

/-! Ten-variable geometric bounds needed by the analytic argument, derived
from the existing fully proved geometry. They concern a hypothetical
anisotropic cubic; no rational-solubility conclusion is claimed here. -/
noncomputable section
namespace CubicTenVariables.Geometry
open HessianTheorem11 MvPolynomial RationalDescent

/-- The existing first-normal parity sieve excludes generic rank seven
in ten variables. This avoids assuming the manuscript's Zak-style bound. -/
theorem firstNormal_rank_eight {r : ℕ} (S : FirstNormalSieve 10 r) : 8 ≤ r := by
  have hd := S.dimension
  have hm := S.corank_le_multiplicity
  have hh := S.degree_bound
  have hρ := S.normalRank_le
  have hnormal := S.normal_bound
  by_contra hr
  have heq : r = 7 := by omega
  have heven := S.even_middle (by omega)
  norm_num [heq] at heven

/-- The actual generic full Hessian rank on the ten-variable cubic is at
least eight. Every geometric interface is supplied by an existing proof. -/
theorem genericHessianRank_ge_eight (F : AnisotropicCubic 10) :
    8 ≤ genericHessianRank F.polynomial := by
  have hi := Unconditional.cubicGeometricIrreducibility F (by norm_num)
  obtain ⟨S⟩ := exists_firstNormalSieve ReducedGenericRank.genericMatrixRankInput
    provedSymmetricDeterminantalTangent
    (ReducedFormalImplicit.formalImplicitFunctionInput GeometricField)
    (geometricPolynomial F.polynomial) (geometric_homogeneous F.homogeneous) hi
    (geometric_hessianDeterminantPolynomial_ne_zero (provedDeterminantalTangentOver ℚ) F)
  have h := firstNormal_rank_eight S
  rwa [geometricCubicGenericRank_geometricPolynomial
    ReducedGenericRank.genericMatrixRankInput F.polynomial hi] at h

/-- The full affine incidence, without an equation F(x)=0, has dimension
at most twelve in ten variables. -/
theorem incidenceDimension_le_twelve (F : AnisotropicCubic 10) :
    incidenceDimension F.polynomial ≤ 12 := by
  obtain ⟨C⟩ := incidence_concentration Unconditional.concentrationGeometry
    provedSymmetricDeterminantalTangent (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous)
  obtain ⟨d,hd,hnum⟩ := incidence_radial_of_concentrated_base
    Unconditional.genericConePointSelection provedSymmetricDeterminantalTangent
    F.polynomial F.homogeneous
    (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F (by norm_num))
    C.base C.closed C.irreducible C.cone C.contained C.baseDimension C.rank C.nullity
    C.dimension_base C.dimension_incidence C.rank_nullity C.rank_attained C.maximal_rank
  have hb : d ≤ 12 := by rcases hnum with h | h <;> omega
  rw [hd]
  exact_mod_cast hb

/-- The affine singular cone has dimension at most five. -/
theorem singularDimension_le_five (F : AnisotropicCubic 10) :
    singularDimension F.polynomial ≤ 5 := by
  simpa using BibleRestrictions.singularDimension_le_radial_floor
    Unconditional.finiteQuadraticConeCover provedSymmetricDeterminantalTangent F
    (by norm_num)

/-- The manuscript's projective singular-dimension bound, using the
actual normalized projective charts rather than a subtraction convention. -/
theorem projectiveSingularDimension_le_four (F : AnisotropicCubic 10) :
    BibleProjectiveGeometry.projectiveDimension (singularLocus F.polynomial) ≤ 4 := by
  apply BibleProjectiveGeometry.projectiveDimension_le Unconditional.projectiveDimensionInput
    _ (BibleHyperplanes.singularCone_closed _)
    (BibleHyperplanes.singularCone_cone _ (geometric_homogeneous F.homogeneous))
  exact singularDimension_le_five F

/-- The full geometric SL orbit is closed, using the previously proved
rational boundary theorem with no remaining GIT assumption. -/
theorem closedSLOrbit (F : AnisotropicCubic 10) :
    NonzeroLimitTransport.ClosedSLOrbit (geometricPolynomial F.polynomial) :=
  NonzeroLimitTransport.anisotropic_closedSLOrbit
    UnconditionalBoundary.rationalRelativeBoundaryInput F (by norm_num)

end CubicTenVariables.Geometry
