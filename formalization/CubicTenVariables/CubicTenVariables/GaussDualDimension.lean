import CubicTenVariables.GaussImageGeometry
import CubicTenVariables.TerminalProjectiveDimension
import HessianTheorem11.HessianMultiplicity

/-!
Exact normalized-chart projective dimension of the gradient-image cone,
and the strict generic-fiber threshold needed for terminal Gauss strata.
All cubic irreducibility and Hessian-degree ingredients are proved.
-/
noncomputable section
namespace CubicTenVariables.GaussDualDimension
open HessianTheorem11 GaussImageGeometry BibleProjectiveGeometry

/-- The proved Hessian determinant multiplicity bound supplies the generic
rank lower bound, with the actual anisotropic polynomial as the only input. -/
theorem rank_corank_degree_bound {n : ℕ} (F : AnisotropicCubic n) (hn : 4 ≤ n) :
    3 * (n - genericHessianRank F.polynomial) ≤ n :=
  anisotropic_generic_corank_degree_bound ReducedGenericRank.genericMatrixRankInput
    (provedDeterminantalTangentOver ℚ) F (Unconditional.cubicGeometricIrreducibility F hn)

/-- Exact projective dimension, using actual normalized geometric charts.
The cone/image dimension formula is proved in GaussImageGeometry. -/
theorem projective_gradient_image_dimension {n : ℕ} (F : AnisotropicCubic n)
    (hn : 4 ≤ n) :
    projectiveDimension (gradientImage (geometricPolynomial F.polynomial)) =
      ((genericHessianRank F.polynomial - 2 : ℕ) : Dimension) := by
  have hdegree := rank_corank_degree_bound F hn
  have hrn := genericHessianRank_le F.polynomial
  have htwo : 2 ≤ genericHessianRank F.polynomial := by omega
  have he : genericHessianRank F.polynomial - 1 =
      genericHessianRank F.polynomial - 2 + 1 := by omega
  have hc := gradientImage_closed (geometricPolynomial F.polynomial)
  have hcone := gradientImage_isAffineCone _ (geometric_homogeneous F.homogeneous)
  have hd := anisotropic_gradient_image_dimension F hn
  apply le_antisymm
  · apply (TerminalProjectiveDimension.projectiveDimension_le_nat_iff _ hc hcone _).mpr
    rw [hd, he]
  · apply (TerminalProjectiveDimension.nat_le_projectiveDimension_iff _ hc hcone _).mpr
    rw [hd, he]

/-- The source condition 3t>n makes t+1 strictly larger than the generic
affine Gauss-graph fiber dimension n-(r_X-1). -/
theorem terminal_threshold_above_generic {n t : ℕ} (F : AnisotropicCubic n)
    (hn : 4 ≤ n) (ht : n < 3 * t) :
    n - (genericHessianRank F.polynomial - 1) < t + 1 := by
  have hdegree := rank_corank_degree_bound F hn
  have hrn := genericHessianRank_le F.polynomial
  omega

end CubicTenVariables.GaussDualDimension
