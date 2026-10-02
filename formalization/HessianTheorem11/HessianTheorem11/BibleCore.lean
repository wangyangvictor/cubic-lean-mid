import HessianTheorem11.UnconditionalWeightDescent
import HessianTheorem11.ReducedClosedOrbitZero
import HessianTheorem11.CubicIrreducibility
import HessianTheorem11.GeometricFactorization
import HessianTheorem11.GenericRankBridge
import HessianTheorem11.GeometricInjectivity
import HessianTheorem11.AffineHypersurfaceDimension
import HessianTheorem11.Concentration
import HessianTheorem11.IncidenceRadial
import HessianTheorem11.RationalDescent

/-! Core geometric assertions and the kernel-bundle lower bound for
Theorem I.1.1. The source rank bound is derived from incidence dimension,
without invoking the stronger completed numerical rank theorem. -/

noncomputable section
namespace HessianTheorem11.BibleCore
open MvPolynomial Module RationalDescent

/-- The actual geometric principal coordinate ring is a domain. -/
theorem geometric_coordinateRing_isDomain
    (CI : CubicGeometricIrreducibility) (DTQ : DeterminantalTangentOver ℚ)
    {n : ℕ} (F : AnisotropicCubic n) (hn : 4 ≤ n) :
    IsDomain (cubicCoordinateRing F.polynomial) :=
  cubicCoordinateRing_isDomain F.polynomial
    (CI F hn)

/-- The geometric vanishing-ideal coordinate ring is the same integral
coordinate ring; thus reducedness is not an extra hypothesis. -/
theorem geometric_reduced_coordinateRing_isDomain
    (CI : CubicGeometricIrreducibility) (DTQ : DeterminantalTangentOver ℚ)
    {n : ℕ} (F : AnisotropicCubic n) (hn : 4 ≤ n) :
    IsDomain (GeometricPolynomial n ⧸ vanishingIdeal GeometricField (cubicLocus F.polynomial)) := by
  rw [vanishingIdeal_cubicLocus_eq F.polynomial
    (CI F hn)]
  exact geometric_coordinateRing_isDomain CI DTQ F hn

/-- Both the rational and geometric Hessian pencils are injective, and
their actual determinant polynomials are nonzero. -/
theorem hessian_injective_and_determinant_nonzero
    (DTQ : DeterminantalTangentOver ℚ) {n : ℕ} (F : AnisotropicCubic n) :
    Function.Injective (hessian F.polynomial) ∧
    Function.Injective (hessian (geometricPolynomial F.polynomial)) ∧
    hessianDeterminantPolynomial F.polynomial ≠ 0 ∧
    hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0 :=
  ⟨rational_hessian_injective F, geometric_hessian_injective F,
    anisotropic_hessianDeterminantPolynomial_ne_zero DTQ F,
    geometric_hessianDeterminantPolynomial_ne_zero DTQ F⟩

/-- The incidence contains the actual kernel bundle over the maximum-rank
open of the integral cubic. Its dimension is (n-1)+(n-r_X). -/
theorem incidenceDimension_lower_bound
    (GR : GenericRankOpenInput) (KI : KernelBundleInput)
    (AD : AffineHypersurfaceDimensionInput) {n : ℕ}
    (F : RationalPolynomial n) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible (geometricPolynomial F)) :
    ((n-1+(n-genericHessianRank F) : ℕ) : Dimension) ≤ incidenceDimension F := by
  let U := cubicLocus F
  let M := hessianLinearMap (geometricPolynomial F) (geometric_homogeneous hF)
  have hc : AlgebraicallyClosedSet U := polynomialHypersurface_closed _
  have hi : GeometricallyIrreducible U := polynomialHypersurface_irreducible _ hirred
  obtain ⟨G⟩ := GR.choose U hc hi (fun _ : Fin 0 => (0 : GeometricPolynomial n)) M
  obtain ⟨x,hx⟩ := G.nonempty
  have hrank : (hessian (geometricPolynomial F) x).rank = genericHessianRank F := by
    apply le_antisymm (rank_le_genericHessianRank F (G.subset hx))
    apply csSup_le'
    rintro r ⟨y,hy,rfl⟩
    exact G.maximal_rank x hx y hy
  have hker := G.kernel_dimension x hx
  change finrank GeometricField (LinearMap.ker (hessian (geometricPolynomial F) x).mulVecLin) =
    G.nullity at hker
  have hsum := (hessian (geometricPolynomial F) x).mulVecLin.finrank_range_add_finrank_ker
  change (hessian (geometricPolynomial F) x).rank +
    finrank GeometricField (LinearMap.ker (hessian (geometricPolynomial F) x).mulVecLin) =
      finrank GeometricField (GeometricPoint n) at hsum
  rw [hrank,hker] at hsum
  have hn : finrank GeometricField (GeometricPoint n) = n := by simp
  rw [hn] at hsum
  have hnull : G.nullity = n-genericHessianRank F := by omega
  have hdim := KI.dimension M U G.openSet hc hi G.isOpen G.dense (n-1) G.nullity
    (AD.hypersurface _ hirred) G.kernel_dimension
  have hsub : kernelBundle M G.openSet ⊆ incidenceLocus F := by
    intro p hp
    exact hp.2
  calc
    ((n-1+(n-genericHessianRank F) : ℕ) : Dimension) =
        affineDimension (kernelBundle M G.openSet) := by rw [hdim,hnull]
    _ ≤ incidenceDimension F := affineDimension_mono hsub

/-- The same lower bound with the actual matrix rank over the fraction
field of the cubic's geometric coordinate ring. -/
theorem incidenceDimension_genericPoint_lower_bound
    (GR : GenericRankOpenInput) (KI : KernelBundleInput)
    (AD : AffineHypersurfaceDimensionInput) (MR : GenericMatrixRankInput) {n : ℕ}
    (F : RationalPolynomial n) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible (geometricPolynomial F)) :
    ((n-1+(n-genericPointHessianRank F) : ℕ) : Dimension) ≤ incidenceDimension F := by
  rw [← genericHessianRank_eq_genericPointHessianRank MR F hirred]
  exact incidenceDimension_lower_bound GR KI AD F hF hirred

theorem incidenceDimension_twelve_lower_bound
    (GR : GenericRankOpenInput) (KI : KernelBundleInput)
    (AD : AffineHypersurfaceDimensionInput)
    (CI : CubicGeometricIrreducibility) (DTQ : DeterminantalTangentOver ℚ)
    (F : AnisotropicCubic 12) :
    ((11+(12-genericHessianRank F.polynomial) : ℕ) : Dimension) ≤
      incidenceDimension F.polynomial :=
  incidenceDimension_lower_bound GR KI AD F.polynomial F.homogeneous
    (CI F (by norm_num))

/-- Source bound fifteen, obtained directly from concentration and radial
weights; the stronger completed twelve-variable incidence theorem is not used. -/
theorem incidenceDimension_twelve_le_fifteen
    (AG : ConcentrationGeometryInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput)
    (F : AnisotropicCubic 12) :
    incidenceDimension F.polynomial ≤ 15 := by
  obtain ⟨C⟩ := incidence_concentration AG DT (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous)
  obtain ⟨d,hd,hnum⟩ := incidence_radial_of_concentrated_base GP DT F.polynomial
    F.homogeneous (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F (by norm_num))
    C.base C.closed C.irreducible C.cone C.contained C.baseDimension C.rank C.nullity
    C.dimension_base C.dimension_incidence C.rank_nullity C.rank_attained C.maximal_rank
  have hbound : d ≤ 15 := by rcases hnum with h | h <;> omega
  rw [hd]
  exact_mod_cast hbound

/-- The requested arithmetic implication on the actual incidence and rank. -/
theorem rank_eight_of_incidence_le_fifteen
    (GR : GenericRankOpenInput) (KI : KernelBundleInput)
    (AD : AffineHypersurfaceDimensionInput)
    (CI : CubicGeometricIrreducibility) (DTQ : DeterminantalTangentOver ℚ)
    (F : AnisotropicCubic 12) (hI : incidenceDimension F.polynomial ≤ 15) :
    8 ≤ genericHessianRank F.polynomial := by
  have hlo := incidenceDimension_twelve_lower_bound GR KI AD CI DTQ F
  have hnat : 11+(12-genericHessianRank F.polynomial) ≤ 15 := by
    exact_mod_cast hlo.trans hI
  omega

/-- The source rank bound is derived from the source incidence bound and
the actual kernel bundle over X, independently of Completed.R12. -/
theorem rank_eight_via_incidence
    (AG : ConcentrationGeometryInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput) (AD : AffineHypersurfaceDimensionInput)
    (DTQ : DeterminantalTangentOver ℚ) (CI : CubicGeometricIrreducibility)
    (F : AnisotropicCubic 12) :
    8 ≤ genericHessianRank F.polynomial :=
  rank_eight_of_incidence_le_fifteen AG.toGenericRankOpenInput AG.toKernelBundleInput AD CI DTQ F
    (incidenceDimension_twelve_le_fifteen AG GP DT  F)

end HessianTheorem11.BibleCore
