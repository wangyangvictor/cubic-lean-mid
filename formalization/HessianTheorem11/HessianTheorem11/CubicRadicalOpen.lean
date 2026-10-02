import HessianTheorem11.CubicDivisorPoint
import HessianTheorem11.KernelAnnihilatorGeometry
import HessianTheorem11.AffineHypersurfaceDimension

/-! A genuine dense open of the cubic on which its intrinsic radical is a
vector bundle, with every point smooth, of maximal Hessian rank, and away
from the residual Hessian divisor. The good open is constructed using only
the general kernel-bundle theorem and the previously proved divisor data. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

structure CubicRadicalOpen {n : ℕ} (F : GeometricPolynomial n) where
  divisor : CubicDivisorPoint F
  openSet : Set (GeometricPoint n)
  isOpen : RelativelyOpenSet (polynomialHypersurface F) openSet
  dense : geometricClosure openSet = polynomialHypersurface F
  nonempty : openSet.Nonempty
  subset : openSet ⊆ polynomialHypersurface F
  smooth : ∀ x ∈ openSet, gradient F x ≠ 0
  rank_eq : ∀ x ∈ openSet, (hessian F x).rank = geometricCubicGenericRank F
  residual_nonzero : ∀ x ∈ openSet, eval x divisor.residual ≠ 0
  nullity : ℕ
  dimension_kernel : ∀ x ∈ openSet, finrank GeometricField (intrinsicRadical F x) = nullity
  bundle_irreducible : GeometricallyIrreducible (radicalBundle F openSet)
  bundle_locally_closed : RelativelyOpenSet (geometricClosure (radicalBundle F openSet))
    (radicalBundle F openSet)
  bundle_dimension : affineDimension (radicalBundle F openSet) = ((n - 1 + nullity : ℕ) : Dimension)

theorem exists_cubicRadicalOpen
    (MR : GenericMatrixRankInput) (KA : KernelAnnihilatorGeometryInput)
    (AD : AffineHypersurfaceDimensionInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hirred : Irreducible F) (hdet : hessianDeterminantPolynomial F ≠ 0) :
    Nonempty (CubicRadicalOpen F) := by
  classical
  obtain ⟨P⟩ := exists_cubicDivisorPoint MR F hF hirred hdet
  obtain ⟨i, hi⟩ : ∃ i, eval P.point (pderiv i F) ≠ 0 := by
    by_contra h
    push_neg at h
    apply P.smooth
    ext i
    exact h i
  let Q := P.residual * pderiv i F
  have hQ : ∃ x ∈ polynomialHypersurface F, eval x Q ≠ 0 := by
    refine ⟨P.point, P.on_cubic, ?_⟩
    simpa only [Q, map_mul] using mul_ne_zero P.residual_nonzero hi
  obtain ⟨G⟩ := KA.choose (polynomialHypersurface F) (polynomialHypersurface_closed F)
    (polynomialHypersurface_irreducible F hirred)
    (hessianLinearMap F hF) (hessianLinearMap F hF) Q hQ
  have hrank : ∀ x ∈ G.openSet, (hessian F x).rank = geometricCubicGenericRank F := by
    intro x hx
    rw [← P.rank_eq]
    apply le_antisymm
    · exact P.maximal_rank x (G.subset hx)
    · exact G.maximal_rank x hx P.point P.on_cubic
  have havoid : ∀ x ∈ G.openSet, eval x P.residual ≠ 0 ∧ eval x (pderiv i F) ≠ 0 := by
    intro x hx
    have h := G.avoids x hx
    simpa only [Q, map_mul, mul_ne_zero_iff] using h
  refine ⟨{
    divisor := P
    openSet := G.openSet
    isOpen := G.isOpen
    dense := G.dense
    nonempty := G.nonempty
    subset := G.subset
    smooth := ?_
    rank_eq := hrank
    residual_nonzero := fun x hx => (havoid x hx).1
    nullity := G.nullity
    dimension_kernel := ?_
    bundle_irreducible := ?_
    bundle_locally_closed := ?_
    bundle_dimension := ?_
  }⟩
  · intro x hx hg
    exact (havoid x hx).2 (congrFun hg i)
  · intro x hx
    exact G.dimension_kernel x hx
  · exact G.bundle_irreducible
  · exact G.bundle_locally_closed
  · exact G.bundle_dimension (n - 1) (AD.hypersurface F hirred)

/-- Every point on the chosen open carries the same genuine divisor data,
so all local normal-form arguments can be applied uniformly on that open. -/
def CubicRadicalOpen.divisorPointAt
    {n : ℕ} {F : GeometricPolynomial n} (O : CubicRadicalOpen F)
    (hF : F.IsHomogeneous 3) (x : GeometricPoint n) (hx : x ∈ O.openSet) :
    CubicDivisorPoint F := {
  O.divisor with
  point := x
  on_cubic := O.subset hx
  smooth := O.smooth x hx
  nonzero := by
    intro hz
    apply O.smooth x hx
    subst x
    ext j
    exact eval_origin_of_positive_homogeneous hF.pderiv (by norm_num)
  rank_eq := O.rank_eq x hx
  residual_nonzero := O.residual_nonzero x hx
  maximal_rank := by
    intro y hy
    rw [O.rank_eq x hx, ← O.divisor.rank_eq]
    exact O.divisor.maximal_rank y hy
}

end HessianTheorem11
