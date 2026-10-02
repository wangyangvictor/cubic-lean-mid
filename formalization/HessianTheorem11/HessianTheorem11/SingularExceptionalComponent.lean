import HessianTheorem11.ConeComponents
import HessianTheorem11.ConePointSelection
import HessianTheorem11.SingularGeometry
import HessianTheorem11.SingularNormalEquations
import HessianTheorem11.GradientCoisotropy
import HessianTheorem11.BasicLoci

/-! A violation of either remaining singular-locus bound has an actual
closed irreducible cone component of dimension n-5 and generic Hessian
rank five. All component selection and radial numerics are constructed
from the already permitted general textbook inputs. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module Matrix
variable {n e : ℕ}

theorem finiteEquationZeroSet_closed (q : Fin e → GeometricPolynomial n) :
    AlgebraicallyClosedSet (finiteEquationZeroSet q) := by
  have he : finiteEquationZeroSet q = zeroLocus GeometricField (Ideal.span (Set.range q)) := by
    ext x
    rw [zeroLocus_span]
    constructor
    · intro hx P hP
      obtain ⟨i,rfl⟩ := hP
      exact hx i
    · intro hx i
      exact hx (q i) ⟨i,rfl⟩
  rw [he]
  exact algebraicallyClosedSet_zeroLocus _

theorem finiteQuadraticZeroSet_cone (q : Fin e → GeometricPolynomial n)
    (hq : ∀ i, (q i).IsHomogeneous 2) : IsAffineCone (finiteEquationZeroSet q) := by
  intro a x hx i
  rw [SingularNormalEquations.eval_quadratic_smul (q i) (hq i), hx i, mul_zero]

theorem singularLocus_closed (F : RationalPolynomial n) : AlgebraicallyClosedSet (singularLocus F) := by
  rw [← singular_equation_zeroSet]
  exact finiteEquationZeroSet_closed _

theorem singularLocus_cone (F : RationalPolynomial n) (hF : F.IsHomogeneous 3) :
    IsAffineCone (singularLocus F) := by
  rw [← singular_equation_zeroSet]
  exact finiteQuadraticZeroSet_cone _ (fun i => (geometric_homogeneous hF).pderiv)

/-- The radial vector belongs to the embedded tangent of any affine cone. -/
theorem IsAffineCone.radial_tangent {Z : Set (GeometricPoint n)}
    (hZ : IsAffineCone Z) (x : GeometricPoint n) (hx : x ∈ Z) :
    x ∈ affineTangentSpace Z x := by
  let S : Submodule GeometricField (GeometricPoint n) := Submodule.span GeometricField {x}
  have hmem : x ∈ S := Submodule.subset_span (Set.mem_singleton x)
  have hs : (S : Set (GeometricPoint n)) ⊆ Z := by
    intro y hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact hZ a x hx
  exact submodule_le_affineTangentSpace_of_subset S Z hs x hmem hmem

structure SingularRankFiveException (F : AnisotropicCubic n) where
  base : Set (GeometricPoint n)
  component : IsIrreducibleComponent (singularLocus F.polynomial) base
  cone : IsAffineCone base
  generic : GenericRankOpen base (fun i => pderiv i (geometricPolynomial F.polynomial))
    (hessianLinearMap (geometricPolynomial F.polynomial) (geometric_homogeneous F.homogeneous))
  dimension : affineDimension base = ((n - 5 : ℕ) : Dimension)
  rank_five : ∀ y ∈ generic.openSet, (hessian (geometricPolynomial F.polynomial) y).rank = 5

namespace SingularRankFiveException
variable {F : AnisotropicCubic n}

theorem singular (E : SingularRankFiveException F) :
    ∀ z ∈ E.base, gradient (geometricPolynomial F.polynomial) z = 0 :=
  E.component.subset

theorem tangent_dimension (E : SingularRankFiveException F)
    (y : GeometricPoint n) (hy : y ∈ E.generic.openSet) :
    finrank GeometricField (affineTangentSpace E.base y) = n - 5 := by
  have hd : E.generic.baseDimension = n - 5 := by
    exact_mod_cast E.generic.dimension_base.symm.trans E.dimension
  rw [E.generic.smooth y hy, hd]

theorem point_nonzero (E : SingularRankFiveException F)
    (y : GeometricPoint n) (hy : y ∈ E.generic.openSet) : y ≠ 0 := by
  intro hz
  have hr := E.rank_five y hy
  rw [hz, hessian_zero (geometric_homogeneous F.homogeneous), Matrix.rank_zero] at hr
  omega

theorem smooth (E : SingularRankFiveException F)
    (y : GeometricPoint n) (hy : y ∈ E.generic.openSet) :
    affineDimension E.base = (finrank GeometricField (affineTangentSpace E.base y) : Dimension) := by
  rw [E.tangent_dimension y hy]
  exact E.dimension

theorem radial (E : SingularRankFiveException F)
    (y : GeometricPoint n) (hy : y ∈ E.generic.openSet) : y ∈ affineTangentSpace E.base y :=
  E.cone.radial_tangent y (E.generic.subset hy)

theorem tangent_eq_kernel (E : SingularRankFiveException F)
    (hn : 5 ≤ n) (y : GeometricPoint n) (hy : y ∈ E.generic.openSet) :
    affineTangentSpace E.base y = LinearMap.ker (hessian (geometricPolynomial F.polynomial) y).mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq (affineTangentSpace_le_hessian_ker _ E.base E.singular y)
  have hh := (hessian (geometricPolynomial F.polynomial) y).mulVecLin.finrank_range_add_finrank_ker
  change (hessian (geometricPolynomial F.polynomial) y).rank + _ =
    finrank GeometricField (GeometricPoint n) at hh
  rw [E.rank_five y hy, show finrank GeometricField (GeometricPoint n) = n by simp] at hh
  rw [E.tangent_dimension y hy]
  omega

end SingularRankFiveException

/-- The elementary radial inequalities isolate precisely the rank-five
exception in dimensions eleven and twelve. -/
theorem singular_violation_has_rank_five_exception
    (AC : AffineComponentsInput) (GP : GenericConePointSelectionInput)
    (GR : GenericRankOpenInput) (DT : SymmetricDeterminantalTangentInput)
    (F : AnisotropicCubic n) (hn : n = 11 ∨ n = 12)
    (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (hbad : ((n - 6 : ℕ) : Dimension) < singularDimension F.polynomial) :
    Nonempty (SingularRankFiveException F) := by
  obtain ⟨Z,hZ,hdim⟩ := AC.maximal_dimension_component (singularLocus F.polynomial)
    (singularLocus_closed F.polynomial) ⟨0, origin_mem_singularLocus F⟩
  have hcone := hZ.isAffineCone AC (singularLocus_closed F.polynomial)
    (singularLocus_cone F.polynomial F.homogeneous)
  have hlow : ((n - 6 : ℕ) : Dimension) < affineDimension Z := by
    rw [hdim]
    exact hbad
  have hnonorigin : ¬ Z ⊆ {0} := by
    intro h
    have hd := affineDimension_mono h
    rw [affineDimension_singleton] at hd
    have hzero : (0 : Dimension) ≤ ((n - 6 : ℕ) : Dimension) := by simp
    exact (not_lt_of_ge (hd.trans hzero)) hlow
  let M := hessianLinearMap (geometricPolynomial F.polynomial) (geometric_homogeneous F.homogeneous)
  let q := fun i => pderiv i (geometricPolynomial F.polynomial)
  let P := GP.choose Z hZ.closed hZ.irreducible hcone hnonorigin M q
  have hsing : ∀ z ∈ Z, gradient (geometricPolynomial F.polynomial) z = 0 := hZ.subset
  have hmax : ∀ y ∈ Z, (hessian (geometricPolynomial F.polynomial) y).rank ≤
      (hessian (geometricPolynomial F.polynomial) P.point).rank := P.rank_maximal
  have htensor := hessian_tangent_polarization_zero DT (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous) Z P.point P.member hmax
  have hrad := singular_radial_of_tensor_vanishing (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous) hsemi P.point P.nonzero
    (affineTangentSpace Z P.point) P.radial
    (affineTangentSpace_le_hessian_ker _ Z hsing P.point) htensor
  have hrk := hessian_rank_add_tangent_finrank_le (geometricPolynomial F.polynomial) Z hsing P.point
  have htlow : n - 6 < finrank GeometricField (affineTangentSpace Z P.point) := by
    rw [P.dimension] at hlow
    exact_mod_cast hlow
  have ht : finrank GeometricField (affineTangentSpace Z P.point) = n - 5 := by
    rcases hn with hn | hn <;> omega
  have hr : (hessian (geometricPolynomial F.polynomial) P.point).rank = 5 := by
    rcases hn with hn | hn <;> omega
  obtain ⟨G⟩ := GR.choose Z hZ.closed hZ.irreducible q M
  refine ⟨⟨Z,hZ,hcone,G,?_,?_⟩⟩
  · rw [P.dimension, ht]
  · intro y hy
    apply Nat.le_antisymm
    · simpa only [hr] using hmax y (G.subset hy)
    · have h := G.maximal_rank y hy P.point P.member
      change (hessian (geometricPolynomial F.polynomial) P.point).rank ≤
        (hessian (geometricPolynomial F.polynomial) y).rank at h
      rwa [hr] at h

end HessianTheorem11
