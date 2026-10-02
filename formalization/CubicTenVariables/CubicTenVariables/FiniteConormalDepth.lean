import CubicTenVariables.FiniteIncidenceDepth
import CubicTenVariables.ConormalDepthDimension
import CubicTenVariables.RationalConormalAnisotropy
import CubicTenVariables.GeometricTerminalBound

/-! Geometric depth and rational codimension gain for a supplied finite
conormal incidence. Every component and fiber is an actual algebraic point
set. The conormal-on-open and hypersurface-support conditions remain explicit;
existence of the singular-support incidence is not asserted here. -/

noncomputable section
namespace CubicTenVariables.FiniteConormalDepth
open MvPolynomial HessianTheorem11 Module
open FiberJumpDimension TerminalFiberCoordinates FiniteIncidenceDepth
open RationalConeClosure RationalConeComponents

/-- Finite components of dimension n give the geometric codimension-j
bound for the actual large-fiber locus and its closure. -/
theorem depth_closure_dimension_le {a m n c j : ℕ}
    (P : Fin m → GeometricPolynomial a) (Y : Fin c → Set (GeometricPoint a))
    (hY : ∀ i, AlgebraicallyClosedSet (Y i))
    (hiY : ∀ i, GeometricallyIrreducible (Y i))
    (hdY : ∀ i, affineDimension (Y i) = (n : Dimension)) (hj : 0 < j) :
    affineDimension (geometricClosure (largeFiberParameters P (⋃ i, Y i) j)) ≤
      ((n-j : ℕ) : Dimension) := by
  rw [depth_closure_iUnion]
  apply affineDimension_fintype_union_le
  intro i
  have hiD : GeometricallyIrreducible (geometricClosure (polynomialMap P '' Y i)) :=
    (geometricallyIrreducible_closure_iff _).mpr ((hiY i).polynomialMap_image P)
  obtain ⟨s, hs⟩ := ReducedComponentDimension.finite_dimension _ hiD.nonempty
  exact ConormalDepthDimension.closure_dimension_le P (Y i) (hY i) (hiY i) (hdY i) hs hj

/-- The image closure of each actual conormal component is its base. -/
def base {n : ℕ} (Y : Set (GeometricPoint (n+n))) : Set (GeometricPoint n) :=
  geometricClosure (polynomialMap (normalProjection n) '' Y)

/-- Rational anisotropy improves the depth codimension by one. The conormal
condition is only required on a nonempty open in each actual image base.
The range 0<j<n is intentional: the rational closure adjoins the origin. -/
theorem rational_depth_closure_dimension_le {n c j : ℕ}
    (F : RationalPolynomial n) (hF : Anisotropic F)
    (Y : Fin c → Set (GeometricPoint (n+n)))
    (hY : ∀ i, AlgebraicallyClosedSet (Y i))
    (hiY : ∀ i, GeometricallyIrreducible (Y i))
    (hdY : ∀ i, affineDimension (Y i) = (n : Dimension))
    (O : Fin c → Set (GeometricPoint n))
    (hO : ∀ i, RelativelyOpenSet (base (Y i)) (O i))
    (hneO : ∀ i, (O i).Nonempty)
    (hconormal : ∀ i v, v ∈ O i →
      (coordinatePairing.orthogonal (affineTangentSpace (base (Y i)) v) :
        Set (GeometricPoint n)) ⊆ pointFiber (Y i) v)
    (hsupport : ∀ i v, pointFiber (Y i) v ⊆ cubicLocus F)
    (hj : 0 < j) (hjn : j < n) :
    affineDimension (rationalConeClosure
      (geometricClosure (largeFiberParameters (normalProjection n) (⋃ i, Y i) j))) ≤
        ((n-(j+1) : ℕ) : Dimension) := by
  let L := geometricClosure (largeFiberParameters (normalProjection n) (⋃ i, Y i) j)
  have hL : AlgebraicallyClosedSet L := algebraicallyClosedSet_geometricClosure _
  have hdL : affineDimension L ≤ ((n-j : ℕ) : Dimension) :=
    depth_closure_dimension_le (normalProjection n) Y hY hiY hdY hj
  have hdR : affineDimension (rationalConeClosure L) ≤ ((n-j : ℕ) : Dimension) := by
    apply (affineDimension_mono (rationalConeClosure_subset L hL)).trans
    rw [affineDimension_union]
    apply max_le hdL
    rw [affineDimension_singleton]
    exact_mod_cast (Nat.zero_le (n-j))
  obtain ⟨r, K, hcover, hK⟩ := ReducedMaximalComponent.finite_components
    (rationalConeClosure L) (rationalConeClosure_closed L)
  change affineDimension (rationalConeClosure L) ≤ _
  rw [hcover]
  apply affineDimension_fintype_union_le
  intro k
  obtain ⟨z, hz⟩ := ReducedComponentDimension.finite_dimension (K k)
    (hK k).irreducible.nonempty
  have hzle : z ≤ n-j := by
    have h := (affineDimension_mono (hK k).subset).trans hdR
    rw [hz] at h
    exact_mod_cast h
  suffices z ≤ n-(j+1) by
    rw [hz]
    exact_mod_cast this
  by_contra hnot
  have hzEq : z = n-j := by omega
  have hkdim : affineDimension (K k) = ((n-j : ℕ) : Dimension) := hz.trans (by rw [hzEq])
  let D : Fin (c+1) → Set (GeometricPoint n) :=
    Fin.cases {0} (fun i => geometricClosure
      (largeFiberParameters (normalProjection n) (Y i) j))
  have hD (i : Fin (c+1)) : AlgebraicallyClosedSet (D i) :=
    Fin.cases origin_closed (fun _ => algebraicallyClosedSet_geometricClosure _) i
  have hKD : K k ⊆ ⋃ i, D i := by
    intro x hx
    rcases rationalConeClosure_subset L hL ((hK k).subset hx) with hxL | hx0
    · change x ∈ geometricClosure
        (largeFiberParameters (normalProjection n) (⋃ i, Y i) j) at hxL
      rw [depth_closure_iUnion] at hxL
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxL
      exact Set.mem_iUnion.mpr ⟨i.succ, hi⟩
    · exact Set.mem_iUnion.mpr ⟨0, hx0⟩
  obtain ⟨i, hi⟩ := GeometricTerminalBound.subset_one_of_finite_closed_cover
    (K k) (hK k).irreducible D hD hKD
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · have hsmall := affineDimension_mono hi
    change affineDimension (K k) ≤ affineDimension ({0} : Set (GeometricPoint n)) at hsmall
    rw [hkdim, affineDimension_singleton] at hsmall
    have hnat : n-j ≤ 0 := by exact_mod_cast hsmall
    omega
  · have hiBase : GeometricallyIrreducible (base (Y i)) :=
      (geometricallyIrreducible_closure_iff _).mpr
        ((hiY i).polynomialMap_image (normalProjection n))
    obtain ⟨s, hs⟩ := ReducedComponentDimension.finite_dimension _ hiBase.nonempty
    obtain ⟨_, heq⟩ := ConormalDepthDimension.closed_subset_eq_imageClosure_of_dimension_eq
      (normalProjection n) (Y i) (hY i) (hiY i) (hdY i) hs hj hjn
      (K k) (hK k).closed hi hkdim
    have hbaseEq : K k = base (Y i) := heq
    have hOK : RelativelyOpenSet (K k) (O i) := by
      rw [hbaseEq]
      exact hO i
    obtain ⟨q, hqO, hqs⟩ := exists_rational_smooth_point_in_component_open
      L (K k) hL (hK k) (O i) hOK (hneO i)
    apply RationalConormalAnisotropy.smooth_tangent_annihilator_not_subset
      F hF L (K k) hL (hK k) hkdim (by omega) q hqs
    rw [hbaseEq]
    exact (hconormal i (rationalEmbedding q) hqO).trans (hsupport i (rationalEmbedding q))

end CubicTenVariables.FiniteConormalDepth
