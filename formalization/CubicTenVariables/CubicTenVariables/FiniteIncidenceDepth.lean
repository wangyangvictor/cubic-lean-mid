import CubicTenVariables.FiberJumpDimension
import CubicTenVariables.TerminalFiberCoordinates
import CubicTenVariables.HomogeneousFamilyBadLocus

/-! Literal depth loci of a finite affine incidence. Fiber dimensions are
preserved by the actual point/normal coordinate maps. A finite union has
a large fiber exactly when one member does, including an empty family.
These are adapters for a supplied singular-support incidence; this file
does not assert existence or the conormal structure of singular support. -/

noncomputable section
namespace CubicTenVariables.FiniteIncidenceDepth
open MvPolynomial HessianTheorem11
open TerminalFiberCoordinates FiberJumpDimension

variable {a m n : ℕ} {ι : Type*}

/-- The literal point fiber of a two-block incidence, in the existing
coordinate convention (point, normal). -/
def pointFiber (C : Set (GeometricPoint (n+n))) (v : GeometricPoint n) :
    Set (GeometricPoint n) :=
  {x | polynomialMap (fixedNormalSection v) x ∈ C}

theorem point_image_fiber (C : Set (GeometricPoint (n+n))) (v : GeometricPoint n) :
    polynomialMap (pointProjection n) ''
      {y | y ∈ C ∧ polynomialMap (normalProjection n) y = v} = pointFiber C v := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hyv⟩, rfl⟩
    change polynomialMap (fixedNormalSection v) (polynomialMap (pointProjection n) y) ∈ C
    simpa only [section_pointProjection v y hyv] using hy
  · intro hx
    exact ⟨polynomialMap (fixedNormalSection v) x,
      ⟨hx, normalProjection_section v x⟩, pointProjection_section v x⟩

theorem pointFiber_dimension (C : Set (GeometricPoint (n+n))) (v : GeometricPoint n) :
    affineDimension (pointFiber C v) =
      affineDimension {y | y ∈ C ∧ polynomialMap (normalProjection n) y = v} := by
  rw [← point_image_fiber]
  exact fiber_dimension C v

/-- The polynomial-map depth is exactly the depth of the literal x-fiber. -/
theorem largeFiberParameters_eq_pointFiber (C : Set (GeometricPoint (n+n))) (j : ℕ) :
    largeFiberParameters (normalProjection n) C j =
      {v | (j : Dimension) ≤ affineDimension (pointFiber C v)} := by
  ext v
  change (j : Dimension) ≤ _ ↔ (j : Dimension) ≤ _
  rw [pointFiber_dimension]

/-- Finite positive homogeneous fiber equations prove closedness of the
raw depth locus. No closure is inserted into the definition. -/
theorem depth_closed_of_equations [Fintype ι]
    (C : Set (GeometricPoint (n+n)))
    (f : ι → MvPolynomial (Fin n) (GeometricPolynomial n)) (e : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (e i)) (he : ∀ i, 0 < e i)
    (hmodel : ∀ v, pointFiber C v = HomogeneousFamilyBadLocus.fiber f v) (t : ℕ) :
    AlgebraicallyClosedSet (largeFiberParameters (normalProjection n) C (t+1)) := by
  rw [largeFiberParameters_eq_pointFiber]
  simp_rw [hmodel]
  exact HomogeneousFamilyBadLocus.badParameters_closed f e hf he t

/-- Separate normal-scalar stability of the supplied incidence is sufficient
for the depth loci to be cones, including scaling the normal to zero. -/
theorem depth_isAffineCone (C : Set (GeometricPoint (n+n)))
    (hscale : ∀ (v : GeometricPoint n) (b : GeometricField),
      pointFiber C v ⊆ pointFiber C (b • v)) (j : ℕ) :
    IsAffineCone (largeFiberParameters (normalProjection n) C j) := by
  rw [largeFiberParameters_eq_pointFiber]
  intro b v hv
  exact hv.trans (affineDimension_mono (hscale v b))

theorem mapFiber_iUnion (P : Fin m → GeometricPolynomial a)
    (Y : ι → Set (GeometricPoint a)) (v : GeometricPoint m) :
    {x | x ∈ ⋃ i, Y i ∧ polynomialMap P x = v} =
      ⋃ i, {x | x ∈ Y i ∧ polynomialMap P x = v} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_and_right]

/-- Exact finite-union formula; no irreducibility or closedness is required. -/
theorem largeFiberParameters_iUnion [Fintype ι]
    (P : Fin m → GeometricPolynomial a) (Y : ι → Set (GeometricPoint a)) (j : ℕ) :
    largeFiberParameters P (⋃ i, Y i) j = ⋃ i, largeFiberParameters P (Y i) j := by
  classical
  ext v
  change (j : Dimension) ≤ affineDimension {x | x ∈ ⋃ i, Y i ∧ polynomialMap P x = v} ↔ _
  rw [mapFiber_iUnion]
  have hd := affineDimension_finset_union Finset.univ
    (fun i => {x | x ∈ Y i ∧ polynomialMap P x = v})
  simp only [Finset.mem_univ, Set.iUnion_true] at hd
  rw [hd, Finset.le_sup_iff (show (⊥ : Dimension) < (j : Dimension) from WithBot.bot_lt_coe _)]
  simp only [Finset.mem_univ, true_and, Set.mem_iUnion, largeFiberParameters, Set.mem_setOf_eq]

theorem closed_finset_union (s : Finset ι) (Y : ι → Set (GeometricPoint m))
    (hY : ∀ i ∈ s, AlgebraicallyClosedSet (Y i)) :
    AlgebraicallyClosedSet (⋃ i ∈ s, Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (algebraicallyClosedSet_zeroLocus (⊤ : Ideal (GeometricPolynomial m)))
  | @insert i s hi ih =>
      simpa only [Finset.set_biUnion_insert] using
        (hY i (Finset.mem_insert_self i s)).union
          (ih (fun j hj => hY j (Finset.mem_insert_of_mem hj)))

theorem closed_iUnion [Fintype ι] (Y : ι → Set (GeometricPoint m))
    (hY : ∀ i, AlgebraicallyClosedSet (Y i)) : AlgebraicallyClosedSet (⋃ i, Y i) := by
  simpa using closed_finset_union Finset.univ Y (fun i _ => hY i)

theorem closure_iUnion [Fintype ι] (Y : ι → Set (GeometricPoint m)) :
    geometricClosure (⋃ i, Y i) = ⋃ i, geometricClosure (Y i) := by
  apply Set.Subset.antisymm
  · apply geometricClosure_subset_closed
    · exact Set.iUnion_mono (fun i => subset_geometricClosure (Y i))
    · exact closed_iUnion _ (fun i => algebraicallyClosedSet_geometricClosure (Y i))
  · apply Set.iUnion_subset
    intro i
    exact geometricClosure_mono (Set.subset_iUnion Y i)

theorem depth_closure_iUnion [Fintype ι]
    (P : Fin m → GeometricPolynomial a) (Y : ι → Set (GeometricPoint a)) (j : ℕ) :
    geometricClosure (largeFiberParameters P (⋃ i, Y i) j) =
      ⋃ i, geometricClosure (largeFiberParameters P (Y i) j) := by
  rw [largeFiberParameters_iUnion, closure_iUnion]

end CubicTenVariables.FiniteIncidenceDepth
