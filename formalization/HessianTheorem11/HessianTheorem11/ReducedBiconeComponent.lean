import HessianTheorem11.Concentration

/-! Component invariance under the two scalar actions, derived from the
ordinary zero-matrix kernel bundle and actual polynomial images. -/

noncomputable section
namespace HessianTheorem11.ReducedBiconeComponent
open MvPolynomial Module

theorem closed_empty {σ : Type*} : AlgebraicallyClosedSet (∅ : Set (σ → GeometricField)) := by
  apply le_antisymm _ (subset_geometricClosure _)
  intro x hx
  have h := hx 1 (by intro y hy; exact hy.elim)
  simp at h

theorem relativelyOpen_self {σ : Type*} (Z : Set (σ → GeometricField)) :
    RelativelyOpenSet Z Z := ⟨∅, closed_empty, Set.diff_empty.symm⟩

/-- A product with affine space is the actual kernel bundle of a zero matrix.
Only the ordinary bundle irreducibility field is used. -/
theorem zero_bundle_irreducible (KI : KernelBundleInput) {n : ℕ}
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hiZ : GeometricallyIrreducible Z) (k : ℕ) :
    GeometricallyIrreducible (kernelBundle
      (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin k) GeometricField) Z) := by
  apply (geometricallyIrreducible_closure_iff _).mp
  apply KI.closure_irreducible _ Z Z hZ hiZ (relativelyOpen_self Z) hZ k
  intro x hx
  change finrank GeometricField
    (LinearMap.ker (Matrix.mulVecLin (0 : Matrix (Fin 0) (Fin k) GeometricField))) = k
  rw [Matrix.mulVecLin_zero, LinearMap.ker_zero]
  simp

/-- The literal reindexing of the original two coordinate blocks. -/
def pairCoordinates (n m : ℕ) : PolynomialCoordinateEquiv (Fin n ⊕ Fin m) (Fin (n+m)) where
  forward j := X (finSumFinEquiv.symm j)
  inverse i := X (finSumFinEquiv i)
  forward_inverse i := by simp
  inverse_forward j := by simp

def scalePolynomials (n m : ℕ) :
    (Fin n ⊕ Fin m) → MvPolynomial (Fin (n+m) ⊕ Fin 2) GeometricField :=
  Sum.elim
    (fun i => X (Sum.inr 0) * X (Sum.inl (finSumFinEquiv (Sum.inl i))))
    (fun j => X (Sum.inr 1) * X (Sum.inl (finSumFinEquiv (Sum.inr j))))

theorem scalePolynomials_apply {n m : ℕ} (x : PairPoint n m) (s : GeometricPoint 2) :
    polynomialMap (scalePolynomials n m)
      (pairPoint ((pairCoordinates n m).forwardMap x) s) =
      pairPoint (s 0 • pairLeft x) (s 1 • pairRight x) := by
  ext (i | j) <;>
    simp [polynomialMap, scalePolynomials, pairPoint, pairLeft, pairRight,
      PolynomialCoordinateEquiv.forwardMap, pairCoordinates]

/-- The exact bicone-component field of the former AC interface, proved
from the ordinary kernel-bundle input alone. -/
theorem bicone_component (KI : KernelBundleInput) {n m : ℕ}
    (X Z : Set (PairPoint n m)) (hX : AlgebraicallyClosedSet X)
    (hbi : IsBicone X) (hZ : IsIrreducibleComponent X Z) : IsBicone Z := by
  let E := pairCoordinates n m
  let U := E.forwardMap '' Z
  have hU : AlgebraicallyClosedSet U := (E.algebraicallyClosedSet_image_iff Z).mpr hZ.closed
  have hiU : GeometricallyIrreducible U :=
    (E.geometricallyIrreducible_image_iff Z).mpr hZ.irreducible
  let M : GeometricPoint (n+m) →ₗ[GeometricField]
      Matrix (Fin 0) (Fin 2) GeometricField := 0
  let K := kernelBundle M U
  have hiK : GeometricallyIrreducible K := zero_bundle_irreducible KI U hU hiU 2
  let P := scalePolynomials n m
  let Y := geometricClosure (polynomialMap P '' K)
  have hyclosed : AlgebraicallyClosedSet Y := algebraicallyClosedSet_geometricClosure _
  have hyirred : GeometricallyIrreducible Y :=
    (geometricallyIrreducible_closure_iff _).mpr (hiK.polynomialMap_image P)
  have hscaled (z : PairPoint n m) (hz : z ∈ Z) (s : GeometricPoint 2) :
      pairPoint (s 0 • pairLeft z) (s 1 • pairRight z) ∈ polynomialMap P '' K := by
    refine ⟨pairPoint (E.forwardMap z) s, ?_, scalePolynomials_apply z s⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    ext i
    exact Fin.elim0 i
  have hZY : Z ⊆ Y := by
    intro z hz
    have h := subset_geometricClosure _ (hscaled z hz (fun _ => 1))
    simpa only [one_smul, pairPoint_projections] using h
  have hYX : Y ⊆ X := by
    apply geometricClosure_subset_closed _ hX
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, hz, he⟩ := hp.1
    have hpair : p = pairPoint (E.forwardMap z) (pairRight p) := by
      rw [he, pairPoint_projections]
    rw [hpair, scalePolynomials_apply]
    exact hbi z (hZ.subset hz) _ _
  have hYZ : Y = Z := hZ.maximal Y hyclosed hyirred hZY hYX
  intro z hz a b
  let s : GeometricPoint 2 := fun i => if i = 0 then a else b
  have h := subset_geometricClosure _ (hscaled z hz s)
  change pairPoint (s 0 • pairLeft z) (s 1 • pairRight z) ∈ Y at h
  rw [hYZ] at h
  simpa [s] using h

end HessianTheorem11.ReducedBiconeComponent
