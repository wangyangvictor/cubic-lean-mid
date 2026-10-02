import HessianTheorem11.IntrinsicRadical

/-! General textbook geometry for a kernel inside a kernel bundle, and
fiber dimensions of arbitrary polynomial maps. All coordinate spaces and
matrices are independent; no cubic or Hessian appears in an input. -/
noncomputable section
namespace HessianTheorem11
open Module MvPolynomial

/-- Kernel of a linear family of maps on the kernel of a matrix pencil. -/
def kernelAnnihilator {n a b c : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (N : GeometricPoint b →ₗ[GeometricField] Matrix (Fin c) (Fin b) GeometricField)
    (x : GeometricPoint n) : Submodule GeometricField (GeometricPoint b) :=
  LinearMap.ker (M x).mulVecLin ⊓
    ⨅ u : LinearMap.ker (M x).mulVecLin, LinearMap.ker (N u).mulVecLin

def kernelAnnihilatorBundle {n a b c : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (N : GeometricPoint b →ₗ[GeometricField] Matrix (Fin c) (Fin b) GeometricField)
    (O : Set (GeometricPoint n)) : Set (PairPoint n b) :=
  {p | pairLeft p ∈ O ∧ pairRight p ∈ kernelAnnihilator M N (pairLeft p)}

/-- A generic trivialization locus for two successive kernel constructions.
The dimensions refer to actual vector spaces and the actual bundle set. -/
structure KernelAnnihilatorOpen {n a b c : ℕ}
    (U : Set (GeometricPoint n))
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (N : GeometricPoint b →ₗ[GeometricField] Matrix (Fin c) (Fin b) GeometricField)
    (P : GeometricPolynomial n) where
  openSet : Set (GeometricPoint n)
  isOpen : RelativelyOpenSet U openSet
  subset : openSet ⊆ U
  dense : geometricClosure openSet = U
  nonempty : openSet.Nonempty
  avoids : ∀ x ∈ openSet, eval x P ≠ 0
  nullity : ℕ
  dimension_kernel : ∀ x ∈ openSet,
    finrank GeometricField (kernelAnnihilator M N x) = nullity
  maximal_rank : ∀ x ∈ openSet, ∀ y ∈ U, (M y).rank ≤ (M x).rank
  bundle_irreducible : GeometricallyIrreducible (kernelAnnihilatorBundle M N openSet)
  bundle_locally_closed : RelativelyOpenSet
    (geometricClosure (kernelAnnihilatorBundle M N openSet))
    (kernelAnnihilatorBundle M N openSet)
  bundle_dimension : ∀ t : ℕ, affineDimension U = (t : Dimension) →
    affineDimension (kernelAnnihilatorBundle M N openSet) = ((t + nullity : ℕ) : Dimension)

/-- Constant-rank matrices have locally free kernels. Apply this first to
M, then to the induced morphism from ker(M) to Hom(ker(M),K^c). Shrinking
the integral base to the two maximum-rank opens gives this general result. -/
structure KernelAnnihilatorGeometryInput : Prop where
  choose : ∀ {n a b c : ℕ} (U : Set (GeometricPoint n)),
    AlgebraicallyClosedSet U → GeometricallyIrreducible U →
    ∀ (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
      (N : GeometricPoint b →ₗ[GeometricField] Matrix (Fin c) (Fin b) GeometricField)
      (P : GeometricPolynomial n), (∃ x ∈ U, eval x P ≠ 0) →
      Nonempty (KernelAnnihilatorOpen U M N P)

/-- Usual dimension-of-fibers upper bound, valid for an irreducible locally
closed source and on any dense open of its image closure. -/
structure AffineFiberDimensionInput : Prop where
  dimension_le : ∀ {σ τ : Type} [Fintype σ] [Fintype τ]
    (P : τ → MvPolynomial σ GeometricField) (R : Set (σ → GeometricField)),
    GeometricallyIrreducible R → RelativelyOpenSet (geometricClosure R) R →
    ∀ O : Set (τ → GeometricField),
    RelativelyOpenSet (geometricClosure (polynomialMap P '' R)) O →
    geometricClosure O = geometricClosure (polynomialMap P '' R) →
    ∀ k : ℕ, (∀ y ∈ O,
      affineDimension {x | x ∈ R ∧ polynomialMap P x = y} ≤ (k : Dimension)) →
    affineDimension R ≤ affineDimension (geometricClosure (polynomialMap P '' R)) + k

/-- Elementary affine linear-space dimension and one nonzero equation,
plus invariance under adjoining fixed coordinates. -/
structure LinearSectionDimensionInput : Prop where
  subspace_hypersurface : ∀ {n : ℕ} (L : Submodule GeometricField (GeometricPoint n))
    (P : GeometricPolynomial n), (∃ x ∈ L, eval x P ≠ 0) →
    affineDimension {x | x ∈ L ∧ eval x P = 0} ≤
      ((finrank GeometricField L - 1 : ℕ) : Dimension)
  fixed_coordinates : ∀ {n m : ℕ} (Z : Set (GeometricPoint n)) (y : GeometricPoint m),
    affineDimension {p : PairPoint n m | pairLeft p ∈ Z ∧ pairRight p = y} = affineDimension Z

/-- A polynomial nonzero somewhere on a closure is nonzero somewhere on
the original set. This avoids adding a source-specific point-selection input. -/
theorem exists_on_dense_set_eval_ne_zero {n : ℕ}
    {O U : Set (GeometricPoint n)} (hdense : geometricClosure O = U)
    (P : GeometricPolynomial n) (hP : ∃ x ∈ U, eval x P ≠ 0) :
    ∃ x ∈ O, eval x P ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, hPx⟩ := hP
  apply hPx
  apply geometricClosure_subset_of_polynomial_vanishes O P h x
  rwa [hdense]

theorem kernelAnnihilator_hessian {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (x : GeometricPoint n) :
    kernelAnnihilator (hessianLinearMap F hF) (hessianLinearMap F hF) x =
      intrinsicRadical F x := rfl

theorem kernelAnnihilatorBundle_hessian {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (O : Set (GeometricPoint n)) :
    kernelAnnihilatorBundle (hessianLinearMap F hF) (hessianLinearMap F hF) O =
      radicalBundle F O := rfl

end HessianTheorem11
