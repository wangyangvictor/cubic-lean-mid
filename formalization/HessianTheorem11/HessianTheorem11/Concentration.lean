import HessianTheorem11.PolynomialCoordinateEquiv
import HessianTheorem11.ConcentrationLinearAlgebra
import HessianTheorem11.GradientIncidence
import HessianTheorem11.TextbookGeometry

/-!
Incidence concentration, with actual sets, embedded tangent spaces, and
polynomial maps. All external inputs below are general finite-type algebraic
geometry statements. None mentions cubics, Hessians, concentration, or any
numerical conclusion of Theorem 1.1.
-/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

abbrev PairPoint (n m : ℕ) := (Fin n ⊕ Fin m) → GeometricField

def pairLeft {n m : ℕ} (p : PairPoint n m) : GeometricPoint n := p ∘ Sum.inl

def pairRight {n m : ℕ} (p : PairPoint n m) : GeometricPoint m := p ∘ Sum.inr

def pairPoint {n m : ℕ} (x : GeometricPoint n) (y : GeometricPoint m) : PairPoint n m :=
  Sum.elim x y

@[simp] theorem pairLeft_pairPoint {n m : ℕ} (x : GeometricPoint n) (y : GeometricPoint m) :
    pairLeft (pairPoint x y) = x := rfl

@[simp] theorem pairRight_pairPoint {n m : ℕ} (x : GeometricPoint n) (y : GeometricPoint m) :
    pairRight (pairPoint x y) = y := rfl

@[simp] theorem pairPoint_projections {n m : ℕ} (p : PairPoint n m) :
    pairPoint (pairLeft p) (pairRight p) = p := by ext (i | i) <;> rfl

def pairLeftPolynomials (n m : ℕ) : Fin n → MvPolynomial (Fin n ⊕ Fin m) GeometricField :=
  fun i => X (Sum.inl i)

def pairRightPolynomials (n m : ℕ) : Fin m → MvPolynomial (Fin n ⊕ Fin m) GeometricField :=
  fun i => X (Sum.inr i)

@[simp] theorem polynomialMap_pairLeftPolynomials (n m : ℕ) :
    polynomialMap (pairLeftPolynomials n m) = pairLeft := by
  funext p i
  simp [polynomialMap, pairLeftPolynomials, pairLeft]

@[simp] theorem polynomialMap_pairRightPolynomials (n m : ℕ) :
    polynomialMap (pairRightPolynomials n m) = pairRight := by
  funext p i
  simp [polynomialMap, pairRightPolynomials, pairRight]

/-- An open subset in the induced Zariski topology, using a closed complement. -/
def RelativelyOpenSet {σ : Type*} (U O : Set (σ → GeometricField)) : Prop :=
  ∃ C : Set (σ → GeometricField), AlgebraicallyClosedSet C ∧ O = U \ C

/-- Maximality is with respect to actual closed irreducible subsets. -/
structure IsIrreducibleComponent {σ : Type*}
    (X Z : Set (σ → GeometricField)) : Prop where
  closed : AlgebraicallyClosedSet Z
  irreducible : GeometricallyIrreducible Z
  subset : Z ⊆ X
  maximal : ∀ W, AlgebraicallyClosedSet W → GeometricallyIrreducible W →
    Z ⊆ W → W ⊆ X → W = Z

def IsBicone {n m : ℕ} (X : Set (PairPoint n m)) : Prop :=
  ∀ p ∈ X, ∀ a b : GeometricField,
    pairPoint (a • pairLeft p) (b • pairRight p) ∈ X

/-- Finite irreducible decomposition, finiteness of affine dimension,
and strict dimension decrease for proper closed irreducible inclusions. -/
structure AffineComponentsInput : Prop where
  finite_dimension : ∀ {σ : Type} [Fintype σ] (Z : Set (σ → GeometricField)),
    Z.Nonempty → ∃ d : ℕ, affineDimension Z = (d : Dimension)
  maximal_dimension_component : ∀ {σ : Type} [Fintype σ]
    (X : Set (σ → GeometricField)), AlgebraicallyClosedSet X → X.Nonempty →
    ∃ Z, IsIrreducibleComponent X Z ∧ affineDimension Z = affineDimension X
  dimension_maximal : ∀ {σ : Type} [Fintype σ]
    (X Z : Set (σ → GeometricField)), AlgebraicallyClosedSet X →
    AlgebraicallyClosedSet Z → GeometricallyIrreducible Z → Z ⊆ X →
    affineDimension Z = affineDimension X → IsIrreducibleComponent X Z
  /-- A connected torus preserves each component; closure extends the action
  from nonzero scalars to all scalars. -/
  bicone_component : ∀ {n m : ℕ} (X Z : Set (PairPoint n m)),
    AlgebraicallyClosedSet X → IsBicone X → IsIrreducibleComponent X Z → IsBicone Z

/-- The actual differential of a polynomial map, component by component. -/
def polynomialMapDifferential {n m : ℕ} (P : Fin m → GeometricPolynomial n)
    (x : GeometricPoint n) : GeometricPoint n →ₗ[GeometricField] GeometricPoint m :=
  LinearMap.pi (fun i => polynomialDifferential (P i) x)

/-- The simultaneous smooth, generic differential rank, and maximum pencil
rank locus for an arbitrary polynomial map and arbitrary matrix pencil. -/
structure GenericRankOpen {n m a b : ℕ} (U : Set (GeometricPoint n))
    (P : Fin m → GeometricPolynomial n)
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField) where
  openSet : Set (GeometricPoint n)
  isOpen : RelativelyOpenSet U openSet
  subset : openSet ⊆ U
  dense : geometricClosure openSet = U
  nonempty : openSet.Nonempty
  baseDimension : ℕ
  imageDimension : ℕ
  nullity : ℕ
  dimension_base : affineDimension U = (baseDimension : Dimension)
  dimension_image : affineDimension (geometricClosure (polynomialMap P '' U)) =
    (imageDimension : Dimension)
  smooth : ∀ x ∈ openSet, finrank GeometricField (affineTangentSpace U x) = baseDimension
  differential_rank : ∀ x ∈ openSet,
    finrank GeometricField (LinearMap.range
      ((polynomialMapDifferential P x).domRestrict (affineTangentSpace U x))) = imageDimension
  kernel_dimension : ∀ x ∈ openSet,
    finrank GeometricField (LinearMap.ker (M x).mulVecLin) = nullity
  maximal_rank : ∀ x ∈ openSet, ∀ y ∈ U, (M y).rank ≤ (M x).rank

/-- Generic smoothness in characteristic zero, differential rank equal to
image dimension, and the open maximum-rank locus of a matrix. -/
structure GenericRankOpenInput : Prop where
  choose : ∀ {n m a b : ℕ} (U : Set (GeometricPoint n)),
    AlgebraicallyClosedSet U → GeometricallyIrreducible U →
    ∀ (P : Fin m → GeometricPolynomial n)
      (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField),
      Nonempty (GenericRankOpen U P M)

/-- A fiber product component dominating both copies of an irreducible base
has dimension at most twice the base dimension minus the image dimension. -/
structure DominantFiberProductInput : Prop where
  dimension_bound : ∀ {n m : ℕ} (P : Fin m → GeometricPolynomial n)
    (U : Set (GeometricPoint n)) (Y : Set (PairPoint n n)),
    AlgebraicallyClosedSet U → GeometricallyIrreducible U →
    AlgebraicallyClosedSet Y → GeometricallyIrreducible Y →
    geometricClosure (pairLeft '' Y) = U → geometricClosure (pairRight '' Y) = U →
    (∀ p ∈ Y, polynomialMap P (pairLeft p) = polynomialMap P (pairRight p)) →
    ∀ t s d : ℕ, affineDimension U = (t : Dimension) →
    affineDimension (geometricClosure (polynomialMap P '' U)) = (s : Dimension) →
    affineDimension Y = (d : Dimension) → d + s ≤ 2 * t

def kernelBundle {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (O : Set (GeometricPoint n)) : Set (PairPoint n b) :=
  {p | pairLeft p ∈ O ∧ (M (pairLeft p)).mulVec (pairRight p) = 0}

/-- Constant-rank kernels form a vector bundle. This is the general matrix
minor-chart theorem, with independently sized source, rows, and columns. -/
structure KernelBundleInput : Prop where
  closure_irreducible : ∀ {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (U O : Set (GeometricPoint n)), AlgebraicallyClosedSet U →
    GeometricallyIrreducible U → RelativelyOpenSet U O → geometricClosure O = U →
    ∀ ell : ℕ, (∀ x ∈ O, finrank GeometricField (LinearMap.ker (M x).mulVecLin) = ell) →
    GeometricallyIrreducible (geometricClosure (kernelBundle M O))
  dimension : ∀ {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (U O : Set (GeometricPoint n)), AlgebraicallyClosedSet U →
    GeometricallyIrreducible U → RelativelyOpenSet U O → geometricClosure O = U →
    ∀ t ell : ℕ, affineDimension U = (t : Dimension) →
    (∀ x ∈ O, finrank GeometricField (LinearMap.ker (M x).mulVecLin) = ell) →
    affineDimension (kernelBundle M O) = ((t + ell : ℕ) : Dimension)

/-- Restricting a dominant map on an irreducible variety to a dense open
subset of its image closure preserves dimension. -/
structure DominantOpenInput : Prop where
  dimension_preimage : ∀ {σ : Type} [Fintype σ] {n : ℕ}
    (P : Fin n → MvPolynomial σ GeometricField) (Z : Set (σ → GeometricField))
    (U O : Set (GeometricPoint n)),
    AlgebraicallyClosedSet Z → GeometricallyIrreducible Z →
    geometricClosure (polynomialMap P '' Z) = U →
    RelativelyOpenSet U O → geometricClosure O = U →
    affineDimension {z ∈ Z | polynomialMap P z ∈ O} = affineDimension Z

structure ConcentrationGeometryInput : Prop extends AffineComponentsInput,
    GenericRankOpenInput, DominantFiberProductInput, KernelBundleInput, DominantOpenInput

/-- The first projection of a bicone, followed by affine closure, is a cone.
The only closure fact used is polynomial continuity of scalar multiplication. -/
theorem projection_closure_isAffineCone {n m : ℕ} (Z : Set (PairPoint n m))
    (hz : IsBicone Z) : IsAffineCone (geometricClosure (pairLeft '' Z)) := by
  intro a x hx
  let P : Fin n → GeometricPolynomial n := fun i => C a * X i
  have hmap : polynomialMap P = fun x : GeometricPoint n => a • x := by
    funext x i
    simp [polynomialMap, P]
  have hinc : polynomialMap P '' (pairLeft '' Z) ⊆ pairLeft '' Z := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [hmap]
    exact ⟨pairPoint (a • pairLeft p) (1 • pairRight p), hz p hp a 1, rfl⟩
  have hc := polynomialMap_image_closure_subset P (pairLeft '' Z)
  have hm := geometricClosure_mono hinc
  apply hm
  apply hc
  exact ⟨x, hx, congrFun hmap x⟩

/-- The actual cubic incidence equations, with the same sum coordinates used
in `incidenceLocus`. -/
def cubicIncidence {n : ℕ} (F : GeometricPolynomial n) : Set (PairPoint n n) :=
  {p | (hessian F (pairLeft p)).mulVec (pairRight p) = 0}

@[simp] theorem cubicIncidence_geometricPolynomial {n : ℕ} (F : RationalPolynomial n) :
    cubicIncidence (geometricPolynomial F) = incidenceLocus F := rfl

def incidenceEquation {n : ℕ} (F : GeometricPolynomial n) (i : Fin n) :
    MvPolynomial (Fin n ⊕ Fin n) GeometricField :=
  ∑ j, rename Sum.inl (hessianPolynomial F i j) * X (Sum.inr j)

@[simp] theorem eval_incidenceEquation {n : ℕ} (F : GeometricPolynomial n)
    (p : PairPoint n n) (i : Fin n) :
    eval p (incidenceEquation F i) = ((hessian F (pairLeft p)).mulVec (pairRight p)) i := by
  simp [incidenceEquation, hessian, Matrix.mulVec, dotProduct, pairLeft, pairRight,
    eval_rename]

 theorem cubicIncidence_closed {n : ℕ} (F : GeometricPolynomial n) :
    AlgebraicallyClosedSet (cubicIncidence F) := by
  apply Set.Subset.antisymm
  · intro p hp
    ext i
    rw [← eval_incidenceEquation]
    apply hp (incidenceEquation F i)
    intro q hq
    change eval q (incidenceEquation F i) = 0
    rw [eval_incidenceEquation]
    exact congrFun hq i
  · exact subset_geometricClosure _

theorem cubicIncidence_nonempty {n : ℕ} (F : GeometricPolynomial n) :
    (cubicIncidence F).Nonempty := by
  refine ⟨pairPoint 0 0, ?_⟩
  change (hessian F 0).mulVec 0 = 0
  simp

theorem cubicIncidence_bicone {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) : IsBicone (cubicIncidence F) := by
  intro p hp a b
  change (hessian F (a • pairLeft p)).mulVec (b • pairRight p) = 0
  rw [hessian_smul hF, Matrix.smul_mulVec, Matrix.mulVec_smul]
  change a • b • (hessian F (pairLeft p)).mulVec (pairRight p) = 0
  rw [hp, smul_zero, smul_zero]

/-- The set and dimension conclusions of source Proposition 5.5. -/
structure IncidenceConcentration {n : ℕ} (F : GeometricPolynomial n) where
  base : Set (GeometricPoint n)
  closed : AlgebraicallyClosedSet base
  irreducible : GeometricallyIrreducible base
  cone : IsAffineCone base
  contained : ∀ x ∈ base, eval x F = 0
  baseDimension : ℕ
  rank : ℕ
  nullity : ℕ
  dimension_base : affineDimension base = (baseDimension : Dimension)
  dimension_incidence : affineDimension (cubicIncidence F) =
    ((baseDimension + nullity : ℕ) : Dimension)
  rank_nullity : rank + nullity = n
  rank_attained : ∃ x ∈ base, (hessian F x).rank = rank
  maximal_rank : ∀ x ∈ base, (hessian F x).rank ≤ rank

@[simp] theorem polynomialMap_gradient {n : ℕ} (F : GeometricPolynomial n) :
    polynomialMap (fun i => pderiv i F) = gradient F := rfl

@[simp] theorem polynomialMapDifferential_gradient {n : ℕ}
    (F : GeometricPolynomial n) (x : GeometricPoint n) :
    polynomialMapDifferential (fun i => pderiv i F) x = (hessian F x).mulVecLin := by
  ext v i
  simp [polynomialMapDifferential, polynomialDifferential_apply, hessian, hessianPolynomial,
    Matrix.mulVec, dotProduct]

theorem kernelBundle_subset_cubicIncidence {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (O : Set (GeometricPoint n)) :
    kernelBundle (hessianLinearMap F hF) O ⊆ cubicIncidence F := fun _ h => h.2

/-- Dimension equality for the full kernel family over the first projection
of any maximum-dimensional closed irreducible incidence subset. The proof uses
both actual set inclusions; no incidence-specific dimension formula is an input. -/
theorem maximal_incidence_projection_dimension
    (AG : ConcentrationGeometryInput) {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (W : Set (PairPoint n n))
    (hWclosed : AlgebraicallyClosedSet W) (hWirred : GeometricallyIrreducible W)
    (hWI : W ⊆ cubicIncidence F)
    (hWdim : affineDimension W = affineDimension (cubicIncidence F))
    (G : GenericRankOpen (geometricClosure (pairLeft '' W))
      (fun i => pderiv i F) (hessianLinearMap F hF)) :
    affineDimension (cubicIncidence F) =
      ((G.baseDimension + G.nullity : ℕ) : Dimension) := by
  let U := geometricClosure (pairLeft '' W)
  have hUclosed : AlgebraicallyClosedSet U := algebraicallyClosedSet_geometricClosure _
  have hUirred : GeometricallyIrreducible U := by
    apply (geometricallyIrreducible_closure_iff _).mpr
    simpa using hWirred.polynomialMap_image (pairLeftPolynomials n n)
  have hbdim := AG.dimension (hessianLinearMap F hF) U G.openSet
    hUclosed hUirred G.isOpen G.dense G.baseDimension G.nullity
    G.dimension_base G.kernel_dimension
  have hupper : ((G.baseDimension + G.nullity : ℕ) : Dimension) ≤
      affineDimension (cubicIncidence F) := by
    rw [← hbdim]
    exact affineDimension_mono (kernelBundle_subset_cubicIncidence F hF _)
  have hcutdim : affineDimension {p ∈ W | pairLeft p ∈ G.openSet} = affineDimension W := by
    simpa using AG.dimension_preimage (pairLeftPolynomials n n) W U G.openSet
      hWclosed hWirred (by simp [U]) G.isOpen G.dense
  have hcut : {p ∈ W | pairLeft p ∈ G.openSet} ⊆
      kernelBundle (hessianLinearMap F hF) G.openSet := by
    intro p hp
    exact ⟨hp.2, hWI hp.1⟩
  have hlower := affineDimension_mono hcut
  rw [hcutdim, hWdim, hbdim] at hlower
  exact le_antisymm hlower hupper

/-- The source's invertible change `(x,y) ↦ (x+y,x−y)`, now on the actual
sum-coordinate affine space used in `incidenceLocus`. -/
def incidenceSumCoordinateChange (n : ℕ) :
    PairPoint n n ≃ₗ[GeometricField] PairPoint n n where
  toFun p := pairPoint (pairLeft p + pairRight p) (pairLeft p - pairRight p)
  invFun p := pairPoint ((2 : GeometricField)⁻¹ • (pairLeft p + pairRight p))
    ((2 : GeometricField)⁻¹ • (pairLeft p - pairRight p))
  left_inv p := by
    ext (i | i) <;>
      simp [pairPoint, pairLeft, pairRight, Pi.add_apply] <;> field_simp <;> ring
  right_inv p := by
    ext (i | i) <;>
      simp [pairPoint, pairLeft, pairRight, Pi.add_apply] <;> field_simp <;> ring
  map_add' p q := by
    ext (i | i) <;> simp [pairPoint, pairLeft, pairRight] <;> ring
  map_smul' a p := by
    ext (i | i) <;> simp [pairPoint, pairLeft, pairRight, mul_add, mul_sub]

@[simp] theorem incidenceSumCoordinateChange_left {n : ℕ} (p : PairPoint n n) :
    pairLeft (incidenceSumCoordinateChange n p) = pairLeft p + pairRight p := rfl

@[simp] theorem incidenceSumCoordinateChange_right {n : ℕ} (p : PairPoint n n) :
    pairRight (incidenceSumCoordinateChange n p) = pairLeft p - pairRight p := rfl

def pairSwapEquiv (n : ℕ) : PairPoint n n ≃ₗ[GeometricField] PairPoint n n where
  toFun p := pairPoint (pairRight p) (pairLeft p)
  invFun p := pairPoint (pairRight p) (pairLeft p)
  left_inv p := pairPoint_projections p
  right_inv p := pairPoint_projections p
  map_add' p q := by ext (i | i) <;> rfl
  map_smul' a p := by ext (i | i) <;> rfl

@[simp] theorem pairLeft_pairSwapEquiv {n : ℕ} (p : PairPoint n n) :
    pairLeft (pairSwapEquiv n p) = pairRight p := rfl

@[simp] theorem pairRight_pairSwapEquiv {n : ℕ} (p : PairPoint n n) :
    pairRight (pairSwapEquiv n p) = pairLeft p := rfl

theorem incidenceSumCoordinateChange_equal_gradients {n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (PairPoint n n)) (hz : Z ⊆ cubicIncidence F) :
    ∀ p ∈ incidenceSumCoordinateChange n '' Z,
      gradient F (pairLeft p) = gradient F (pairRight p) := by
  rintro _ ⟨q, hq, rfl⟩
  exact (incidence_iff_equal_gradients hF _ _).mp (hz hq)

/-- Componentwise independent scaling gives equal projections after the
coordinate change. Whole-incidence symmetry alone would not justify this. -/
theorem incidenceSumCoordinateChange_equal_projections {n : ℕ}
    (Z : Set (PairPoint n n)) (hz : IsBicone Z) :
    pairRight '' (incidenceSumCoordinateChange n '' Z) =
      pairLeft '' (incidenceSumCoordinateChange n '' Z) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨_, ⟨pairPoint (pairLeft p) (-pairRight p), ?_, rfl⟩, ?_⟩
    · simpa using hz p hp 1 (-1)
    · simp [sub_eq_add_neg]
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨_, ⟨pairPoint (pairLeft p) (-pairRight p), ?_, rfl⟩, ?_⟩
    · simpa using hz p hp 1 (-1)
    · simp

theorem pairSwapEquiv_incidence {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) :
    pairSwapEquiv n '' cubicIncidence F ⊆ cubicIncidence F := by
  rintro _ ⟨p, hp, rfl⟩
  change (hessian F (pairRight p)).mulVec (pairLeft p) = 0
  rw [hessian_polarization hF]
  exact hp

/-- Equality throughout the fiber-product/kernel-bundle dimension squeeze.
Its geometric hypotheses concern the actual transformed incidence component. -/
theorem gradient_fiber_product_kernel_vanishing
    (AG : ConcentrationGeometryInput) (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Y : Set (PairPoint n n)) (hYclosed : AlgebraicallyClosedSet Y)
    (hYirred : GeometricallyIrreducible Y)
    (hYdim : affineDimension Y = affineDimension (cubicIncidence F))
    (hequal : geometricClosure (pairRight '' Y) = geometricClosure (pairLeft '' Y))
    (hrelation : ∀ p ∈ Y, gradient F (pairLeft p) = gradient F (pairRight p))
    (G : GenericRankOpen (geometricClosure (pairLeft '' Y))
      (fun i => pderiv i F) (hessianLinearMap F hF)) :
    affineDimension (kernelBundle (hessianLinearMap F hF) G.openSet) =
      affineDimension (cubicIncidence F) ∧
    ∀ x ∈ G.openSet, ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, eval v F = 0 := by
  let U := geometricClosure (pairLeft '' Y)
  have hUc : AlgebraicallyClosedSet U := algebraicallyClosedSet_geometricClosure _
  have hUi : GeometricallyIrreducible U := by
    apply (geometricallyIrreducible_closure_iff _).mpr
    simpa using hYirred.polynomialMap_image (pairLeftPolynomials n n)
  obtain ⟨d, hd⟩ := AG.finite_dimension (cubicIncidence F) (cubicIncidence_nonempty F)
  have hfiber : d + G.imageDimension ≤ 2 * G.baseDimension :=
    AG.dimension_bound (fun i => pderiv i F) U Y hUc hUi hYclosed hYirred rfl hequal
      hrelation G.baseDimension G.imageDimension d G.dimension_base G.dimension_image
      (hYdim.trans hd)
  have hbdim := AG.dimension (hessianLinearMap F hF) U G.openSet hUc hUi
    G.isOpen G.dense G.baseDimension G.nullity G.dimension_base G.kernel_dimension
  have hbundle : G.baseDimension + G.nullity ≤ d := by
    have hb := affineDimension_mono (kernelBundle_subset_cubicIncidence F hF G.openSet)
    rw [hbdim, hd] at hb
    exact_mod_cast hb
  have hrestriction : G.baseDimension ≤ G.imageDimension + G.nullity := by
    obtain ⟨x, hx⟩ := G.nonempty
    have h := kernel_finrank_lower_of_restricted_rank (hessian F x).mulVecLin
      (affineTangentSpace U x) (h := G.imageDimension) (by
        have hg := G.differential_rank x hx
        rw [polynomialMapDifferential_gradient F x] at hg
        exact hg.le)
    rw [G.smooth x hx] at h
    have hk : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = G.nullity :=
      G.kernel_dimension x hx
    rwa [hk] at h
  have hbalance : G.baseDimension = G.imageDimension + G.nullity := by omega
  have hdimension : d = G.baseDimension + G.nullity := by omega
  constructor
  · rw [hbdim, hd, hdimension]
  · intro x hx
    have hKT : LinearMap.ker (hessian F x).mulVecLin ≤ affineTangentSpace U x := by
      apply ker_le_of_restriction_nullity_equality
      rw [G.smooth x hx]
      have hr : finrank GeometricField (LinearMap.range
          ((hessian F x).mulVecLin.domRestrict (affineTangentSpace U x))) = G.imageDimension := by
        have hg := G.differential_rank x hx
        rw [polynomialMapDifferential_gradient F x] at hg
        exact hg
      rw [hr, show finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) =
        G.nullity from G.kernel_dimension x hx]
      exact hbalance
    apply cubic_vanishes_on_kernel_of_tangent_containment F hF x (affineTangentSpace U x) hKT
    intro t ht u hu v hv
    have hp := DT.tangent_kernel_pairing (hessianLinearMap F hF) (hessian_symmetric F)
      U x (G.subset hx) (G.maximal_rank x hx) t ht u hu v hv
    rw [polarization_swap_first, polarization_swap_last hF]
    exact hp

/-- Source Proposition 5.5, obtained from individually general AG inputs.
A largest incidence family can be concentrated over an actual closed
irreducible cone contained in the cubic. -/
theorem incidence_concentration
    (AG : ConcentrationGeometryInput) (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) :
    Nonempty (IncidenceConcentration F) := by
  let I := cubicIncidence F
  have hIc : AlgebraicallyClosedSet I := cubicIncidence_closed F
  obtain ⟨Z, hZ, hZdim⟩ := AG.maximal_dimension_component I hIc (cubicIncidence_nonempty F)
  have hZb : IsBicone Z := AG.bicone_component I Z hIc (cubicIncidence_bicone F hF) hZ
  let E := PolynomialCoordinateEquiv.ofLinearEquiv (incidenceSumCoordinateChange n)
  let Y := incidenceSumCoordinateChange n '' Z
  have hYc : AlgebraicallyClosedSet Y := by
    simpa [E, Y] using (E.algebraicallyClosedSet_image_iff Z).mpr hZ.closed
  have hYi : GeometricallyIrreducible Y := by
    simpa [E, Y] using (E.geometricallyIrreducible_image_iff Z).mpr hZ.irreducible
  have hYdim : affineDimension Y = affineDimension I := by
    calc
      affineDimension Y = affineDimension Z := by simpa [E, Y] using E.affineDimension_image Z
      _ = affineDimension I := hZdim
  let U := geometricClosure (pairLeft '' Y)
  have hUc : AlgebraicallyClosedSet U := algebraicallyClosedSet_geometricClosure _
  have hUi : GeometricallyIrreducible U := by
    apply (geometricallyIrreducible_closure_iff _).mpr
    simpa using hYi.polynomialMap_image (pairLeftPolynomials n n)
  let M := hessianLinearMap F hF
  let G := Classical.choice (AG.choose U hUc hUi (fun i => pderiv i F) M)
  have hequal : geometricClosure (pairRight '' Y) = U := by
    unfold U Y
    rw [incidenceSumCoordinateChange_equal_projections Z hZb]
  have hrelation : ∀ p ∈ Y, gradient F (pairLeft p) = gradient F (pairRight p) :=
    incidenceSumCoordinateChange_equal_gradients F hF Z hZ.subset
  obtain ⟨hBdim, hBzero⟩ := gradient_fiber_product_kernel_vanishing AG DT F hF Y
    hYc hYi hYdim hequal hrelation G
  let B := kernelBundle M G.openSet
  let K := geometricClosure B
  have hKc : AlgebraicallyClosedSet K := algebraicallyClosedSet_geometricClosure _
  have hKi : GeometricallyIrreducible K :=
    AG.closure_irreducible M U G.openSet hUc hUi G.isOpen G.dense
      G.nullity G.kernel_dimension
  have hKI : K ⊆ I := geometricClosure_subset_closed
    (kernelBundle_subset_cubicIncidence F hF G.openSet) hIc
  have hKdim : affineDimension K = affineDimension I := by
    rw [affineDimension_closure]
    exact hBdim
  have hKzero : ∀ p ∈ K, eval (pairRight p) F = 0 := by
    have hb : ∀ p ∈ B, eval p (aeval (pairRightPolynomials n n) F) = 0 := by
      intro p hp
      rw [← eval_polynomialMap]
      simp only [polynomialMap_pairRightPolynomials]
      exact hBzero (pairLeft p) hp.1 (pairRight p) hp.2
    have hc := geometricClosure_subset_of_polynomial_vanishes B
      (aeval (pairRightPolynomials n n) F) hb
    intro p hp
    have h := hc p hp
    rw [← eval_polynomialMap] at h
    simpa using h
  let S := PolynomialCoordinateEquiv.ofLinearEquiv (pairSwapEquiv n)
  let W := pairSwapEquiv n '' K
  have hWc : AlgebraicallyClosedSet W := by
    simpa [S, W] using (S.algebraicallyClosedSet_image_iff K).mpr hKc
  have hWi : GeometricallyIrreducible W := by
    simpa [S, W] using (S.geometricallyIrreducible_image_iff K).mpr hKi
  have hWI : W ⊆ I := by
    intro p hp
    exact pairSwapEquiv_incidence F hF (Set.image_mono hKI hp)
  have hWdim : affineDimension W = affineDimension I := by
    calc
      affineDimension W = affineDimension K := by simpa [S, W] using S.affineDimension_image K
      _ = affineDimension I := hKdim
  have hWcomponent := AG.dimension_maximal I W hIc hWc hWi hWI hWdim
  have hWb := AG.bicone_component I W hIc (cubicIncidence_bicone F hF) hWcomponent
  let V := geometricClosure (pairLeft '' W)
  have hVc : AlgebraicallyClosedSet V := algebraicallyClosedSet_geometricClosure _
  have hVi : GeometricallyIrreducible V := by
    apply (geometricallyIrreducible_closure_iff _).mpr
    simpa using hWi.polynomialMap_image (pairLeftPolynomials n n)
  have hVzero : ∀ x ∈ V, eval x F = 0 := by
    apply geometricClosure_subset_of_polynomial_vanishes (pairLeft '' W) F
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact hKzero p hp
  let Gv := Classical.choice (AG.choose V hVc hVi (fun i => pderiv i F) M)
  obtain ⟨x, hx⟩ := Gv.nonempty
  have hIdim := maximal_incidence_projection_dimension AG F hF W hWc hWi hWI hWdim Gv
  refine ⟨{
    base := V
    closed := hVc
    irreducible := hVi
    cone := projection_closure_isAffineCone W hWb
    contained := hVzero
    baseDimension := Gv.baseDimension
    rank := (hessian F x).rank
    nullity := Gv.nullity
    dimension_base := Gv.dimension_base
    dimension_incidence := hIdim
    rank_nullity := ?_
    rank_attained := ⟨x, Gv.subset hx, rfl⟩
    maximal_rank := Gv.maximal_rank x hx
  }⟩
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hk : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = Gv.nullity :=
    Gv.kernel_dimension x hx
  change (hessian F x).rank + _ = _ at hr
  simpa [hk] using hr

end HessianTheorem11
