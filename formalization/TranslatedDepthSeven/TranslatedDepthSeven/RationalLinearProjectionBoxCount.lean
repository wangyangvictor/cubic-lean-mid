import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Data.Finset.Card
import TranslatedDepthSeven.ExplicitLineContribution
import TranslatedDepthSeven.JacobianCertificatePolynomialHeight

/-!
# Integral box counts under a fixed rational linear projection

A rational linear projection is made integral by multiplying all its
coordinates by the single positive denominator `Matrix.den A`.  This file
records the elementary consequences needed after a finite geometric
projection has been chosen:

* the integral numerator map is exactly the rational map multiplied by that
  denominator;
* an integral box of radius `M` maps into an integral box of radius `C M`,
  where `C` depends only on the fixed matrix; and
* a uniform cardinality bound for the rational geometric fibres gives the
  corresponding literal `Finset` bound.

There is no dimension, degree, or determinant-method input here.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset

/-- Evaluation of a rational matrix on a rational column vector. -/
def rationalLinearProjection {n d : ℕ}
    (A : Matrix (Fin d) (Fin n) ℚ) (x : Fin n → ℚ) : Fin d → ℚ :=
  fun i ↦ ∑ j, A i j * x j

/-- The integral numerator map obtained by clearing the common denominator
of a rational projection matrix. -/
def integralNumeratorLinearProjection {n d : ℕ}
    (A : Matrix (Fin d) (Fin n) ℚ) (x : IntVector n) : IntVector d :=
  fun i ↦ ∑ j, A.num i j * x j

/-- Coordinatewise casting of an integral vector to a rational vector. -/
def intVectorToRat {n : ℕ} (x : IntVector n) : Fin n → ℚ :=
  fun j ↦ (x j : ℚ)

theorem intVectorToRat_injective {n : ℕ} :
    Function.Injective (@intVectorToRat n) := by
  intro x y h
  funext j
  have hj := congrFun h j
  change (x j : ℚ) = (y j : ℚ) at hj
  exact_mod_cast hj

/-- Clearing the matrix denominator commutes with evaluation on an integral
point. -/
theorem integralNumeratorLinearProjection_cast_eq_den_mul
    {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℚ)
    (x : IntVector n) (i : Fin d) :
    ((integralNumeratorLinearProjection A x i : ℤ) : ℚ) =
      (A.den : ℚ) * rationalLinearProjection A (intVectorToRat x) i := by
  simp only [integralNumeratorLinearProjection, rationalLinearProjection,
    intVectorToRat, Int.cast_sum, Int.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  have hden : (A.den : ℚ) ≠ 0 := by
    exact_mod_cast A.den_ne_zero
  have hnum : (A.num i j : ℚ) = (A.den : ℚ) * A i j := by
    have h := (div_eq_iff hden).mp (Matrix.num_div_den A i j)
    simpa [mul_comm] using h
  rw [hnum]
  ring

/-- The `ℓ¹` norm of one row of the cleared integral matrix. -/
def rationalLinearProjectionNumeratorRowMass {n d : ℕ}
    (A : Matrix (Fin d) (Fin n) ℚ) (i : Fin d) : ℕ :=
  ∑ j, (A.num i j).natAbs

/-- A fixed coefficient constant which bounds every cleared row. -/
def rationalLinearProjectionNumeratorConstant {n d : ℕ}
    (A : Matrix (Fin d) (Fin n) ℚ) : ℕ :=
  Finset.univ.sup (rationalLinearProjectionNumeratorRowMass A)

theorem rationalLinearProjectionNumeratorRowMass_le_constant
    {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℚ) (i : Fin d) :
    rationalLinearProjectionNumeratorRowMass A i ≤
      rationalLinearProjectionNumeratorConstant A := by
  exact Finset.le_sup (s := Finset.univ)
    (f := rationalLinearProjectionNumeratorRowMass A) (Finset.mem_univ i)

/-- The cleared integral projection of `[-M,M]^n` lies in
`[-C M,C M]^d`. -/
theorem integralNumeratorLinearProjection_coordinate_natAbs_le
    {n d M : ℕ} (A : Matrix (Fin d) (Fin n) ℚ)
    (x : IntVector n) (hx : ∀ j, (x j).natAbs ≤ M) (i : Fin d) :
    (integralNumeratorLinearProjection A x i).natAbs ≤
      rationalLinearProjectionNumeratorConstant A * M := by
  calc
    (integralNumeratorLinearProjection A x i).natAbs ≤
        ∑ j, (A.num i j * x j).natAbs := by
      exact int_natAbs_sum_le_sum_natAbs Finset.univ _
    _ = ∑ j, (A.num i j).natAbs * (x j).natAbs := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Int.natAbs_mul]
    _ ≤ ∑ j, (A.num i j).natAbs * M := by
      exact Finset.sum_le_sum fun j _hj ↦
        Nat.mul_le_mul_left (A.num i j).natAbs (hx j)
    _ = rationalLinearProjectionNumeratorRowMass A i * M := by
      simp [rationalLinearProjectionNumeratorRowMass,
        Finset.sum_mul]
    _ ≤ rationalLinearProjectionNumeratorConstant A * M :=
      Nat.mul_le_mul_right M
        (rationalLinearProjectionNumeratorRowMass_le_constant A i)

/-- The rational target represented by an integral numerator vector. -/
def rationalTargetOfIntegralNumerator {d : ℕ}
    (Aden : ℕ) (z : IntVector d) : Fin d → ℚ :=
  fun i ↦ (z i : ℚ) / (Aden : ℚ)

/-- Equality in one fibre of the cleared integral map implies equality in
the corresponding rational fibre. -/
theorem rationalLinearProjection_eq_target_of_integralNumerator_eq
    {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℚ)
    (x : IntVector n) (z : IntVector d)
    (hx : integralNumeratorLinearProjection A x = z) :
    rationalLinearProjection A (intVectorToRat x) =
      rationalTargetOfIntegralNumerator A.den z := by
  funext i
  have hclear := integralNumeratorLinearProjection_cast_eq_den_mul A x i
  rw [congrFun hx i] at hclear
  have hden : (A.den : ℚ) ≠ 0 := by
    exact_mod_cast A.den_ne_zero
  apply (eq_div_iff hden).2
  simpa [rationalTargetOfIntegralNumerator, mul_comm] using hclear.symm

/-- A finite set of integral points in one cleared fibre injects into the
corresponding rational geometric fibre.  Thus a geometric fibre-cardinality
bound transfers to the literal filtered `Finset`. -/
theorem integralNumeratorLinearProjection_fibre_card_le_geometric
    {n d D : ℕ} (A : Matrix (Fin d) (Fin n) ℚ)
    (points : Finset (IntVector n))
    (X : (Fin n → ℚ) → Prop)
    (hX : ∀ x ∈ points, X (intVectorToRat x))
    (hfinite : ∀ y : Fin d → ℚ,
      Set.Finite {x : Fin n → ℚ |
        X x ∧ rationalLinearProjection A x = y})
    (hfibre : ∀ y : Fin d → ℚ,
      Set.ncard {x : Fin n → ℚ |
        X x ∧ rationalLinearProjection A x = y} ≤ D)
    (z : IntVector d) :
    (points.filter fun x ↦
      integralNumeratorLinearProjection A x = z).card ≤ D := by
  classical
  let y := rationalTargetOfIntegralNumerator A.den z
  let fibre : Set (Fin n → ℚ) :=
    {x | X x ∧ rationalLinearProjection A x = y}
  have hfibreFinite : fibre.Finite := hfinite y
  have hmaps : Set.MapsTo intVectorToRat
      (↑(points.filter fun x ↦
        integralNumeratorLinearProjection A x = z) : Set (IntVector n))
      (↑hfibreFinite.toFinset : Set (Fin n → ℚ)) := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    simpa [fibre] using
      (show X (intVectorToRat x) ∧
          rationalLinearProjection A (intVectorToRat x) = y from
        ⟨hX x hx'.1,
          rationalLinearProjection_eq_target_of_integralNumerator_eq
            A x z hx'.2⟩)
  have hcard :
      (points.filter fun x ↦
        integralNumeratorLinearProjection A x = z).card ≤
        hfibreFinite.toFinset.card :=
    Finset.card_le_card_of_injOn intVectorToRat hmaps
      intVectorToRat_injective.injOn
  calc
    (points.filter fun x ↦
        integralNumeratorLinearProjection A x = z).card ≤
        hfibreFinite.toFinset.card := hcard
    _ = Set.ncard fibre := (Set.ncard_eq_toFinset_card fibre hfibreFinite).symm
    _ ≤ D := hfibre y

/-- **Fixed rational projection box count.**  If every rational geometric
fibre has at most `D` points, then any finite set of its integral points in
`[-M,M]^n` has size at most `D` times the number of lattice points in the
image box. -/
theorem card_le_integerBox_mul_of_rationalLinearProjection_fibres
    {n d M D : ℕ} (A : Matrix (Fin d) (Fin n) ℚ)
    (points : Finset (IntVector n))
    (X : (Fin n → ℚ) → Prop)
    (hbox : ∀ x ∈ points, ∀ j, (x j).natAbs ≤ M)
    (hX : ∀ x ∈ points, X (intVectorToRat x))
    (hfinite : ∀ y : Fin d → ℚ,
      Set.Finite {x : Fin n → ℚ |
        X x ∧ rationalLinearProjection A x = y})
    (hfibre : ∀ y : Fin d → ℚ,
      Set.ncard {x : Fin n → ℚ |
        X x ∧ rationalLinearProjection A x = y} ≤ D) :
    points.card ≤
      (2 * (rationalLinearProjectionNumeratorConstant A * M) + 1) ^ d * D := by
  apply finiteSet_card_le_fibre_mul_integerBox points
    (integralNumeratorLinearProjection A)
    (rationalLinearProjectionNumeratorConstant A * M) D
  · intro x hx i
    exact integralNumeratorLinearProjection_coordinate_natAbs_le
      A x (hbox x hx) i
  · intro z
    exact integralNumeratorLinearProjection_fibre_card_le_geometric
      A points X hX hfinite hfibre z

/-! ## A homogeneous projection on the standard affine chart -/

/-- The standard affine representative `[1:x]` of a rational point. -/
def rationalStandardAffineRepresentative {n : ℕ}
    (x : Fin n → ℚ) : Option (Fin n) → ℚ
  | none => 1
  | some j => x j

/-- The integral standard affine representative `[1:x]`. -/
def integralStandardAffineRepresentative {n : ℕ}
    (x : IntVector n) : Option (Fin n) → ℤ
  | none => 1
  | some j => x j

theorem integralStandardAffineRepresentative_cast
    {n : ℕ} (x : IntVector n) (j : Option (Fin n)) :
    ((integralStandardAffineRepresentative x j : ℤ) : ℚ) =
      rationalStandardAffineRepresentative (intVectorToRat x) j := by
  cases j <;> simp [integralStandardAffineRepresentative,
    rationalStandardAffineRepresentative, intVectorToRat]

/-- On the chart where the first target coordinate is the retained
homogenizing coordinate, these are the remaining rational target
coordinates. -/
def rationalProjectiveAffineTailProjection {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ)
    (x : Fin n → ℚ) : Fin d → ℚ :=
  fun i ↦ ∑ j, A i.succ j * rationalStandardAffineRepresentative x j

/-- Integral numerator coordinates for the preceding affine-chart map. -/
def integralNumeratorProjectiveAffineTailProjection {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ)
    (x : IntVector n) : IntVector d :=
  fun i ↦ ∑ j,
    A.num i.succ j * integralStandardAffineRepresentative x j

/-- The statement that the first row of a homogeneous projection matrix is
literally the distinguished coordinate `X_none`. -/
def FirstProjectionRowIsHomogenizingCoordinate {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ) : Prop :=
  A 0 none = 1 ∧ ∀ j, A 0 (some j) = 0

/-- Under the displayed first-row condition, the first homogeneous target
coordinate is one on the standard affine chart. -/
theorem rationalProjectiveAffine_firstCoordinate_eq_one
    {n d : ℕ} (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ)
    (hfirst : FirstProjectionRowIsHomogenizingCoordinate A)
    (x : Fin n → ℚ) :
    (∑ j, A 0 j * rationalStandardAffineRepresentative x j) = 1 := by
  rw [Fintype.sum_option]
  simp [rationalStandardAffineRepresentative, hfirst.1, hfirst.2]

/-- Clearing denominators commutes with restriction of a homogeneous
projection to the standard affine chart. -/
theorem integralNumeratorProjectiveAffineTailProjection_cast_eq_den_mul
    {n d : ℕ} (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ)
    (x : IntVector n) (i : Fin d) :
    ((integralNumeratorProjectiveAffineTailProjection A x i : ℤ) : ℚ) =
      (A.den : ℚ) *
        rationalProjectiveAffineTailProjection A (intVectorToRat x) i := by
  simp only [integralNumeratorProjectiveAffineTailProjection,
    rationalProjectiveAffineTailProjection, Int.cast_sum, Int.cast_mul,
    integralStandardAffineRepresentative_cast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  have hden : (A.den : ℚ) ≠ 0 := by
    exact_mod_cast A.den_ne_zero
  have hnum : (A.num i.succ j : ℚ) =
      (A.den : ℚ) * A i.succ j := by
    have h := (div_eq_iff hden).mp (Matrix.num_div_den A i.succ j)
    simpa [mul_comm] using h
  rw [hnum]
  ring

/-- The `ℓ¹` norm of one retained row of the cleared homogeneous
projection matrix. -/
def rationalProjectiveAffineTailNumeratorRowMass {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ) (i : Fin d) : ℕ :=
  ∑ j, (A.num i.succ j).natAbs

/-- A fixed coefficient constant for the affine-chart tail map. -/
def rationalProjectiveAffineTailNumeratorConstant {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ) : ℕ :=
  Finset.univ.sup (rationalProjectiveAffineTailNumeratorRowMass A)

theorem rationalProjectiveAffineTailNumeratorRowMass_le_constant
    {n d : ℕ} (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ)
    (i : Fin d) :
    rationalProjectiveAffineTailNumeratorRowMass A i ≤
      rationalProjectiveAffineTailNumeratorConstant A := by
  exact Finset.le_sup (s := Finset.univ)
    (f := rationalProjectiveAffineTailNumeratorRowMass A)
    (Finset.mem_univ i)

/-- The affine-chart tail of the cleared homogeneous projection sends a box
of radius `M` into a box of radius `C * max 1 M`; the maximum accounts for
the fixed homogenizing coordinate. -/
theorem integralNumeratorProjectiveAffineTailProjection_coordinate_natAbs_le
    {n d M : ℕ} (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ)
    (x : IntVector n) (hx : ∀ j, (x j).natAbs ≤ M) (i : Fin d) :
    (integralNumeratorProjectiveAffineTailProjection A x i).natAbs ≤
      rationalProjectiveAffineTailNumeratorConstant A * max 1 M := by
  have hrepresentative : ∀ j : Option (Fin n),
      (integralStandardAffineRepresentative x j).natAbs ≤ max 1 M := by
    intro j
    cases j with
    | none => simp [integralStandardAffineRepresentative]
    | some j =>
        exact (hx j).trans (Nat.le_max_right 1 M)
  calc
    (integralNumeratorProjectiveAffineTailProjection A x i).natAbs ≤
        ∑ j, (A.num i.succ j *
          integralStandardAffineRepresentative x j).natAbs := by
      exact int_natAbs_sum_le_sum_natAbs Finset.univ _
    _ = ∑ j, (A.num i.succ j).natAbs *
          (integralStandardAffineRepresentative x j).natAbs := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Int.natAbs_mul]
    _ ≤ ∑ j, (A.num i.succ j).natAbs * max 1 M := by
      exact Finset.sum_le_sum fun j _hj ↦
        Nat.mul_le_mul_left (A.num i.succ j).natAbs
          (hrepresentative j)
    _ = rationalProjectiveAffineTailNumeratorRowMass A i * max 1 M := by
      rw [rationalProjectiveAffineTailNumeratorRowMass, Finset.sum_mul]
    _ ≤ rationalProjectiveAffineTailNumeratorConstant A * max 1 M :=
      Nat.mul_le_mul_right (max 1 M)
        (rationalProjectiveAffineTailNumeratorRowMass_le_constant A i)

def rationalProjectiveAffineTailTargetOfIntegralNumerator {d : ℕ}
    (Aden : ℕ) (z : IntVector d) : Fin d → ℚ :=
  fun i ↦ (z i : ℚ) / (Aden : ℚ)

theorem rationalProjectiveAffineTailProjection_eq_target_of_integral_eq
    {n d : ℕ} (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ)
    (x : IntVector n) (z : IntVector d)
    (hx : integralNumeratorProjectiveAffineTailProjection A x = z) :
    rationalProjectiveAffineTailProjection A (intVectorToRat x) =
      rationalProjectiveAffineTailTargetOfIntegralNumerator A.den z := by
  funext i
  have hclear :=
    integralNumeratorProjectiveAffineTailProjection_cast_eq_den_mul A x i
  rw [congrFun hx i] at hclear
  have hden : (A.den : ℚ) ≠ 0 := by
    exact_mod_cast A.den_ne_zero
  apply (eq_div_iff hden).2
  simpa [rationalProjectiveAffineTailTargetOfIntegralNumerator,
    mul_comm] using hclear.symm

theorem integralNumeratorProjectiveAffineTail_fibre_card_le_geometric
    {n d D : ℕ} (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ)
    (points : Finset (IntVector n))
    (X : (Fin n → ℚ) → Prop)
    (hX : ∀ x ∈ points, X (intVectorToRat x))
    (hfinite : ∀ y : Fin d → ℚ,
      Set.Finite {x : Fin n → ℚ |
        X x ∧ rationalProjectiveAffineTailProjection A x = y})
    (hfibre : ∀ y : Fin d → ℚ,
      Set.ncard {x : Fin n → ℚ |
        X x ∧ rationalProjectiveAffineTailProjection A x = y} ≤ D)
    (z : IntVector d) :
    (points.filter fun x ↦
      integralNumeratorProjectiveAffineTailProjection A x = z).card ≤ D := by
  classical
  let y := rationalProjectiveAffineTailTargetOfIntegralNumerator A.den z
  let fibre : Set (Fin n → ℚ) :=
    {x | X x ∧ rationalProjectiveAffineTailProjection A x = y}
  have hfibreFinite : fibre.Finite := hfinite y
  have hmaps : Set.MapsTo intVectorToRat
      (↑(points.filter fun x ↦
        integralNumeratorProjectiveAffineTailProjection A x = z) :
        Set (IntVector n))
      (↑hfibreFinite.toFinset : Set (Fin n → ℚ)) := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    simpa [fibre] using
      (show X (intVectorToRat x) ∧
          rationalProjectiveAffineTailProjection A (intVectorToRat x) = y from
        ⟨hX x hx'.1,
          rationalProjectiveAffineTailProjection_eq_target_of_integral_eq
            A x z hx'.2⟩)
  have hcard :
      (points.filter fun x ↦
        integralNumeratorProjectiveAffineTailProjection A x = z).card ≤
        hfibreFinite.toFinset.card :=
    Finset.card_le_card_of_injOn intVectorToRat hmaps
      intVectorToRat_injective.injOn
  calc
    (points.filter fun x ↦
        integralNumeratorProjectiveAffineTailProjection A x = z).card ≤
        hfibreFinite.toFinset.card := hcard
    _ = Set.ncard fibre := (Set.ncard_eq_toFinset_card fibre hfibreFinite).symm
    _ ≤ D := hfibre y

/-- Homogeneous/projective affine-chart counterpart of
`card_le_integerBox_mul_of_rationalLinearProjection_fibres`.  When the first
target coordinate is `X_none`, the remaining `d` coordinates lie in a
`d`-dimensional box, so no spurious extra power is paid for projective
scaling. -/
theorem card_le_integerBox_mul_of_projectiveAffineTail_fibres
    {n d M D : ℕ} (A : Matrix (Fin (d + 1)) (Option (Fin n)) ℚ)
    (points : Finset (IntVector n))
    (X : (Fin n → ℚ) → Prop)
    (hbox : ∀ x ∈ points, ∀ j, (x j).natAbs ≤ M)
    (hX : ∀ x ∈ points, X (intVectorToRat x))
    (hfinite : ∀ y : Fin d → ℚ,
      Set.Finite {x : Fin n → ℚ |
        X x ∧ rationalProjectiveAffineTailProjection A x = y})
    (hfibre : ∀ y : Fin d → ℚ,
      Set.ncard {x : Fin n → ℚ |
        X x ∧ rationalProjectiveAffineTailProjection A x = y} ≤ D) :
    points.card ≤
      (2 * (rationalProjectiveAffineTailNumeratorConstant A * max 1 M) + 1) ^ d * D := by
  apply finiteSet_card_le_fibre_mul_integerBox points
    (integralNumeratorProjectiveAffineTailProjection A)
    (rationalProjectiveAffineTailNumeratorConstant A * max 1 M) D
  · intro x hx i
    exact integralNumeratorProjectiveAffineTailProjection_coordinate_natAbs_le
      A x (hbox x hx) i
  · intro z
    exact integralNumeratorProjectiveAffineTail_fibre_card_le_geometric
      A points X hX hfinite hfibre z

/-! The projective ideals elsewhere in this development use `Fin (n+1)`
rather than `Option (Fin n)` for homogeneous coordinates.  The following
thin wrappers make the preceding bridge directly applicable to those
matrices. -/

/-- Reindex homogeneous columns so that coordinate `0` becomes `none` and
coordinate `j.succ` becomes `some j`. -/
def finProjectiveMatrixAsOption {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin (d + 1)) (Option (Fin n)) ℚ :=
  A.submatrix id (finSuccEquiv n).symm

/-- First-row condition in the `Fin (n+1)` convention used for projective
ideals. -/
def FirstFinProjectionRowIsHomogenizingCoordinate {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ) : Prop :=
  A 0 0 = 1 ∧ ∀ j : Fin n, A 0 j.succ = 0

theorem firstProjectionRowIsHomogenizingCoordinate_finProjectiveMatrixAsOption
    {n d : ℕ} (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (hA : FirstFinProjectionRowIsHomogenizingCoordinate A) :
    FirstProjectionRowIsHomogenizingCoordinate
      (finProjectiveMatrixAsOption A) := by
  constructor
  · simpa [finProjectiveMatrixAsOption] using hA.1
  · intro j
    simpa [finProjectiveMatrixAsOption] using hA.2 j

def rationalFinProjectiveAffineTailProjection {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (x : Fin n → ℚ) : Fin d → ℚ :=
  rationalProjectiveAffineTailProjection (finProjectiveMatrixAsOption A) x

def integralNumeratorFinProjectiveAffineTailProjection {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (x : IntVector n) : IntVector d :=
  integralNumeratorProjectiveAffineTailProjection
    (finProjectiveMatrixAsOption A) x

def rationalFinProjectiveAffineTailNumeratorConstant {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ) : ℕ :=
  rationalProjectiveAffineTailNumeratorConstant
    (finProjectiveMatrixAsOption A)

theorem rationalFinProjectiveAffine_firstCoordinate_eq_one
    {n d : ℕ} (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (hA : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (x : Fin n → ℚ) :
    (∑ j, (finProjectiveMatrixAsOption A) 0 j *
      rationalStandardAffineRepresentative x j) = 1 :=
  rationalProjectiveAffine_firstCoordinate_eq_one
    (finProjectiveMatrixAsOption A)
    (firstProjectionRowIsHomogenizingCoordinate_finProjectiveMatrixAsOption
      A hA) x

/-- Direct `Fin (n+1)` form of the projective affine-chart box count. -/
theorem card_le_integerBox_mul_of_finProjectiveAffineTail_fibres
    {n d M D : ℕ} (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (points : Finset (IntVector n))
    (X : (Fin n → ℚ) → Prop)
    (hbox : ∀ x ∈ points, ∀ j, (x j).natAbs ≤ M)
    (hX : ∀ x ∈ points, X (intVectorToRat x))
    (hfinite : ∀ y : Fin d → ℚ,
      Set.Finite {x : Fin n → ℚ |
        X x ∧ rationalFinProjectiveAffineTailProjection A x = y})
    (hfibre : ∀ y : Fin d → ℚ,
      Set.ncard {x : Fin n → ℚ |
        X x ∧ rationalFinProjectiveAffineTailProjection A x = y} ≤ D) :
    points.card ≤
      (2 * (rationalFinProjectiveAffineTailNumeratorConstant A * max 1 M) + 1) ^ d * D := by
  exact card_le_integerBox_mul_of_projectiveAffineTail_fibres
    (finProjectiveMatrixAsOption A) points X hbox hX hfinite hfibre

end

end TranslatedDepthSeven
