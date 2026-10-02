import HessianTheorem11.UnconditionalSpecialLinearGraph
import HessianTheorem11.GenericRankBridge
import Mathlib.Algebra.MvPolynomial.Funext

/-! The actual special-linear matrix point locus is closed and irreducible.
For positive size, row normalization maps the reciprocal determinant graph
onto it by a polynomial map. The zero-size locus is the one-point affine
space. No algebraic-group or geometric input is used. -/
noncomputable section
namespace HessianTheorem11.UnconditionalSpecialLinear
open MvPolynomial Matrix

abbrev MatrixCoordinates (n : ℕ) := Fin n × Fin n

def pointMatrix {n : ℕ} (x : MatrixCoordinates n → GeometricField) :
    Matrix (Fin n) (Fin n) GeometricField := fun i j => x (i,j)

def determinantPolynomial (n : ℕ) : MvPolynomial (MatrixCoordinates n) GeometricField :=
  Matrix.det (fun i j : Fin n => (X (i,j) : MvPolynomial (MatrixCoordinates n) GeometricField))

@[simp] theorem eval_determinantPolynomial {n : ℕ} (x : MatrixCoordinates n → GeometricField) :
    eval x (determinantPolynomial n) = (pointMatrix x).det := by
  rw [determinantPolynomial,RingHom.map_det]
  congr 1
  ext i j
  simp [pointMatrix]

def specialLinearLocus (n : ℕ) : Set (MatrixCoordinates n → GeometricField) :=
  {x | (pointMatrix x).det = 1}

@[simp] theorem mem_specialLinearLocus {n : ℕ} (x : MatrixCoordinates n → GeometricField) :
    x ∈ specialLinearLocus n ↔ Matrix.det (fun i j : Fin n => x (i,j)) = 1 :=
  Iff.rfl

theorem identity_mem_specialLinearLocus (n : ℕ) :
    (fun ij : MatrixCoordinates n => (1 : Matrix (Fin n) (Fin n) GeometricField) ij.1 ij.2) ∈
      specialLinearLocus n := by
  change (1 : Matrix (Fin n) (Fin n) GeometricField).det = 1
  exact Matrix.det_one

theorem determinantPolynomial_ne_zero (n : ℕ) : determinantPolynomial n ≠ 0 := by
  intro h
  have he := congrArg (eval (fun ij : MatrixCoordinates n =>
    (1 : Matrix (Fin n) (Fin n) GeometricField) ij.1 ij.2)) h
  have hm : pointMatrix (fun ij : MatrixCoordinates n =>
      (1 : Matrix (Fin n) (Fin n) GeometricField) ij.1 ij.2) = 1 := rfl
  rw [eval_determinantPolynomial,hm,Matrix.det_one,map_zero] at he
  exact one_ne_zero he

theorem specialLinearLocus_closed (n : ℕ) :
    AlgebraicallyClosedSet (specialLinearLocus n) := by
  have he : specialLinearLocus n = zeroLocus GeometricField
      (Ideal.span {determinantPolynomial n - 1}) := by
    ext x
    simp [zeroLocus_span,sub_eq_zero]
    rfl
  rw [he]
  exact algebraicallyClosedSet_zeroLocus _

def normalizeRowTuple {n : ℕ} (k : Fin n) :
    MatrixCoordinates n → MvPolynomial (MatrixCoordinates n ⊕ Unit) GeometricField :=
  fun ij => (Matrix.updateRow
    (fun i j : Fin n => (X (Sum.inl (i,j)) : MvPolynomial (MatrixCoordinates n ⊕ Unit) GeometricField)) k
      (fun j => (X (Sum.inr ()) : MvPolynomial (MatrixCoordinates n ⊕ Unit) GeometricField) *
        X (Sum.inl (k,j)))) ij.1 ij.2

@[simp] theorem pointMatrix_normalizeRowTuple {n : ℕ} (k : Fin n)
    (y : (MatrixCoordinates n ⊕ Unit) → GeometricField) :
    pointMatrix (polynomialMap (normalizeRowTuple k) y) =
      (pointMatrix (y ∘ Sum.inl)).updateRow k
        (y (Sum.inr ()) • pointMatrix (y ∘ Sum.inl) k) := by
  ext i j
  simp only [pointMatrix,polynomialMap,normalizeRowTuple,Matrix.updateRow_apply]
  split_ifs <;> simp_all [pointMatrix]

/-- Every determinant-one matrix is the polynomial normalization of a
matrix together with its reciprocal determinant. -/
theorem normalizeRowTuple_image {n : ℕ} (k : Fin n) :
    polynomialMap (normalizeRowTuple k) '' reciprocalGraph (determinantPolynomial n) =
      specialLinearLocus n := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (pointMatrix (polynomialMap (normalizeRowTuple k) y)).det = 1
    rw [pointMatrix_normalizeRowTuple,Matrix.det_updateRow_smul,Matrix.updateRow_eq_self]
    change eval (y ∘ Sum.inl) (determinantPolynomial n) * y (Sum.inr ()) = 1 at hy
    rw [eval_determinantPolynomial] at hy
    rwa [mul_comm]
  · intro hx
    refine ⟨Sum.elim x (fun _ => 1), ?_, ?_⟩
    · change eval ((Sum.elim x (fun _ => 1)) ∘ Sum.inl) (determinantPolynomial n) * 1 = 1
      simpa only [Sum.elim_comp_inl,mul_one,eval_determinantPolynomial] using hx
    · ext ⟨i,j⟩
      by_cases h : i = k <;> simp_all [polynomialMap,normalizeRowTuple,Matrix.updateRow_apply]

/-- Actual SL matrix varieties, including SL_0, have prime reduced
vanishing ideals. The proof uses an actual surjective polynomial map from a
localization graph; it assumes no connectedness or group-variety theorem. -/
theorem specialLinearLocus_irreducible (n : ℕ) :
    GeometricallyIrreducible (specialLinearLocus n) := by
  cases n with
  | zero =>
    have he : specialLinearLocus 0 = Set.univ := by
      ext x
      simp [specialLinearLocus,Matrix.det_isEmpty]
    have hu : vanishingIdeal GeometricField
        (Set.univ : Set (MatrixCoordinates 0 → GeometricField)) = ⊥ := by
      ext p
      rw [Ideal.mem_bot]
      constructor
      · intro hp
        apply MvPolynomial.funext
        intro x
        simpa using hp x (Set.mem_univ x)
      · rintro rfl
        exact (vanishingIdeal GeometricField (Set.univ : Set (MatrixCoordinates 0 → GeometricField))).zero_mem
    unfold GeometricallyIrreducible
    rw [he,hu]
    exact Ideal.bot_prime
  | succ n =>
    rw [← normalizeRowTuple_image (0 : Fin (n+1))]
    exact (reciprocalGraph_irreducible (determinantPolynomial (n+1))
      (determinantPolynomial_ne_zero (n+1))).polynomialMap_image _

theorem specialLinearCoordinateRing_isDomain (n : ℕ) :
    IsDomain (affineCoordinateRing (vanishingIdeal GeometricField (specialLinearLocus n))) := by
  letI : (vanishingIdeal GeometricField (specialLinearLocus n)).IsPrime :=
    specialLinearLocus_irreducible n
  infer_instance

end HessianTheorem11.UnconditionalSpecialLinear
