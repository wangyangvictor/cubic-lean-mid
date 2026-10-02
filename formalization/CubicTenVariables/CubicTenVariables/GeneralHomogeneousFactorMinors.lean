import CubicTenVariables.CubicFactorCharts
import CubicTenVariables.MatrixAugmentedColumn
import CubicTenVariables.HomogeneousOriginOpen
import CubicTenVariables.IrreducibleFromTopHomogeneousPart

/-!
# Explicit principal opens for irreducibility in every fixed degree

For every possible factor degree `e`, multiplication by the potential
factor is represented by a literal finite matrix.  Maximal minors of the
matrix with the equation adjoined cut out precisely the projective locus of
degree-`e` factors.  The already proved homogeneous-origin certificate then
spreads the absence of such factors from one algebraically closed fibre.

This is the elementary fixed-degree replacement for the general
geometric-integrality-open input used elsewhere in the project.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.GeneralHomogeneousFactorMinors

open MvPolynomial CubicFactorCharts MatrixAugmentedColumn
open IrreducibleFromTopHomogeneousPart

variable {R : Type*} [CommRing R] {n d e : ℕ}

/-- Multiplication by the potential degree-`e` factor, in bounded
coefficient coordinates. -/
def multiplicationMatrix (d e : ℕ) (a : Monomial n e → R) :
    Matrix (Monomial n d) (Monomial n (d - e)) R :=
  fun row col ↦ coeff row.val (polynomial a * monomial col.val 1)

theorem multiplicationMatrix_mulVec (he : e ≤ d)
    (a : Monomial n e → R) (c : Monomial n (d - e) → R) :
    (multiplicationMatrix d e a).mulVec c =
      fun row : Monomial n d ↦ coeff row.val (polynomial a * polynomial c) := by
  ext row
  simp only [Matrix.mulVec, dotProduct, multiplicationMatrix, polynomial,
    Finset.mul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro col _
  have hm : monomial col.val (c col) =
      C (c col) * monomial col.val (1 : R) := by
    rw [C_mul_monomial, mul_one]
  rw [hm, mul_left_comm, coeff_C_mul]
  ring

theorem polynomial_multiplicationMatrix_mulVec (he : e ≤ d)
    (a : Monomial n e → R) (c : Monomial n (d - e) → R) :
    polynomial ((multiplicationMatrix d e a).mulVec c) =
      polynomial a * polynomial c := by
  rw [multiplicationMatrix_mulVec he]
  apply polynomial_coefficients
  have ha := polynomial_totalDegree_le a
  have hc := polynomial_totalDegree_le c
  have hsum := (totalDegree_mul (polynomial a) (polynomial c)).trans
    (add_le_add ha hc)
  omega

theorem multiplicationMatrix_injective [IsDomain R] (he : e ≤ d)
    (a : Monomial n e → R) (ha : a ≠ 0) :
    Function.Injective (multiplicationMatrix d e a).mulVec := by
  have hpa : polynomial a ≠ 0 := by
    intro h
    apply ha
    ext m
    simpa only [coeff_polynomial, coeff_zero] using congrArg (coeff m.val) h
  intro c c' h
  have hp := congrArg polynomial h
  rw [polynomial_multiplicationMatrix_mulVec he,
    polynomial_multiplicationMatrix_mulVec he] at hp
  have hc := mul_left_cancel₀ hpa hp
  ext m
  simpa only [coeff_polynomial] using congrArg (coeff m.val) hc

theorem multiplicationMatrix_rank {K : Type*} [Field K] (he : e ≤ d)
    (a : Monomial n e → K) (ha : a ≠ 0) :
    (multiplicationMatrix d e a).rank = Fintype.card (Monomial n (d - e)) := by
  have hi : Function.Injective (Matrix.mulVecLin (multiplicationMatrix d e a)) :=
    multiplicationMatrix_injective he a ha
  change Module.finrank K
      (LinearMap.range (Matrix.mulVecLin (multiplicationMatrix d e a))) = _
  rw [LinearMap.finrank_range_of_inj hi, Module.finrank_pi]

/-- The universal multiplication matrix is linear in the coefficients of
the potential factor. -/
def universalMatrix (n d e : ℕ) (R : Type*) [CommRing R] :
    Matrix (Monomial n d) (Monomial n (d - e))
      (MvPolynomial (Monomial n e) R) :=
  fun row col ↦ ∑ i,
    C (coeff row.val
      (monomial i.val (1 : R) * monomial col.val (1 : R))) * X i

theorem universalMatrix_homogeneous (row : Monomial n d)
    (col : Monomial n (d - e)) :
    (universalMatrix n d e R row col).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

theorem eval_universalMatrix (a : Monomial n e → R)
    (row : Monomial n d) (col : Monomial n (d - e)) :
    eval a (universalMatrix n d e R row col) = multiplicationMatrix d e a row col := by
  simp only [universalMatrix, map_sum, map_mul, eval_C, eval_X,
    multiplicationMatrix, polynomial, Finset.sum_mul, coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, ← coeff_C_mul]
  congr 1
  rw [← mul_assoc, C_mul_monomial, mul_one]

theorem map_universalMatrix {S : Type*} [CommRing S] (rho : R →+* S)
    (row : Monomial n d) (col : Monomial n (d - e)) :
    map rho (universalMatrix n d e R row col) = universalMatrix n d e S row col := by
  simp only [universalMatrix, map_sum, map_mul, map_C, map_X]
  apply Finset.sum_congr rfl
  intro i _
  rw [← coeff_map, map_mul, map_monomial, map_monomial, map_one]

theorem eval₂_universalMatrix {S : Type*} [CommRing S] (rho : R →+* S)
    (a : Monomial n e → S) (row : Monomial n d) (col : Monomial n (d - e)) :
    eval₂ rho a (universalMatrix n d e R row col) = multiplicationMatrix d e a row col := by
  rw [eval₂_eq_eval_map, map_universalMatrix, eval_universalMatrix]

abbrev minorSize (n d e : ℕ) := Fintype.card (Monomial n (d - e)) + 1

abbrev EquationIndex (n d e : ℕ) :=
  (Fin (minorSize n d e) → Monomial n d) ×
    (Fin (minorSize n d e) → Option (Monomial n (d - e)))

def augmentedMatrix (d e : ℕ) (F : MvPolynomial (Fin n) R) :
    Matrix (Monomial n d) (Option (Monomial n (d - e)))
      (MvPolynomial (Monomial n e) R) :=
  augment (universalMatrix n d e R) (fun row ↦ C (coeff row.val F))

def equations (d e : ℕ) (F : MvPolynomial (Fin n) R)
    (i : EquationIndex n d e) : MvPolynomial (Monomial n e) R :=
  ((augmentedMatrix d e F).submatrix i.1 i.2).det

def columnDegree (j : Option (Monomial n (d - e))) : ℕ :=
  Option.elim' 0 (fun _ ↦ 1) j

def degrees (i : EquationIndex n d e) : ℕ := ∑ j, columnDegree (e := e) (i.2 j)

theorem augmentedMatrix_homogeneous (F : MvPolynomial (Fin n) R)
    (row : Monomial n d) (col : Option (Monomial n (d - e))) :
    (augmentedMatrix d e F row col).IsHomogeneous (columnDegree (e := e) col) := by
  cases col with
  | none => exact isHomogeneous_C (σ := Monomial n e) (coeff row.val F)
  | some col => exact universalMatrix_homogeneous row col

theorem equations_homogeneous (F : MvPolynomial (Fin n) R)
    (i : EquationIndex n d e) :
    (equations d e F i).IsHomogeneous (degrees (e := e) i) := by
  rw [equations, Matrix.det_apply']
  apply IsHomogeneous.sum
  intro s _
  have hp : (∏ j, augmentedMatrix d e F (i.1 (s j)) (i.2 j)).IsHomogeneous
      (degrees (e := e) i) :=
    IsHomogeneous.prod Finset.univ
      (fun j ↦ augmentedMatrix d e F (i.1 (s j)) (i.2 j))
      (fun j ↦ columnDegree (e := e) (i.2 j))
      (fun j _ ↦ augmentedMatrix_homogeneous F _ _)
  simpa using hp.C_mul (((Equiv.Perm.sign s : ℤ) : R))

theorem eval₂_augmentedMatrix {K : Type*} [CommRing K] (rho : R →+* K)
    (F : MvPolynomial (Fin n) R) (a : Monomial n e → K) :
    (augmentedMatrix d e F).map (eval₂Hom rho a) =
      augment (multiplicationMatrix d e a)
        (fun row : Monomial n d ↦ coeff row.val (map rho F)) := by
  ext row col
  cases col with
  | none => simp [augmentedMatrix, augment, coeff_map]
  | some col => exact eval₂_universalMatrix rho a row col

theorem eval₂_equations {K : Type*} [CommRing K] (rho : R →+* K)
    (F : MvPolynomial (Fin n) R) (a : Monomial n e → K)
    (i : EquationIndex n d e) :
    eval₂ rho a (equations d e F i) =
      ((augment (multiplicationMatrix d e a)
        (fun row : Monomial n d ↦ coeff row.val (map rho F))).submatrix i.1 i.2).det := by
  change eval₂Hom rho a (((augmentedMatrix d e F).submatrix i.1 i.2).det) = _
  rw [RingHom.map_det]
  change (((augmentedMatrix d e F).submatrix i.1 i.2).map (eval₂Hom rho a)).det = _
  rw [← Matrix.submatrix_map, eval₂_augmentedMatrix]

theorem map_augmentedMatrix {S : Type*} [CommRing S] (rho : R →+* S)
    (F : MvPolynomial (Fin n) R) :
    (augmentedMatrix d e F).map (map rho) = augmentedMatrix d e (map rho F) := by
  funext row col
  cases col with
  | none => simp [augmentedMatrix, augment, coeff_map]
  | some col => exact map_universalMatrix rho row col

theorem map_equations {S : Type*} [CommRing S] (rho : R →+* S)
    (F : MvPolynomial (Fin n) R) (i : EquationIndex n d e) :
    map rho (equations d e F i) = equations d e (map rho F) i := by
  rw [equations, RingHom.map_det]
  change (((augmentedMatrix d e F).submatrix i.1 i.2).map (map rho)).det = _
  rw [← Matrix.submatrix_map, map_augmentedMatrix]
  rfl

theorem vanishing_iff_solution {K : Type*} [Field K] (he : e ≤ d)
    (F : MvPolynomial (Fin n) K) (a : Monomial n e → K) (ha : a ≠ 0) :
    (∀ i : EquationIndex n d e, eval a (equations d e F i) = 0) ↔
      ∃ c : Monomial n (d - e) → K,
        (multiplicationMatrix d e a).mulVec c =
          fun row : Monomial n d ↦ coeff row.val F := by
  have heval (i : EquationIndex n d e) : eval a (equations d e F i) =
      ((augment (multiplicationMatrix d e a)
        (fun row : Monomial n d ↦ coeff row.val F)).submatrix i.1 i.2).det := by
    simpa only [eval₂_id, map_id] using
      eval₂_equations (RingHom.id K) F a i
  simp only [heval]
  rw [exists_mulVec_eq_iff_rank_le (multiplicationMatrix d e a)
    (fun row : Monomial n d ↦ coeff row.val F)
    (multiplicationMatrix_rank he a ha), rank_le_iff_maximal_minors_zero]
  exact Prod.forall

end CubicTenVariables.GeneralHomogeneousFactorMinors
