import CubicTenVariables.CubicLinearFactorMatrix
import CubicTenVariables.MatrixAugmentedColumn

/-! A finite homogeneous system in the linear-factor coefficients whose
nonzero solutions are exactly the linear factors of a homogeneous cubic.
The quadratic coefficients are eliminated by literal maximal minors.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.CubicLinearFactorMinors
open MvPolynomial CubicFactorCharts CubicLinearFactorMatrix MatrixAugmentedColumn

variable {R : Type*} [CommRing R] {n : ℕ}

abbrev minorSize (n : ℕ) := Fintype.card (Monomial n 2) + 1
abbrev EquationIndex (n : ℕ) :=
  (Fin (minorSize n) → Monomial n 3) ×
    (Fin (minorSize n) → Option (Monomial n 2))

def augmentedMatrix (F : MvPolynomial (Fin n) R) :
    Matrix (Monomial n 3) (Option (Monomial n 2)) (MvPolynomial (Fin n) R) :=
  augment (universalMatrix n R) (fun row ↦ C (coeff row.val F))

def equations (F : MvPolynomial (Fin n) R) (i : EquationIndex n) :
    MvPolynomial (Fin n) R :=
  ((augmentedMatrix F).submatrix i.1 i.2).det

def columnDegree (j : Option (Monomial n 2)) : ℕ := Option.elim' 0 (fun _ ↦ 1) j

def degrees (i : EquationIndex n) : ℕ := ∑ j, columnDegree (i.2 j)

theorem augmentedMatrix_homogeneous (F : MvPolynomial (Fin n) R)
    (row : Monomial n 3) (col : Option (Monomial n 2)) :
    (augmentedMatrix F row col).IsHomogeneous (columnDegree col) := by
  cases col with
  | none => exact isHomogeneous_C (σ := Fin n) (coeff row.val F)
  | some col => exact universalMatrix_homogeneous n R row col

/-- Each minor has its displayed homogeneous degree in the linear-factor
coefficients. Repeated rows or columns cause no exceptional case. -/
theorem equations_homogeneous (F : MvPolynomial (Fin n) R) (i : EquationIndex n) :
    (equations F i).IsHomogeneous (degrees i) := by
  rw [equations, Matrix.det_apply']
  apply IsHomogeneous.sum
  intro s _
  have hp : (∏ j, augmentedMatrix F (i.1 (s j)) (i.2 j)).IsHomogeneous (degrees i) :=
    IsHomogeneous.prod Finset.univ (fun j ↦ augmentedMatrix F (i.1 (s j)) (i.2 j))
      (fun j ↦ columnDegree (i.2 j)) (fun j _ ↦ augmentedMatrix_homogeneous F _ _)
  simpa using hp.C_mul (((Equiv.Perm.sign s : ℤ) : R))

theorem eval₂_augmentedMatrix {K : Type*} [CommRing K]
    (ρ : R →+* K) (F : MvPolynomial (Fin n) R) (a : Fin n → K) :
    (augmentedMatrix F).map (eval₂Hom ρ a) =
      augment (multiplicationMatrix a)
        (fun row : Monomial n 3 ↦ coeff row.val (map ρ F)) := by
  ext row col
  cases col with
  | none => simp [augmentedMatrix, augment, coeff_map]
  | some col => exact eval₂_universalMatrix ρ a row col

/-- The specialized equations are precisely the minors of the actual
augmented multiplication matrix over the target coefficient field. -/
theorem eval₂_equations {K : Type*} [CommRing K]
    (ρ : R →+* K) (F : MvPolynomial (Fin n) R) (a : Fin n → K)
    (i : EquationIndex n) :
    eval₂ ρ a (equations F i) =
      ((augment (multiplicationMatrix a)
        (fun row : Monomial n 3 ↦ coeff row.val (map ρ F))).submatrix i.1 i.2).det := by
  change eval₂Hom ρ a (((augmentedMatrix F).submatrix i.1 i.2).det) = _
  rw [RingHom.map_det]
  change (((augmentedMatrix F).submatrix i.1 i.2).map (eval₂Hom ρ a)).det = _
  rw [← Matrix.submatrix_map, eval₂_augmentedMatrix]

theorem map_augmentedMatrix {S : Type*} [CommRing S]
    (ρ : R →+* S) (F : MvPolynomial (Fin n) R) :
    (augmentedMatrix F).map (map ρ) = augmentedMatrix (map ρ F) := by
  funext row col
  cases col with
  | none => simp [augmentedMatrix, augment, coeff_map]
  | some col => exact map_universalMatrix ρ row col

/-- The complete finite homogeneous system commutes with every change
of coefficient ring, including bad or noninjective specializations. -/
theorem map_equations {S : Type*} [CommRing S]
    (ρ : R →+* S) (F : MvPolynomial (Fin n) R) (i : EquationIndex n) :
    map ρ (equations F i) = equations (map ρ F) i := by
  rw [equations, RingHom.map_det]
  change (((augmentedMatrix F).submatrix i.1 i.2).map (map ρ)).det = _
  rw [← Matrix.submatrix_map, map_augmentedMatrix]
  rfl

theorem vanishing_iff_solution {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) (a : Fin n → K) (ha : a ≠ 0) :
    (∀ i : EquationIndex n, eval a (equations F i) = 0) ↔
      ∃ c : Monomial n 2 → K,
        (multiplicationMatrix a).mulVec c = fun row : Monomial n 3 ↦ coeff row.val F := by
  have he (i : EquationIndex n) : eval a (equations F i) =
      ((augment (multiplicationMatrix a)
        (fun row : Monomial n 3 ↦ coeff row.val F)).submatrix i.1 i.2).det := by
    simpa only [eval₂_id, map_id] using eval₂_equations (RingHom.id K) F a i
  simp only [he]
  rw [exists_mulVec_eq_iff_rank_le (multiplicationMatrix a)
    (fun row : Monomial n 3 ↦ coeff row.val F) (multiplicationMatrix_rank a ha),
    rank_le_iff_maximal_minors_zero]
  exact Prod.forall

/-- Reducibility is exactly a nonzero solution of this finite homogeneous
system. This is the proper projective witness needed for specialization. -/
theorem not_irreducible_iff_projective_solution {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hFne : F ≠ 0) :
    (¬ Irreducible F) ↔ ∃ a : Fin n → K, a ≠ 0 ∧
      ∀ i : EquationIndex n, eval a (equations F i) = 0 := by
  rw [not_irreducible_iff_matrix_solution F hF hFne]
  constructor
  · rintro ⟨a, ha, hc⟩
    exact ⟨a, ha, (vanishing_iff_solution F a ha).mpr hc⟩
  · rintro ⟨a, ha, hc⟩
    exact ⟨a, ha, (vanishing_iff_solution F a ha).mp hc⟩

end CubicTenVariables.CubicLinearFactorMinors
