import HessianTheorem11.SchurSecondOrder
import HessianTheorem11.CubicIdentities

/-!
The coefficients in the second-order calculation are derived from an actual
polynomial in normal coordinates. Existence of those coordinates is a separate
geometric construction; this module does not postulate it.
-/

set_option linter.unusedSimpArgs false

noncomputable section
namespace HessianTheorem11.LocalCubicNormalForm
open MvPolynomial Matrix
open scoped BigOperators

variable {K : Type*} [Field K]

abbrev Coordinate (m q : ℕ) := Fin m ⊕ (Fin q ⊕ Fin 2)
abbrev ResidualCoordinate (q : ℕ) := Fin q ⊕ Unit

def aIndex {m q : ℕ} (i : Fin m) : Coordinate m q := Sum.inl i
def bIndex {m q : ℕ} (i : Fin q) : Coordinate m q := Sum.inr (Sum.inl i)
def xIndex (m q : ℕ) : Coordinate m q := Sum.inr (Sum.inr 0)
def zIndex (m q : ℕ) : Coordinate m q := Sum.inr (Sum.inr 1)

def residualIndex {m q : ℕ} : ResidualCoordinate q → Coordinate m q :=
  Sum.elim bIndex (fun _ => zIndex m q)

theorem pderiv_rename_outside {σ τ : Type*} (f : σ → τ)
    (i : τ) (p : MvPolynomial σ K) (hi : ∀ j, f j ≠ i) :
    pderiv i (rename f p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp, pderiv_X_of_ne (hi j)]

@[simp] theorem pderiv_a_rename_a {m q : ℕ} (i : Fin m) (p : MvPolynomial (Fin m) K) :
    pderiv (aIndex (q := q) i) (rename aIndex p) = rename aIndex (pderiv i p) :=
  pderiv_rename Sum.inl_injective i p

@[simp] theorem pderiv_b_rename_b {m q : ℕ} (i : Fin q) (p : MvPolynomial (Fin q) K) :
    pderiv (bIndex (m := m) i) (rename bIndex p) = rename bIndex (pderiv i p) :=
  pderiv_rename (Sum.inr_injective.comp Sum.inl_injective) i p

@[simp] theorem pderiv_a_rename_b {m q : ℕ} (i : Fin m) (p : MvPolynomial (Fin q) K) :
    pderiv (aIndex i) (rename (bIndex (m := m)) p) = 0 :=
  pderiv_rename_outside _ _ p (by intro j; simp [aIndex, bIndex])

@[simp] theorem pderiv_b_rename_a {m q : ℕ} (i : Fin q) (p : MvPolynomial (Fin m) K) :
    pderiv (bIndex i) (rename (aIndex (q := q)) p) = 0 :=
  pderiv_rename_outside _ _ p (by intro j; simp [aIndex, bIndex])

@[simp] theorem pderiv_x_rename_a {m q : ℕ} (p : MvPolynomial (Fin m) K) :
    pderiv (xIndex m q) (rename aIndex p) = 0 :=
  pderiv_rename_outside _ _ p (by intro j; simp [aIndex, xIndex])

@[simp] theorem pderiv_z_rename_a {m q : ℕ} (p : MvPolynomial (Fin m) K) :
    pderiv (zIndex m q) (rename aIndex p) = 0 :=
  pderiv_rename_outside _ _ p (by intro j; simp [aIndex, zIndex])

@[simp] theorem pderiv_x_rename_b {m q : ℕ} (p : MvPolynomial (Fin q) K) :
    pderiv (xIndex m q) (rename bIndex p) = 0 :=
  pderiv_rename_outside _ _ p (by intro j; simp [bIndex, xIndex])

@[simp] theorem pderiv_z_rename_b {m q : ℕ} (p : MvPolynomial (Fin q) K) :
    pderiv (zIndex m q) (rename bIndex p) = 0 :=
  pderiv_rename_outside _ _ p (by intro j; simp [bIndex, zIndex])

@[simp] theorem pderiv_a_rename_residual {m q : ℕ} (i : Fin m)
    (p : MvPolynomial (ResidualCoordinate q) K) :
    pderiv (aIndex i) (rename (residualIndex (m := m)) p) = 0 :=
  pderiv_rename_outside _ _ p (by intro j; cases j <;> simp [residualIndex, aIndex, bIndex, zIndex])

@[simp] theorem pderiv_x_rename_residual {m q : ℕ}
    (p : MvPolynomial (ResidualCoordinate q) K) :
    pderiv (xIndex m q) (rename residualIndex p) = 0 :=
  pderiv_rename_outside _ _ p (by intro j; cases j <;> simp [residualIndex, xIndex, bIndex, zIndex])

/-- Quadratic data retain their actual polynomial meaning. The remainder is
`abz + az² + R₀(b,z)`, with `R₀` an arbitrary homogeneous cubic. -/
structure Data (m q : ℕ) where
  QA : MvPolynomial (Fin m) K
  Q0 : MvPolynomial (Fin q) K
  Q : Fin m → MvPolynomial (Fin q) K
  QA_homogeneous : QA.IsHomogeneous 2
  Q0_homogeneous : Q0.IsHomogeneous 2
  Q_homogeneous : ∀ i, (Q i).IsHomogeneous 2
  abz : Matrix (Fin m) (Fin q) K
  azz : Fin m → K
  R : MvPolynomial (ResidualCoordinate q) K
  R_homogeneous : R.IsHomogeneous 3

def polynomial {m q : ℕ} (D : Data (K := K) m q) : MvPolynomial (Coordinate m q) K :=
  X (zIndex m q) * (X (xIndex m q)) ^ 2 +
  X (zIndex m q) * rename aIndex D.QA +
  X (xIndex m q) * rename bIndex D.Q0 +
  (∑ i, X (aIndex i) * rename bIndex (D.Q i)) +
  (∑ i, ∑ j, C (D.abz i j) * X (aIndex i) * X (bIndex j) * X (zIndex m q)) +
  (∑ i, C (D.azz i) * X (aIndex i) * (X (zIndex m q)) ^ 2) +
  rename residualIndex D.R

/-- The constant Hessian matrix of a quadratic polynomial. -/
def quadraticMatrix {n : ℕ} (Q : MvPolynomial (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  fun i j => coeff 0 (pderiv j (pderiv i Q))

theorem quadraticMatrix_symmetric {n : ℕ} (Q : MvPolynomial (Fin n) K) :
    (quadraticMatrix Q).transpose = quadraticMatrix Q := by
  ext i j
  exact congrArg (coeff 0) (partials_commute Q i j)

theorem homogeneous_zero_eq_constant {σ : Type*} (p : MvPolynomial σ K)
    (hp : p.IsHomogeneous 0) : p = C (coeff 0 p) := by
  have h := (totalDegree_zero_iff_isHomogeneous σ).mpr hp
  exact totalDegree_eq_zero_iff_eq_C.mp h

theorem quadratic_second_partial {n : ℕ} (Q : MvPolynomial (Fin n) K)
    (hQ : Q.IsHomogeneous 2) (i j : Fin n) :
    pderiv j (pderiv i Q) = C (quadraticMatrix Q i j) :=
  homogeneous_zero_eq_constant _ hQ.pderiv.pderiv

theorem quadratic_first_partial {n : ℕ} (Q : MvPolynomial (Fin n) K)
    (hQ : Q.IsHomogeneous 2) (i : Fin n) :
    pderiv i Q = ∑ j, C (quadraticMatrix Q i j) * X j := by
  have hi : (pderiv i Q).IsHomogeneous 1 := hQ.pderiv
  have h := hi.sum_X_mul_pderiv
  simp only [one_nsmul, quadratic_second_partial Q hQ] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem quadratic_eval_identity {n : ℕ} (Q : MvPolynomial (Fin n) K)
    (hQ : Q.IsHomogeneous 2) (v : Fin n → K) :
    dotProduct v ((quadraticMatrix Q).mulVec v) = 2 * eval v Q := by
  have h := congrArg (eval v) hQ.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, quadratic_first_partial Q hQ, eval_C] at h
  simpa [dotProduct, Matrix.mulVec, nsmul_eq_mul] using h

/-- The formal curve used in Lemma 7.3. Its `z` coordinate is left as an
actual power series, so all higher implicit-function coefficients are retained. -/
def curve {m q : ℕ} (v : Fin q → K) (z : PowerSeries K) :
    Coordinate m q → PowerSeries K :=
  Sum.elim (fun _ => 0)
    (Sum.elim (fun j => PowerSeries.C (v j) * PowerSeries.X) ![1, z])

def seriesEval {m q : ℕ} (v : Fin q → K) (z : PowerSeries K) :
    MvPolynomial (Coordinate m q) K →+* PowerSeries K :=
  eval₂Hom PowerSeries.C (curve (m := m) v z)

def hessianSeries {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) :
    Matrix (Coordinate m q) (Coordinate m q) (PowerSeries K) :=
  fun i j => seriesEval v z (pderiv j (pderiv i (polynomial D)))

def aBlock {m q : ℕ} (D : Data (K := K) m q) (v : Fin q → K) (z : PowerSeries K) :
    Matrix (Fin m) (Fin m) (PowerSeries K) :=
  (hessianSeries D v z).submatrix Sum.inl Sum.inl

def crossBlock {m q : ℕ} (D : Data (K := K) m q) (v : Fin q → K) (z : PowerSeries K) :
    Matrix (Fin m) (Fin q ⊕ Fin 2) (PowerSeries K) :=
  (hessianSeries D v z).submatrix Sum.inl Sum.inr

def normalBlock {m q : ℕ} (D : Data (K := K) m q) (v : Fin q → K) (z : PowerSeries K) :
    Matrix (Fin q ⊕ Fin 2) (Fin q ⊕ Fin 2) (PowerSeries K) :=
  (hessianSeries D v z).submatrix Sum.inr Sum.inr

/-- The first kernel-coordinate derivative, including both allowed terms
of the remainder that contain a kernel coordinate. -/
theorem a_partial {m q : ℕ} (D : Data (K := K) m q) (i : Fin m) :
    pderiv (aIndex i) (polynomial D) =
      X (zIndex m q) * rename aIndex (pderiv i D.QA) + rename bIndex (D.Q i) +
      (∑ j, C (D.abz i j) * X (bIndex j) * X (zIndex m q)) +
      C (D.azz i) * (X (zIndex m q)) ^ 2 := by
  classical
  simp only [polynomial, map_add, map_sum, pderiv_mul, pderiv_pow,
    pderiv_a_rename_a, pderiv_a_rename_b, pderiv_a_rename_residual]
  simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
    mul_assoc, mul_left_comm, mul_comm]

theorem aa_partial {m q : ℕ} (D : Data (K := K) m q) (i j : Fin m) :
    pderiv (aIndex j) (pderiv (aIndex i) (polynomial D)) =
      C (quadraticMatrix D.QA i j) * X (zIndex m q) := by
  classical
  rw [a_partial]
  simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
    pderiv_a_rename_a, pderiv_a_rename_b, quadratic_second_partial D.QA D.QA_homogeneous]
  simp [pderiv_X, Pi.single_apply, aIndex, bIndex, zIndex, mul_comm]

theorem ab_partial {m q : ℕ} (D : Data (K := K) m q) (i : Fin m) (j : Fin q) :
    pderiv (bIndex j) (pderiv (aIndex i) (polynomial D)) =
      rename bIndex (pderiv j (D.Q i)) + C (D.abz i j) * X (zIndex m q) := by
  classical
  rw [a_partial]
  simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
    pderiv_b_rename_a, pderiv_b_rename_b]
  simp [pderiv_X, Pi.single_apply, aIndex, bIndex, zIndex, mul_comm]

theorem ax_partial {m q : ℕ} (D : Data (K := K) m q) (i : Fin m) :
    pderiv (xIndex m q) (pderiv (aIndex i) (polynomial D)) = 0 := by
  classical
  rw [a_partial]
  simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
    pderiv_x_rename_a, pderiv_x_rename_b]
  simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex]

theorem az_partial {m q : ℕ} (D : Data (K := K) m q) (i : Fin m) :
    pderiv (zIndex m q) (pderiv (aIndex i) (polynomial D)) =
      rename aIndex (pderiv i D.QA) +
      (∑ j, C (D.abz i j) * X (bIndex j)) +
      C (2 * D.azz i) * X (zIndex m q) := by
  classical
  rw [a_partial]
  simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
    pderiv_z_rename_a, pderiv_z_rename_b]
  simp [pderiv_X, Pi.single_apply, aIndex, bIndex, zIndex]
  have hC2 : (C (2 : K) : MvPolynomial (Coordinate m q) K) = 2 := map_ofNat _ _
  simp only [map_mul, hC2]
  ring

theorem seriesEval_quadratic_first_a {m q : ℕ}
    (Q : MvPolynomial (Fin m) K) (hQ : Q.IsHomogeneous 2) (i : Fin m)
    (v : Fin q → K) (z : PowerSeries K) :
    seriesEval v z (rename aIndex (pderiv i Q)) = 0 := by
  rw [quadratic_first_partial Q hQ]
  simp [seriesEval, curve, aIndex]

theorem seriesEval_quadratic_first_b {m q : ℕ}
    (Q : MvPolynomial (Fin q) K) (hQ : Q.IsHomogeneous 2) (i : Fin q)
    (v : Fin q → K) (z : PowerSeries K) :
    seriesEval (m := m) v z (rename bIndex (pderiv i Q)) =
      PowerSeries.C ((quadraticMatrix Q).mulVec v i) * PowerSeries.X := by
  rw [quadratic_first_partial Q hQ]
  simp [seriesEval, curve, bIndex, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem aBlock_exact {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (i j : Fin m) :
    aBlock D v z i j = PowerSeries.C (quadraticMatrix D.QA i j) * z := by
  change seriesEval v z (pderiv (aIndex j) (pderiv (aIndex i) (polynomial D))) = _
  rw [aa_partial]
  simp [seriesEval, curve, zIndex]

theorem crossBlock_b_exact {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (i : Fin m) (j : Fin q) :
    crossBlock D v z i (Sum.inl j) =
      PowerSeries.C ((quadraticMatrix (D.Q i)).mulVec v j) * PowerSeries.X +
        PowerSeries.C (D.abz i j) * z := by
  change seriesEval v z (pderiv (bIndex j) (pderiv (aIndex i) (polynomial D))) = _
  rw [ab_partial, map_add, seriesEval_quadratic_first_b (D.Q i) (D.Q_homogeneous i)]
  simp [seriesEval, curve, zIndex]

theorem crossBlock_x_exact {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (i : Fin m) :
    crossBlock D v z i (Sum.inr 0) = 0 := by
  change seriesEval v z (pderiv (xIndex m q) (pderiv (aIndex i) (polynomial D))) = _
  rw [ax_partial, map_zero]

theorem crossBlock_z_exact {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (i : Fin m) :
    crossBlock D v z i (Sum.inr 1) =
      PowerSeries.C (D.abz.mulVec v i) * PowerSeries.X + PowerSeries.C (2 * D.azz i) * z := by
  change seriesEval v z (pderiv (zIndex m q) (pderiv (aIndex i) (polynomial D))) = _
  rw [az_partial, map_add, map_add,
    seriesEval_quadratic_first_a D.QA D.QA_homogeneous, zero_add]
  simp [seriesEval, curve, bIndex, zIndex, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem crossBlock_coeff_zero {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (hz : PowerSeries.coeff 0 z = 0) :
    SchurSecondOrder.matrixCoeff 0 (crossBlock D v z) = 0 := by
  have hconst : PowerSeries.constantCoeff z = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hz
  ext i j
  rcases j with j | j
  · change PowerSeries.coeff 0 (crossBlock D v z i (Sum.inl j)) = 0
    rw [crossBlock_b_exact]
    simp [PowerSeries.coeff_C_mul, hconst]
  · fin_cases j
    · change PowerSeries.coeff 0 (crossBlock D v z i (Sum.inr 0)) = 0
      rw [crossBlock_x_exact]
      simp
    · change PowerSeries.coeff 0 (crossBlock D v z i (Sum.inr 1)) = 0
      rw [crossBlock_z_exact]
      simp [PowerSeries.coeff_C_mul, hconst]

theorem crossBlock_coeff_one {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (hz : PowerSeries.coeff 1 z = 0) :
    SchurSecondOrder.matrixCoeff 1 (crossBlock D v z) =
      SchurSecondOrder.crossFirst
        (SchurSecondOrder.quadraticRows (fun i => quadraticMatrix (D.Q i)) v) (D.abz.mulVec v) := by
  ext i j
  rcases j with j | j
  · change PowerSeries.coeff 1 (crossBlock D v z i (Sum.inl j)) = _
    rw [crossBlock_b_exact]
    simp [PowerSeries.coeff_C_mul, hz, SchurSecondOrder.crossFirst, SchurSecondOrder.quadraticRows]
  · fin_cases j
    · change PowerSeries.coeff 1 (crossBlock D v z i (Sum.inr 0)) = _
      rw [crossBlock_x_exact]
      simp [SchurSecondOrder.crossFirst]
    · change PowerSeries.coeff 1 (crossBlock D v z i (Sum.inr 1)) = _
      rw [crossBlock_z_exact]
      simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one_X, hz,
        mul_one, mul_zero, add_zero]
      rfl

theorem aBlock_coefficient {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (d : ℕ) :
    SchurSecondOrder.matrixCoeff d (aBlock D v z) =
      (PowerSeries.coeff d z) • quadraticMatrix D.QA := by
  ext i j
  change PowerSeries.coeff d (aBlock D v z i j) = _
  rw [aBlock_exact, PowerSeries.coeff_C_mul]
  change quadraticMatrix D.QA i j * PowerSeries.coeff d z =
    PowerSeries.coeff d z * quadraticMatrix D.QA i j
  ring

theorem aBlock_coeff_two [CharZero K] {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K)
    (hz : PowerSeries.coeff 2 z = -eval v D.Q0) :
    SchurSecondOrder.matrixCoeff 2 (aBlock D v z) =
      (-dotProduct v ((quadraticMatrix D.Q0).mulVec v)) •
        ((2 : K)⁻¹ • quadraticMatrix D.QA) := by
  rw [aBlock_coefficient, hz, smul_smul,
    quadratic_eval_identity D.Q0 D.Q0_homogeneous v]
  congr 1
  have ht : (2 : K) ≠ 0 := by norm_num
  field_simp

theorem residualIndex_injective {m q : ℕ} :
    Function.Injective (residualIndex (m := m) (q := q)) := by
  intro i j h
  cases i <;> cases j <;> simp_all [residualIndex, bIndex, zIndex]

@[simp] theorem pderiv_b_rename_residual {m q : ℕ} (i : Fin q)
    (p : MvPolynomial (ResidualCoordinate q) K) :
    pderiv (bIndex (m := m) i) (rename residualIndex p) =
      rename residualIndex (pderiv (Sum.inl i) p) :=
  pderiv_rename residualIndex_injective (Sum.inl i) p

@[simp] theorem pderiv_z_rename_residual {m q : ℕ}
    (p : MvPolynomial (ResidualCoordinate q) K) :
    pderiv (zIndex m q) (rename residualIndex p) =
      rename residualIndex (pderiv (Sum.inr ()) p) :=
  pderiv_rename residualIndex_injective (Sum.inr ()) p

def basePoint (m q : ℕ) : Coordinate m q → K :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) ![1, 0])

theorem coeff_zero_seriesEval {m q : ℕ} (v : Fin q → K) (z : PowerSeries K)
    (hz : PowerSeries.coeff 0 z = 0) (p : MvPolynomial (Coordinate m q) K) :
    PowerSeries.coeff 0 (seriesEval v z p) = eval (basePoint m q) p := by
  have hconst : PowerSeries.constantCoeff z = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hz
  have hh : PowerSeries.constantCoeff.comp (seriesEval v z) = eval (basePoint m q) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [seriesEval]
    · intro i
      rcases i with i | (i | i)
      · simp [seriesEval, curve, basePoint]
      · simp [seriesEval, curve, basePoint]
      · fin_cases i <;> simp [seriesEval, curve, basePoint, hconst]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact congrArg (fun f : MvPolynomial (Coordinate m q) K →+* K => f p) hh

theorem eval_zero_positive_homogeneous {σ : Type*} {d : ℕ}
    (p : MvPolynomial σ K) (hp : p.IsHomogeneous d) (hd : d ≠ 0) : eval 0 p = 0 := by
  rw [eval_zero]
  exact hp.coeff_eq_zero (by simpa using Ne.symm hd)

@[simp] theorem eval_base_rename_residual {m q : ℕ}
    (p : MvPolynomial (ResidualCoordinate q) K) :
    eval (basePoint m q) (rename residualIndex p) = eval 0 p := by
  rw [eval_rename]
  have h : (basePoint (K := K) m q) ∘ (residualIndex (m := m) (q := q)) =
      (0 : ResidualCoordinate q → K) := by
    funext i
    cases i <;> simp [basePoint, residualIndex, bIndex, zIndex]
  rw [h]

@[simp] theorem eval_base_rename_b {m q : ℕ} (p : MvPolynomial (Fin q) K) :
    eval (basePoint m q) (rename bIndex p) = eval 0 p := by
  rw [eval_rename]
  rfl

@[simp] theorem eval_base_rename_a {m q : ℕ} (p : MvPolynomial (Fin m) K) :
    eval (basePoint m q) (rename aIndex p) = eval 0 p := by
  rw [eval_rename]
  rfl

theorem residual_second_partial_at_base {m q : ℕ} (D : Data (K := K) m q)
    (i j : ResidualCoordinate q) :
    eval (basePoint m q) (rename residualIndex (pderiv j (pderiv i D.R))) = 0 := by
  rw [eval_base_rename_residual]
  exact eval_zero_positive_homogeneous _ D.R_homogeneous.pderiv.pderiv (by decide)

theorem x_partial {m q : ℕ} (D : Data (K := K) m q) :
    pderiv (xIndex m q) (polynomial D) =
      2 * X (zIndex m q) * X (xIndex m q) + rename bIndex D.Q0 := by
  classical
  simp only [polynomial, map_add, map_sum, pderiv_mul, pderiv_pow,
    pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual]
  simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex]
  ring

theorem b_partial {m q : ℕ} (D : Data (K := K) m q) (j : Fin q) :
    pderiv (bIndex j) (polynomial D) =
      X (xIndex m q) * rename bIndex (pderiv j D.Q0) +
      (∑ i, X (aIndex i) * rename bIndex (pderiv j (D.Q i))) +
      (∑ i, C (D.abz i j) * X (aIndex i) * X (zIndex m q)) +
      rename residualIndex (pderiv (Sum.inl j) D.R) := by
  classical
  simp only [polynomial, map_add, map_sum, pderiv_mul, pderiv_pow,
    pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual]
  simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
    mul_assoc, mul_left_comm, mul_comm]

theorem z_partial {m q : ℕ} (D : Data (K := K) m q) :
    pderiv (zIndex m q) (polynomial D) =
      (X (xIndex m q)) ^ 2 + rename aIndex D.QA +
      (∑ i, ∑ j, C (D.abz i j) * X (aIndex i) * X (bIndex j)) +
      (∑ i, C (D.azz i) * X (aIndex i) * (2 * X (zIndex m q))) +
      rename residualIndex (pderiv (Sum.inr ()) D.R) := by
  classical
  simp only [polynomial, map_add, map_sum, pderiv_mul, pderiv_pow,
    pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual]
  simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
    mul_assoc, mul_left_comm, mul_comm]

set_option maxHeartbeats 800000 in
/-- The constant complementary block is the actual Hessian of `Q₀` and the
hyperbolic `(X,z)` plane. Every remainder contribution vanishes at the base. -/
theorem normalBlock_coeff_zero {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (hz : PowerSeries.coeff 0 z = 0) :
    SchurSecondOrder.matrixCoeff 0 (normalBlock D v z) =
      SchurSecondOrder.normalInverse (quadraticMatrix D.Q0) 2 := by
  classical
  have hR (i j : ResidualCoordinate q) : constantCoeff (pderiv j (pderiv i D.R)) = 0 := by
    simpa only [eval_zero] using
      eval_zero_positive_homogeneous (pderiv j (pderiv i D.R))
        D.R_homogeneous.pderiv.pderiv (by decide)
  have hQ (i : Fin q) : constantCoeff (pderiv i D.Q0) = 0 := by
    simpa only [eval_zero] using
      eval_zero_positive_homogeneous (pderiv i D.Q0) D.Q0_homogeneous.pderiv (by decide)
  ext i j
  change PowerSeries.coeff 0 (seriesEval v z
    (pderiv (Sum.inr j) (pderiv (Sum.inr i) (polynomial D)))) = _
  rw [coeff_zero_seriesEval v z hz]
  rcases i with i | i <;> rcases j with j | j
  · change eval (basePoint m q) (pderiv (bIndex j) (pderiv (bIndex i) (polynomial D))) = _
    rw [b_partial]
    simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
      pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual,
      pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual,
      pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual,
      quadratic_second_partial D.Q0 D.Q0_homogeneous]
    simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
      hR, hQ, SchurSecondOrder.normalInverse, Matrix.fromBlocks, apply_ite]
    simp [basePoint]
  · fin_cases j
    · change eval (basePoint m q) (pderiv (xIndex m q) (pderiv (bIndex i) (polynomial D))) = _
      rw [b_partial]
      simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
        pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual,
        pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual,
        pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual,
        quadratic_second_partial D.Q0 D.Q0_homogeneous]
      simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
        hR, hQ, SchurSecondOrder.normalInverse, Matrix.fromBlocks, apply_ite]
    · change eval (basePoint m q) (pderiv (zIndex m q) (pderiv (bIndex i) (polynomial D))) = _
      rw [b_partial]
      simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
        pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual,
        pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual,
        pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual,
        quadratic_second_partial D.Q0 D.Q0_homogeneous]
      simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
        hR, hQ, SchurSecondOrder.normalInverse, Matrix.fromBlocks, apply_ite]
      simp [basePoint]
  · fin_cases i
    · change eval (basePoint m q) (pderiv (bIndex j) (pderiv (xIndex m q) (polynomial D))) = _
      rw [x_partial]
      simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
        pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual,
        pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual,
        pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual,
        quadratic_second_partial D.Q0 D.Q0_homogeneous]
      simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
        hR, hQ, SchurSecondOrder.normalInverse, Matrix.fromBlocks, apply_ite]
      simp [basePoint]
    · change eval (basePoint m q) (pderiv (bIndex j) (pderiv (zIndex m q) (polynomial D))) = _
      rw [z_partial]
      simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
        pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual,
        pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual,
        pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual,
        quadratic_second_partial D.Q0 D.Q0_homogeneous]
      simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
        hR, hQ, SchurSecondOrder.normalInverse, Matrix.fromBlocks, apply_ite]
      simp [basePoint]
  · fin_cases i <;> fin_cases j
    · change eval (basePoint m q) (pderiv (xIndex m q) (pderiv (xIndex m q) (polynomial D))) = _
      rw [x_partial]
      simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
        pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual,
        pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual,
        pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual,
        quadratic_second_partial D.Q0 D.Q0_homogeneous]
      simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
        hR, hQ, SchurSecondOrder.normalInverse, Matrix.fromBlocks, apply_ite]
      simp [basePoint]
    · change eval (basePoint m q) (pderiv (zIndex m q) (pderiv (xIndex m q) (polynomial D))) = _
      rw [x_partial]
      simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
        pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual,
        pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual,
        pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual,
        quadratic_second_partial D.Q0 D.Q0_homogeneous]
      simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
        hR, hQ, SchurSecondOrder.normalInverse, Matrix.fromBlocks, apply_ite]
      simp [basePoint]
    · change eval (basePoint m q) (pderiv (xIndex m q) (pderiv (zIndex m q) (polynomial D))) = _
      rw [z_partial]
      simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
        pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual,
        pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual,
        pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual,
        quadratic_second_partial D.Q0 D.Q0_homogeneous]
      simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
        hR, hQ, SchurSecondOrder.normalInverse, Matrix.fromBlocks, apply_ite]
      simp [basePoint]
    · change eval (basePoint m q) (pderiv (zIndex m q) (pderiv (zIndex m q) (polynomial D))) = _
      rw [z_partial]
      simp only [map_add, map_sum, pderiv_mul, pderiv_pow,
        pderiv_b_rename_a, pderiv_b_rename_b, pderiv_b_rename_residual,
        pderiv_x_rename_a, pderiv_x_rename_b, pderiv_x_rename_residual,
        pderiv_z_rename_a, pderiv_z_rename_b, pderiv_z_rename_residual,
        quadratic_second_partial D.Q0 D.Q0_homogeneous]
      simp [pderiv_X, Pi.single_apply, aIndex, bIndex, xIndex, zIndex,
        hR, hQ, SchurSecondOrder.normalInverse, Matrix.fromBlocks, apply_ite]
      simp [basePoint]

/-- Homogeneous evaluation extracts a common scalar to its actual degree. -/
theorem homogeneous_eval₂_common_scalar {σ S : Type*} [CommSemiring S] {d : ℕ}
    (Q : MvPolynomial σ K) (hQ : Q.IsHomogeneous d) (f : K →+* S)
    (v : σ → S) (t : S) :
    eval₂ f (fun i => t * v i) Q = t ^ d * eval₂ f v Q := by
  classical
  induction hQ using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => simp [hp, hq, mul_add]
  | monomial e c he =>
    have hd : (∑ i ∈ e.support, e i) = d := by
      simpa [Finsupp.weight_apply] using he
    simp [eval₂_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hd, mul_assoc, mul_left_comm, mul_comm]

/-- If all coordinate series vanish at zero, a homogeneous degree-`d`
polynomial in those series has no coefficients below degree `d`. -/
theorem homogeneous_series_coeff_below {σ : Type*} {d l : ℕ}
    (Q : MvPolynomial σ K) (hQ : Q.IsHomogeneous d)
    (g : σ → PowerSeries K) (hg : ∀ i, PowerSeries.coeff 0 (g i) = 0)
    (hl : l < d) : PowerSeries.coeff l (eval₂ PowerSeries.C g Q) = 0 := by
  have hx (i : σ) : (PowerSeries.X : PowerSeries K) ∣ g i := by
    apply PowerSeries.X_dvd_iff.mpr
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hg i
  choose u hu using hx
  have he : g = fun i => PowerSeries.X * u i := by funext i; exact hu i
  rw [he, homogeneous_eval₂_common_scalar Q hQ, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hl]

theorem seriesEval_rename_a {m q : ℕ} (v : Fin q → K) (z : PowerSeries K)
    (Q : MvPolynomial (Fin m) K) :
    seriesEval v z (rename aIndex Q) = PowerSeries.C (coeff 0 Q) := by
  simp [seriesEval, eval₂_rename, curve, aIndex, Function.comp_def, eval₂_zero'_apply, constantCoeff_eq]

theorem eval₂_constant_series {σ : Type*} (v : σ → K) (Q : MvPolynomial σ K) :
    eval₂ PowerSeries.C (fun i => PowerSeries.C (v i)) Q = PowerSeries.C (eval v Q) := by
  simpa using (MvPolynomial.eval₂_comp_left (PowerSeries.C (R := K)) (RingHom.id K) v Q).symm

theorem seriesEval_rename_quadratic_b {m q : ℕ} (v : Fin q → K) (z : PowerSeries K)
    (Q : MvPolynomial (Fin q) K) (hQ : Q.IsHomogeneous 2) :
    seriesEval (m := m) v z (rename bIndex Q) =
      PowerSeries.X ^ 2 * PowerSeries.C (eval v Q) := by
  change eval₂ PowerSeries.C (curve v z) (rename bIndex Q) = _
  rw [eval₂_rename]
  have hp : curve (m := m) v z ∘ bIndex = fun i => PowerSeries.X * PowerSeries.C (v i) := by
    funext i
    simp [curve, bIndex, mul_comm]
  rw [hp, homogeneous_eval₂_common_scalar Q hQ, eval₂_constant_series]

def residualCurve {q : ℕ} (v : Fin q → K) (z : PowerSeries K) :
    ResidualCoordinate q → PowerSeries K :=
  Sum.elim (fun i => PowerSeries.C (v i) * PowerSeries.X) (fun _ => z)

def residualSeries {m q : ℕ} (D : Data (K := K) m q) (v : Fin q → K) (z : PowerSeries K) :
    PowerSeries K := eval₂ PowerSeries.C (residualCurve v z) D.R

theorem seriesEval_rename_residual {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) :
    seriesEval (m := m) v z (rename residualIndex D.R) = residualSeries D v z := by
  change eval₂ PowerSeries.C (curve v z) (rename residualIndex D.R) = _
  rw [eval₂_rename]
  unfold residualSeries
  congr 1
  funext i
  cases i <;> rfl

theorem residualSeries_coeff_below {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (hz : PowerSeries.coeff 0 z = 0)
    (l : ℕ) (hl : l < 3) : PowerSeries.coeff l (residualSeries D v z) = 0 := by
  apply homogeneous_series_coeff_below D.R D.R_homogeneous _ _ hl
  intro i
  rcases i with i | i
  · simp [residualCurve]
  · exact hz

/-- Exact formal-curve equation. Only the unrestricted cubic remainder in
`(b,z)` survives after setting all kernel variables to zero. -/
theorem polynomial_on_curve {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) :
    seriesEval v z (polynomial D) =
      z + PowerSeries.X ^ 2 * PowerSeries.C (eval v D.Q0) + residualSeries D v z := by
  have hQA : coeff 0 D.QA = 0 := D.QA_homogeneous.coeff_eq_zero (by simp)
  simp only [polynomial, map_add, map_sum, map_mul, map_pow,
    seriesEval_rename_a, hQA, map_zero, mul_zero, add_zero,
    seriesEval_rename_quadratic_b v z D.Q0 D.Q0_homogeneous,
    seriesEval_rename_residual]
  simp [seriesEval, curve, aIndex, bIndex, xIndex, zIndex]

/-- The first two implicit coefficients follow from the actual root
equation, without any truncated-root assumption. -/
theorem formal_root_first_two_coefficients {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) (hz : PowerSeries.coeff 0 z = 0)
    (hroot : seriesEval v z (polynomial D) = 0) :
    PowerSeries.coeff 1 z = 0 ∧ PowerSeries.coeff 2 z = -eval v D.Q0 := by
  rw [polynomial_on_curve] at hroot
  have h1 := congrArg (PowerSeries.coeff 1) hroot
  have h2 := congrArg (PowerSeries.coeff 2) hroot
  have hr1 := residualSeries_coeff_below D v z hz 1 (by decide)
  have hr2 := residualSeries_coeff_below D v z hz 2 (by decide)
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow, hr1] at h1
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow, hr2] at h2
  exact ⟨h1, eq_neg_of_add_eq_zero_left h2⟩

end HessianTheorem11.LocalCubicNormalForm
