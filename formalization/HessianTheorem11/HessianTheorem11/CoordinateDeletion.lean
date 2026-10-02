import HessianTheorem11.RadialPureCube

/-! Delete one coordinate using an explicit rectangular linear embedding.
The coordinate ring substitution, its re-embedding, and homogeneity are all
computed directly. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

def coordinateDeletionMatrix (c : Fin (n+1)) : Matrix (Fin (n+1)) (Fin n) K :=
  fun i j => if i = c.succAbove j then 1 else 0

def deleteCoordinate (c : Fin (n+1)) :
    MvPolynomial (Fin (n+1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (c.insertNth 0 X)

theorem coordinateDeletionMatrix_linearForms (c : Fin (n+1)) (i : Fin (n+1)) :
    PolynomialRestriction.linearForms (coordinateDeletionMatrix c : Matrix _ _ K) i =
      Fin.insertNth (α := fun _ : Fin (n+1) => MvPolynomial (Fin n) K) c 0 X i := by
  classical
  cases i using c.succAboveCases with
  | x => simp [PolynomialRestriction.linearForms, coordinateDeletionMatrix, c.ne_succAbove]
  | p i =>
    simp [PolynomialRestriction.linearForms, coordinateDeletionMatrix,
      Fin.succAbove_right_inj, smul_eq_mul]

theorem deleteCoordinate_eq_restrict (c : Fin (n+1))
    (G : MvPolynomial (Fin (n+1)) K) :
    deleteCoordinate c G = PolynomialRestriction.restrict (coordinateDeletionMatrix c) G := by
  unfold deleteCoordinate PolynomialRestriction.restrict
  have he : PolynomialRestriction.linearForms (coordinateDeletionMatrix c : Matrix _ _ K) =
      c.insertNth 0 X := funext (coordinateDeletionMatrix_linearForms (K := K) c)
  rw [he]

@[simp] theorem coordinateDeletionMatrix_mulVec (c : Fin (n+1)) (v : Fin n → K) :
    (coordinateDeletionMatrix c).mulVec v = c.insertNth 0 v := by
  classical
  ext i
  cases i using c.succAboveCases with
  | x => simp [Matrix.mulVec, dotProduct, coordinateDeletionMatrix, c.ne_succAbove]
  | p i => simp [Matrix.mulVec, dotProduct, coordinateDeletionMatrix, Fin.succAbove_right_inj]

theorem coordinateDeletionMatrix_injective (c : Fin (n+1)) :
    Function.Injective (coordinateDeletionMatrix c : Matrix _ _ K).mulVec := by
  intro u v huv
  simp only [coordinateDeletionMatrix_mulVec] at huv
  exact Fin.insertNth_right_injective 0 huv

theorem rename_deleteCoordinate (c : Fin (n+1))
    (G : MvPolynomial (Fin (n+1)) K) :
    rename c.succAbove (deleteCoordinate c G) = eraseCoordinate c G := by
  have he : (rename (R := K) c.succAbove).comp (deleteCoordinate c) = eraseCoordinate c := by
    ext i
    cases i using c.succAboveCases with
    | x => simp [deleteCoordinate, eraseCoordinate]
    | p j => simp [deleteCoordinate, eraseCoordinate, c.succAbove_ne]
  exact congrArg (fun f : MvPolynomial (Fin (n+1)) K →ₐ[K] MvPolynomial (Fin (n+1)) K => f G) he

theorem deleteCoordinate_homogeneous (c : Fin (n+1))
    (G : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hG : G.IsHomogeneous d) :
    (deleteCoordinate c G).IsHomogeneous d := by
  rw [deleteCoordinate_eq_restrict]
  exact PolynomialRestriction.homogeneous_restrict _ G hG

end HessianTheorem11
