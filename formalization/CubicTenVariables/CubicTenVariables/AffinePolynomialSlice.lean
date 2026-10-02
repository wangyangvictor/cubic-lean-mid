import HessianTheorem11.PolynomialRestriction
import TranslatedDepthSeven.AffinePolynomialChange

/-!
# Actual affine polynomial slices

Substitution along `z ↦ b + B*z` commutes with coefficient reduction, cannot
increase total degree, and transports the actual Hessian by matrix
congruence. The statements apply to arbitrary integral polynomials and their
residue-ring reductions; neither homogeneity nor nonsingularity is assumed.
-/

noncomputable section
namespace CubicTenVariables.AffinePolynomialSlice
open MvPolynomial
open HessianTheorem11.PolynomialRestriction

/-- Literal polynomial substitution along an affine rectangular matrix map. -/
def affineSlice {R : Type*} [CommRing R] {m n : ℕ}
    (F : MvPolynomial (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    (b : Fin n → R) : MvPolynomial (Fin m) R :=
  aeval (fun i => C (b i) + linearForms B i) F

@[simp] theorem eval_affineSlice {R : Type*} [CommRing R] {m n : ℕ}
    (F : MvPolynomial (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    (b : Fin n → R) (z : Fin m → R) :
    eval z (affineSlice F B b) = eval (b + B.mulVec z) F := by
  change aeval z (aeval (fun i => C (b i) + linearForms B i) F) =
    aeval (b + B.mulVec z) F
  rw [comp_aeval_apply]
  have hforms : (fun i => aeval z (C (b i) + linearForms B i)) = b + B.mulVec z := by
    funext i
    change eval z (C (b i) + linearForms B i) = _
    simp only [eval_add, eval_C, eval_linearForms, Pi.add_apply]
  rw [hforms]

/-- Coefficientwise reduction or any coefficient homomorphism commutes
with the literal affine substitution. -/
theorem map_affineSlice {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}
    (f : R →+* S) (F : MvPolynomial (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) (b : Fin n → R) :
    map f (affineSlice F B b) =
      affineSlice (map f F) (B.map f) (fun i => f (b i)) := by
  change map f (eval₂ C (fun i => C (b i) + linearForms B i) F) =
    eval₂ C (fun i => C (f (b i)) + linearForms (B.map f) i) (map f F)
  rw [map_eval₂]
  congr 1
  funext i
  simp [linearForms, Matrix.map_apply]

/-- Evaluation in any residue ring is evaluation of the original
polynomial at the actual reduced affine point. -/
theorem eval₂_affineSlice {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}
    (f : R →+* S) (F : MvPolynomial (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) (b : Fin n → R) (z : Fin m → S) :
    eval₂ f z (affineSlice F B b) =
      eval₂ f ((fun i => f (b i)) + (B.map f).mulVec z) F := by
  rw [eval₂_eq_eval_map, map_affineSlice, eval_affineSlice, ← eval₂_eq_eval_map]

theorem totalDegree_affineSlice_le {R : Type*} [CommRing R] {m n : ℕ}
    (F : MvPolynomial (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    (b : Fin n → R) : (affineSlice F B b).totalDegree ≤ F.totalDegree := by
  apply TranslatedDepthSeven.totalDegree_aeval_le_of_totalDegree_le_one
  intro i
  exact (totalDegree_add _ _).trans
    (max_le (by simp only [totalDegree_C]; omega)
      (homogeneous_linearForms B i).totalDegree_le)

theorem pderiv_affineSlice {R : Type*} [CommRing R] {m n : ℕ}
    (F : MvPolynomial (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    (b : Fin n → R) (j : Fin m) :
    pderiv j (affineSlice F B b) =
      ∑ i, affineSlice (pderiv i F) B b * C (B i j) := by
  simp only [affineSlice]
  rw [pderiv_aeval]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp

/-- The full Hessian of the actual affine slice, at every point. -/
theorem hessian_affineSlice {R : Type*} [CommRing R] {m n : ℕ}
    (F : MvPolynomial (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    (b : Fin n → R) (z : Fin m → R) :
    HessianTheorem11.hessian (affineSlice F B b) z =
      B.transpose * HessianTheorem11.hessian F (b + B.mulVec z) * B := by
  classical
  ext i j
  simp only [HessianTheorem11.hessian, HessianTheorem11.hessianPolynomial,
    pderiv_affineSlice, map_sum, Derivation.leibniz, smul_eq_mul, pderiv_C,
    mul_zero, zero_add, map_mul, eval_C, eval_affineSlice,
    Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem hessian_affineSlice_origin {R : Type*} [CommRing R] {m n : ℕ}
    (F : MvPolynomial (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    (b : Fin n → R) :
    HessianTheorem11.hessian (affineSlice F B b) (0 : Fin m → R) =
      B.transpose * HessianTheorem11.hessian F b * B := by
  simpa only [Matrix.mulVec_zero, add_zero] using hessian_affineSlice F B b 0

end CubicTenVariables.AffinePolynomialSlice
