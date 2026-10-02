import CubicTenVariables.Denominators
import HessianTheorem11.HessianLinearity

/-! Integral symmetric tensor coordinates for arbitrary integer cubics.
The third partial derivatives give a literal ordered-triple presentation of
six times the original cubic, without division in the integer coefficient
ring. The tensor matrix is exactly the original cubic's Hessian. -/

noncomputable section
namespace CubicTenVariables
open MvPolynomial HessianTheorem11

/-- Bernert's integral, fully symmetric ordered-triple coefficient array.
The two adjacent transpositions generate every permutation of three slots. -/
structure SymmetricIntegerCubicTensor (n : ℕ) where
  coeff : Fin n → Fin n → Fin n → ℤ
  swap_first : ∀ i j k, coeff i j k = coeff j i k
  swap_last : ∀ i j k, coeff i j k = coeff i k j

namespace SymmetricIntegerCubicTensor
variable {n : ℕ}

/-- The actual cubic with the sum taken over all ordered triples. -/
def polynomial (T : SymmetricIntegerCubicTensor n) : MvPolynomial (Fin n) ℤ :=
  ∑ i, ∑ j, ∑ k, C (T.coeff i j k) * X i * X j * X k

/-- Bernert's integral matrix M(x), before taking its rank over ℚ. -/
def matrix (T : SymmetricIntegerCubicTensor n) (x : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℤ := fun j k => ∑ i, T.coeff i j k * x i

theorem cyclic (T : SymmetricIntegerCubicTensor n) (i j k : Fin n) :
    T.coeff i j k = T.coeff j k i :=
  (T.swap_first i j k).trans (T.swap_last j i k)

theorem reverse (T : SymmetricIntegerCubicTensor n) (i j k : Fin n) :
    T.coeff i j k = T.coeff k j i :=
  (T.swap_last i j k).trans ((T.swap_first i k j).trans (T.swap_last k i j))

theorem polynomial_homogeneous (T : SymmetricIntegerCubicTensor n) :
    T.polynomial.IsHomogeneous 3 := by
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  apply IsHomogeneous.sum
  intro k _
  exact (((isHomogeneous_C _ _).mul (isHomogeneous_X _ i)).mul
    (isHomogeneous_X _ j)).mul (isHomogeneous_X _ k)

theorem matrix_symmetric (T : SymmetricIntegerCubicTensor n) (x : Fin n → ℤ) :
    (T.matrix x).transpose = T.matrix x := by
  ext j k
  change (∑ i, T.coeff i k j * x i) = ∑ i, T.coeff i j k * x i
  apply Finset.sum_congr rfl
  intro i _
  rw [T.swap_last i k j]

end SymmetricIntegerCubicTensor

/-- The integral third-derivative tensor; its symmetry holds for every
polynomial, while the presentation theorem below uses cubic homogeneity. -/
def symmetricTensorOfCubic {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    SymmetricIntegerCubicTensor n where
  coeff i j k := coeff 0 (pderiv k (pderiv j (pderiv i F)))
  swap_first i j k := by rw [partials_commute F j i]
  swap_last i j k := by rw [partials_commute (pderiv i F) k j]

/-- Euler's identities in degrees three, two and one show that the ordered
sum of the integral symmetric coefficients represents exactly 6F. -/
theorem symmetricTensorOfCubic_polynomial {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) :
    (symmetricTensorOfCubic F).polynomial = C 6 * F := by
  classical
  calc
    (symmetricTensorOfCubic F).polynomial =
        ∑ i, X i * (∑ j, X j * pderiv j (pderiv i F)) := by
      unfold SymmetricIntegerCubicTensor.polynomial
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have he : pderiv j (pderiv i F) =
          ∑ k, X k * C (coeff 0 (pderiv k (pderiv j (pderiv i F)))) :=
        homogeneous_one_expansion hF.pderiv.pderiv
      rw [he, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [symmetricTensorOfCubic]
      ring
    _ = ∑ i, X i * (2 • pderiv i F) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hF.pderiv.sum_X_mul_pderiv]
    _ = 2 * ∑ i, X i * pderiv i F := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [nsmul_eq_mul]
      ring
    _ = C 6 * F := by
      rw [hF.sum_X_mul_pderiv]
      simp only [nsmul_eq_mul, map_ofNat]
      ring

/-- M(x) of the tensor representing 6F is precisely the Hessian of F,
including the repeated-index coefficients and every integer x. -/
theorem symmetricTensorOfCubic_matrix {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (x : Fin n → ℤ) :
    (symmetricTensorOfCubic F).matrix x = hessian F x := by
  ext j k
  rw [hessian_entry_expansion hF]
  apply Finset.sum_congr rfl
  intro i _
  change (symmetricTensorOfCubic F).coeff i j k * x i =
    x i * (symmetricTensorOfCubic F).coeff j k i
  rw [(symmetricTensorOfCubic F).cyclic]
  ring

/-- Exact coefficient-extension form of the matrix identity used when
Bernert takes the rank of M(x) over the rational field. -/
theorem symmetricTensorOfCubic_matrix_rat {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (x : Fin n → ℤ) :
    (fun j k => (((symmetricTensorOfCubic F).matrix x j k : ℤ) : ℚ)) =
      hessian (map (Int.castRingHom ℚ) F) (fun i => (x i : ℚ)) := by
  rw [symmetricTensorOfCubic_matrix F hF x]
  ext j k
  change (Int.castRingHom ℚ) (eval x (pderiv k (pderiv j F))) =
    eval (fun i => (x i : ℚ)) (pderiv k (pderiv j (map (Int.castRingHom ℚ) F)))
  rw [pderiv_map, pderiv_map]
  exact MvPolynomial.map_eval (Int.castRingHom ℚ) x _

/-- Multiplication by any nonzero integer scalar preserves exactly the
nonzero integer zeros of a polynomial. -/
theorem hasIntegerZero_C_mul_iff {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (c : ℤ) (hc : c ≠ 0) : HasIntegerZero (C c * F) ↔ HasIntegerZero F := by
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨x, hx, ?_⟩
    rw [eval_mul, eval_C] at he
    exact (mul_eq_zero.mp he).resolve_left hc
  · rintro ⟨x, hx, he⟩
    exact ⟨x, hx, by simp [he]⟩

theorem symmetricTensorOfCubic_hasIntegerZero_iff {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) :
    HasIntegerZero (symmetricTensorOfCubic F).polynomial ↔ HasIntegerZero F := by
  rw [symmetricTensorOfCubic_polynomial F hF]
  exact hasIntegerZero_C_mul_iff F 6 (by norm_num)

end CubicTenVariables
