import CubicTenVariables.CubicSingularPointUpgrade
import CubicTenVariables.SingularCubicLinearFibers

/-!
# Eliminate one singular direction without a characteristic restriction

This is the explicit coordinate step in Pleasants's cubic argument.  An
actual nonzero zero, together with absence of nonsingular zeros, gives a
homogeneous cubic in one fewer variable and an exact linear-form pullback.
No local-solubility or finite-field point-existence theorem is assumed.
-/

noncomputable section
namespace CubicTenVariables.CubicSingularVariableElimination
open MvPolynomial HessianTheorem11 PolynomialRestriction SingularCubicLinearFibers
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- Differentiating a literal coordinate section selects the corresponding
original partial, over every field. -/
theorem pderiv_zeroSection (i : Fin (n+1)) (F : MvPolynomial (Fin (n+1)) K)
    (j : Fin n) :
    pderiv j (zeroSection i F) = zeroSection i (pderiv (i.succAbove j) F) := by
  classical
  unfold zeroSection
  rw [pderiv_aeval, Fin.sum_univ_succAbove _ i]
  simp [Pi.single_apply]

/-- A smooth nonzero zero of the coordinate section is a smooth nonzero
zero of the original polynomial. -/
theorem nonsingular_zero_of_zeroSection
    (i : Fin (n+1)) (F : MvPolynomial (Fin (n+1)) K)
    (y : Fin n → K) (hy : y ≠ 0) (hzero : eval y (zeroSection i F) = 0)
    (hsmooth : gradient (zeroSection i F) y ≠ 0) :
    ∃ x : Fin (n+1) → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0 := by
  refine ⟨i.insertNth 0 y, ?_, (eval_section i F y).symm.trans hzero, ?_⟩
  · intro hz
    apply hy
    funext j
    simpa using congrFun hz (i.succAbove j)
  · intro hg
    apply hsmooth
    ext j
    change eval y (pderiv j (zeroSection i F)) = 0
    rw [pderiv_zeroSection, eval_section]
    exact congrFun hg (i.succAbove j)

/-- Coordinates on the hyperplane complementary to a direction with z_i≠0. -/
def projectionMatrix (z : Fin (n+1) → K) (i : Fin (n+1)) :
    Matrix (Fin n) (Fin (n+1)) K := fun j k =>
  (if k = i.succAbove j then 1 else 0) -
    (z (i.succAbove j) / z i) * (if k = i then 1 else 0)

@[simp] theorem linearForms_projectionMatrix
    (z : Fin (n+1) → K) (i : Fin (n+1)) (j : Fin n) :
    linearForms (projectionMatrix z i) j =
      X (i.succAbove j) - C (z (i.succAbove j) / z i) * X i := by
  classical
  unfold linearForms projectionMatrix
  simp only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
  simp only [apply_ite, map_one, map_zero, ite_mul, mul_one,
    mul_zero, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Exact polynomial equality gives a representation in one fewer linear
forms; this is valid also over F2 and F3. -/
theorem eq_linearForms_zeroSection
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (hno : ¬ ∃ x : Fin (n+1) → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0)
    (z : Fin (n+1) → K) (hzero : eval z F = 0) (hsing : gradient F z = 0)
    (i : Fin (n+1)) (hi : z i ≠ 0) :
    F = aeval (linearForms (projectionMatrix z i)) (zeroSection i F) := by
  classical
  let t : MvPolynomial (Fin (n+1)) K := -C ((z i)⁻¹) * X i
  have he := CubicSingularPointUpgrade.polynomial_translate_of_no_nonsingular_zero
    F hF hno z hzero hsing t
  unfold zeroSection
  rw [MvPolynomial.comp_aeval_apply]
  have hc : (fun k => aeval (linearForms (projectionMatrix z i))
      (@Fin.insertNth n (fun _ => MvPolynomial (Fin n) K) i 0 X k)) =
        (fun k => X k + t * C (z k)) := by
    funext k
    induction k using i.succAboveCases
    · simp only [Fin.insertNth_apply_same, map_zero]
      dsimp [t]
      have hmul : C ((z i)⁻¹) * C (z i) = (1 : MvPolynomial (Fin (n+1)) K) := by
        rw [← map_mul, inv_mul_cancel₀ hi, map_one]
      calc
        0 = X i - (C ((z i)⁻¹) * C (z i)) * X i := by rw [hmul]; ring
        _ = X i + (-C ((z i)⁻¹) * X i) * C (z i) := by ring
    · simp only [Fin.insertNth_apply_succAbove, aeval_X, linearForms_projectionMatrix]
      dsimp [t]
      rw [div_eq_mul_inv, map_mul]
      ring
  rw [hc]
  exact he.symm

/-- A supplied nonzero zero, if no smooth zero exists, removes one variable
while preserving the absence of smooth zeros for the remaining cubic. -/
theorem exists_one_fewer_variables
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous 3)
    (hno : ¬ ∃ x : Fin (n+1) → K, x ≠ 0 ∧ eval x F = 0 ∧ gradient F x ≠ 0)
    (z : Fin (n+1) → K) (hz : z ≠ 0) (hzero : eval z F = 0) :
    ∃ (A : Matrix (Fin n) (Fin (n+1)) K) (G : MvPolynomial (Fin n) K),
      G.IsHomogeneous 3 ∧ F = aeval (linearForms A) G ∧
        ¬ ∃ y : Fin n → K, y ≠ 0 ∧ eval y G = 0 ∧ gradient G y ≠ 0 := by
  classical
  have hsing : gradient F z = 0 := by
    by_contra hs
    exact hno ⟨z, hz, hzero, hs⟩
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  refine ⟨projectionMatrix z i, zeroSection i F, homogeneous_section i F hF,
    eq_linearForms_zeroSection F hF hno z hzero hsing i hi, ?_⟩
  rintro ⟨y, hy, hGy, hgrad⟩
  exact hno (nonsingular_zero_of_zeroSection i F y hy hGy hgrad)

end CubicTenVariables.CubicSingularVariableElimination
