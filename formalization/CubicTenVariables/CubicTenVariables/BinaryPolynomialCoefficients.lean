import CubicTenVariables.BinaryCubicPerturbation

/-!
# Coefficients of actual binary polynomials of degree at most three

The coefficient model for binary quadratic lifting is obtained from an actual
integral polynomial, using its six lower coefficients and its four cubic
coefficients divided by the chosen integer. The degree hypotheses and the
Hessian determinant refer to the actual polynomial.
-/

noncomputable section
namespace CubicTenVariables.BinaryCubicPerturbation
open MvPolynomial

def binaryExponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem binaryExponent_zero (a b : ℕ) : binaryExponent a b 0 = a := by
  simp [binaryExponent]

@[simp] theorem binaryExponent_one (a b : ℕ) : binaryExponent a b 1 = b := by
  simp [binaryExponent]

@[simp] theorem binaryExponent_eq_iff (a b c d : ℕ) :
    binaryExponent a b = binaryExponent c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun s => s 0) h,
      by simpa using congrArg (fun s => s 1) h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem binaryExponent_eta (d : Fin 2 →₀ ℕ) : binaryExponent (d 0) (d 1) = d := by
  ext i
  fin_cases i <;> simp

theorem binaryExponent_sum (d : Fin 2 →₀ ℕ) :
    ∑ i ∈ d.support, d i = d 0 + d 1 := by
  change d.sum (fun _ e => e) = _
  rw [Finsupp.sum_fintype]
  · exact Fin.sum_univ_two _
  · intro i
    rfl

theorem monomial_binaryExponent (a b : ℕ) (c : ℤ) :
    monomial (binaryExponent a b) c =
      (C c * X 0^a * X 1^b : MvPolynomial (Fin 2) ℤ) := by
  simp only [X_pow_eq_monomial, C_mul_monomial, monomial_mul, mul_one,
    binaryExponent]

/-- The ten possible monomials are exhaustive for an actual binary cubic. -/
theorem eq_binary_cubic_expansion (F : MvPolynomial (Fin 2) ℤ)
    (hF : F.totalDegree ≤ 3) :
    F = monomial (binaryExponent 0 0) (coeff (binaryExponent 0 0) F) +
      monomial (binaryExponent 1 0) (coeff (binaryExponent 1 0) F) +
      monomial (binaryExponent 0 1) (coeff (binaryExponent 0 1) F) +
      monomial (binaryExponent 2 0) (coeff (binaryExponent 2 0) F) +
      monomial (binaryExponent 1 1) (coeff (binaryExponent 1 1) F) +
      monomial (binaryExponent 0 2) (coeff (binaryExponent 0 2) F) +
      monomial (binaryExponent 3 0) (coeff (binaryExponent 3 0) F) +
      monomial (binaryExponent 2 1) (coeff (binaryExponent 2 1) F) +
      monomial (binaryExponent 1 2) (coeff (binaryExponent 1 2) F) +
      monomial (binaryExponent 0 3) (coeff (binaryExponent 0 3) F) := by
  classical
  ext d
  obtain ⟨a,b,hd⟩ : ∃ a b, d = binaryExponent a b :=
    ⟨d 0,d 1,(binaryExponent_eta d).symm⟩
  subst d
  by_cases hab : a+b ≤ 3
  · have ha : a ≤ 3 := by omega
    have hb : b ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;>
      norm_num [coeff_add, coeff_monomial, binaryExponent_eq_iff] at *
  · have hz : coeff (binaryExponent a b) F = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      rw [binaryExponent_sum, binaryExponent_zero, binaryExponent_one]
      omega
    have hne (i j : ℕ) (hij : i+j ≤ 3) :
        binaryExponent i j ≠ binaryExponent a b := by
      rw [ne_eq, binaryExponent_eq_iff]
      omega
    simp only [coeff_add, coeff_monomial, hz,
      if_neg (hne 0 0 (by omega)), if_neg (hne 1 0 (by omega)),
      if_neg (hne 0 1 (by omega)), if_neg (hne 2 0 (by omega)),
      if_neg (hne 1 1 (by omega)), if_neg (hne 0 2 (by omega)),
      if_neg (hne 3 0 (by omega)), if_neg (hne 2 1 (by omega)),
      if_neg (hne 1 2 (by omega)), if_neg (hne 0 3 (by omega)), add_zero]

/-- The six lower coefficients are unchanged; only the four cubic
coefficients are divided by the chosen integer. -/
def coefficientsOfPolynomial (F : MvPolynomial (Fin 2) ℤ) (p : ℤ) : Coefficients where
  c := coeff (binaryExponent 0 0) F
  lx := coeff (binaryExponent 1 0) F
  ly := coeff (binaryExponent 0 1) F
  qx := coeff (binaryExponent 2 0) F
  qxy := coeff (binaryExponent 1 1) F
  qy := coeff (binaryExponent 0 2) F
  cx := coeff (binaryExponent 3 0) F / p
  cxxy := coeff (binaryExponent 2 1) F / p
  cxyy := coeff (binaryExponent 1 2) F / p
  cy := coeff (binaryExponent 0 3) F / p

/-- Literal polynomial equality, including all lower-degree terms. -/
theorem eq_polynomial_coefficientsOfPolynomial_of_cubic_dvd
    (F : MvPolynomial (Fin 2) ℤ) (p : ℤ) (hF : F.totalDegree ≤ 3)
    (hdiv : ∀ d : Fin 2 →₀ ℕ, d 0 + d 1 = 3 → p ∣ coeff d F) :
    F = polynomial (coefficientsOfPolynomial F p) p := by
  have hdiv' (a b : ℕ) (hab : a+b=3) :
      (C p : MvPolynomial (Fin 2) ℤ) * C (coeff (binaryExponent a b) F / p) =
        C (coeff (binaryExponent a b) F) := by
    rw [← map_mul]
    congr 1
    exact Int.mul_ediv_cancel' (hdiv _ (by simpa using hab))
  have h30 := hdiv' 3 0 rfl
  have h21 := hdiv' 2 1 rfl
  have h12 := hdiv' 1 2 rfl
  have h03 := hdiv' 0 3 rfl
  calc
    F = _ := eq_binary_cubic_expansion F hF
    _ = polynomial (coefficientsOfPolynomial F p) p := by
      simp only [monomial_binaryExponent, pow_zero, pow_one, mul_one]
      unfold polynomial coefficientsOfPolynomial
      linear_combination -(X 0)^3*h30 - (X 0)^2*X 1*h21 -
        X 0*(X 1)^2*h12 - (X 1)^3*h03

/-- A degree-at-most-two reduction forces every cubic coefficient to be
divisible by the modulus. Primality is not needed for this algebraic fact. -/
theorem cubic_coeff_dvd_of_reduction_degree_le_two
    (F : MvPolynomial (Fin 2) ℤ) (p : ℕ)
    (hred : (map (Int.castRingHom (ZMod p)) F).totalDegree ≤ 2)
    (d : Fin 2 →₀ ℕ) (hd : d 0 + d 1 = 3) :
    (p : ℤ) ∣ coeff d F := by
  have hz : coeff d (map (Int.castRingHom (ZMod p)) F) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    rw [binaryExponent_sum, hd]
    omega
  have hc : ((coeff d F : ℤ) : ZMod p) = 0 := by simpa only [coeff_map] using hz
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

/-- Preferred representation criterion for actual binary slices. -/
theorem eq_polynomial_coefficientsOfPolynomial_of_reduction_degree_le_two
    (F : MvPolynomial (Fin 2) ℤ) (p : ℕ) (hF : F.totalDegree ≤ 3)
    (hred : (map (Int.castRingHom (ZMod p)) F).totalDegree ≤ 2) :
    F = polynomial (coefficientsOfPolynomial F (p : ℤ)) (p : ℤ) :=
  eq_polynomial_coefficientsOfPolynomial_of_cubic_dvd F (p : ℤ) hF
    (cubic_coeff_dvd_of_reduction_degree_le_two F p hred)

/-- The determinant is that of the actual evaluated second derivatives,
with no factor of two omitted from the diagonal entries. -/
theorem hessian_polynomial_origin (G : Coefficients) (p : ℤ) :
    HessianTheorem11.hessian (polynomial G p) (0 : Fin 2 → ℤ) =
      !![2*G.qx, G.qxy; G.qxy, 2*G.qy] := by
  have hc2 : constantCoeff (2 : MvPolynomial (Fin 2) ℤ) = 2 :=
    map_ofNat constantCoeff 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HessianTheorem11.hessian, HessianTheorem11.hessianPolynomial,
      polynomial, hc2] <;> ring

theorem det_hessian_polynomial_origin (G : Coefficients) (p : ℤ) :
    (HessianTheorem11.hessian (polynomial G p) (0 : Fin 2 → ℤ)).det =
      discriminant G := by
  rw [hessian_polynomial_origin, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    discriminant]
  ring

/-- Evaluating the actual Hessian at the origin commutes with reduction. -/
theorem hessian_reduction_origin (F : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    HessianTheorem11.hessian (map (Int.castRingHom (ZMod p)) F)
      (0 : Fin 2 → ZMod p) =
    (HessianTheorem11.hessian F (0 : Fin 2 → ℤ)).map (fun z => (z : ZMod p)) := by
  ext i j
  simp only [HessianTheorem11.hessian, HessianTheorem11.hessianPolynomial,
    pderiv_map, Matrix.map_apply, eval_zero, constantCoeff_eq,
    coeff_map, Int.coe_castRingHom]

theorem det_hessian_reduction_origin (F : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    (HessianTheorem11.hessian (map (Int.castRingHom (ZMod p)) F)
      (0 : Fin 2 → ZMod p)).det =
      ((HessianTheorem11.hessian F (0 : Fin 2 → ℤ)).det : ZMod p) := by
  rw [hessian_reduction_origin, Int.cast_det]

/-- Every actual cubic with quadratic reduction has the coefficient model,
and its model discriminant equals its actual integral Hessian determinant. -/
theorem exists_polynomial_representation_of_reduction_degree_le_two
    (F : MvPolynomial (Fin 2) ℤ) (p : ℕ) (hF : F.totalDegree ≤ 3)
    (hred : (map (Int.castRingHom (ZMod p)) F).totalDegree ≤ 2) :
    ∃ G : Coefficients, F = polynomial G (p : ℤ) ∧
      discriminant G = (HessianTheorem11.hessian F (0 : Fin 2 → ℤ)).det := by
  refine ⟨coefficientsOfPolynomial F (p : ℤ),
    eq_polynomial_coefficientsOfPolynomial_of_reduction_degree_le_two F p hF hred, ?_⟩
  have heq := eq_polynomial_coefficientsOfPolynomial_of_reduction_degree_le_two F p hF hred
  exact (det_hessian_polynomial_origin _ _).symm.trans
    (congrArg (fun Q => (HessianTheorem11.hessian Q (0 : Fin 2 → ℤ)).det) heq.symm)

/-- A nonzero determinant of the actual reduced Hessian supplies exactly
the nondegeneracy assumption of the binary coefficient model. -/
theorem exists_nondegenerate_polynomial_representation
    (F : MvPolynomial (Fin 2) ℤ) (p : ℕ) (hF : F.totalDegree ≤ 3)
    (hred : (map (Int.castRingHom (ZMod p)) F).totalDegree ≤ 2)
    (hD : (HessianTheorem11.hessian (map (Int.castRingHom (ZMod p)) F)
      (0 : Fin 2 → ZMod p)).det ≠ 0) :
    ∃ G : Coefficients, F = polynomial G (p : ℤ) ∧
      (discriminant G : ZMod p) ≠ 0 := by
  obtain ⟨G,hG,hdisc⟩ := exists_polynomial_representation_of_reduction_degree_le_two F p hF hred
  refine ⟨G,hG,?_⟩
  rwa [hdisc, ← det_hessian_reduction_origin]

end CubicTenVariables.BinaryCubicPerturbation
