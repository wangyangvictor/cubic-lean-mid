import CubicTenVariables.CubicSquarefreeSurfaceSingular
import CubicTenVariables.PlaneCubicSingularGeometry

/-! The literal squarefree form obtained from four coordinate singular zeros.
This is a finite coefficient calculation, not a classification premise. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace CubicTenVariables.CubicFourSingularCoordinates
open MvPolynomial HessianTheorem11 CubicSquarefreeSurfaceSingular
open scoped BigOperators
variable {R : Type*} [CommRing R]

private def coordinatePoint (i : Fin 4) : Fin 4 → R := Pi.single i 1

def squarefreeCoefficients (F : MvPolynomial (Fin 4) R) : Fin 4 → R :=
  ![coeff (Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1) F,
    coeff (Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 3 1) F,
    coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1) F,
    coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) F]

private def reconstruction (F : MvPolynomial (Fin 4) R) : MvPolynomial (Fin 4) R :=
  (∑ i : Fin 4, C (eval (coordinatePoint i) F) * X i ^ 3) +
    (∑ i : Fin 4, ∑ j : Fin 4, if i = j then 0 else
      C (eval (coordinatePoint i) (pderiv j F)) * X i ^ 2 * X j) +
    polynomial (squarefreeCoefficients F)

private theorem reconstruction_add (F G : MvPolynomial (Fin 4) R) :
    reconstruction (F+G) = reconstruction F + reconstruction G := by
  simp [reconstruction, squarefreeCoefficients, polynomial, Fin.sum_univ_succ,
    add_mul]
  ring

private theorem degree_three_decomposition (d : Fin 4 →₀ ℕ) (hd : d.degree = 3) :
    ∃ i j k, d = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 := by
  have step (e : Fin 4 →₀ ℕ) (r : ℕ) (he : e.degree = r+1) :
      ∃ i f, e = Finsupp.single i 1 + f ∧ f.degree = r := by
    obtain ⟨i,hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra! hz
      have hz' : e = 0 := Finsupp.ext hz
      simp [hz'] at he
    obtain ⟨f,hf⟩ := exists_add_of_le
      (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))
    refine ⟨i,f,hf,?_⟩
    rw [hf,map_add,Finsupp.degree_single] at he
    omega
  obtain ⟨i,e,rfl,he⟩ := step d 2 hd
  obtain ⟨j,f,rfl,hf⟩ := step e 1 he
  obtain ⟨k,rfl⟩ := Finsupp.range_single_one.symm.subset hf
  exact ⟨i,j,k,(add_assoc _ _ _).symm⟩

private theorem coeff_triple (d : Fin 4 →₀ ℕ) (c : R) (i j k : Fin 4) :
    coeff d (C c * X i * X j * X k) =
      if Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 = d
      then c else 0 := by
  simp only [X,C_apply,monomial_mul,zero_add,mul_one,coeff_monomial]

private theorem exponent_eq_iff (a b : Fin 4 →₀ ℕ) :
    a = b ↔ a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 ∧ a 3 = b 3 := by
  simp [Finsupp.ext_iff,Fin.forall_fin_succ]

private theorem reconstruction_eq (F : MvPolynomial (Fin 4) R)
    (hF : F.IsHomogeneous 3) : reconstruction F = F := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simp [reconstruction,squarefreeCoefficients,polynomial]
  | add F G _ _ hF hG => rw [reconstruction_add,hF,hG]
  | monomial d c hd =>
    have hd' : d.degree = 3 := by simpa [Finsupp.degree_eq_weight_one] using hd
    obtain ⟨i,j,k,rfl⟩ := degree_three_decomposition d hd'
    have hm : monomial (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1) c =
        C c * X i * X j * X k := by
      simp only [X,C_apply,monomial_mul,zero_add,mul_one]
    rw [hm]
    fin_cases i <;> fin_cases j <;> fin_cases k
    · change reconstruction (C c * X 0 * X 0 * X 0) = C c * X 0 * X 0 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 0 * X 1) = C c * X 0 * X 0 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 0 * X 2) = C c * X 0 * X 0 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 0 * X 3) = C c * X 0 * X 0 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 1 * X 0) = C c * X 0 * X 1 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 1 * X 1) = C c * X 0 * X 1 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 1 * X 2) = C c * X 0 * X 1 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 1 * X 3) = C c * X 0 * X 1 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 2 * X 0) = C c * X 0 * X 2 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 2 * X 1) = C c * X 0 * X 2 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 2 * X 2) = C c * X 0 * X 2 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 2 * X 3) = C c * X 0 * X 2 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 3 * X 0) = C c * X 0 * X 3 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 3 * X 1) = C c * X 0 * X 3 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 3 * X 2) = C c * X 0 * X 3 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 0 * X 3 * X 3) = C c * X 0 * X 3 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 0 * X 0) = C c * X 1 * X 0 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 0 * X 1) = C c * X 1 * X 0 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 0 * X 2) = C c * X 1 * X 0 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 0 * X 3) = C c * X 1 * X 0 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 1 * X 0) = C c * X 1 * X 1 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 1 * X 1) = C c * X 1 * X 1 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 1 * X 2) = C c * X 1 * X 1 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 1 * X 3) = C c * X 1 * X 1 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 2 * X 0) = C c * X 1 * X 2 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 2 * X 1) = C c * X 1 * X 2 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 2 * X 2) = C c * X 1 * X 2 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 2 * X 3) = C c * X 1 * X 2 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 3 * X 0) = C c * X 1 * X 3 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 3 * X 1) = C c * X 1 * X 3 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 3 * X 2) = C c * X 1 * X 3 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 1 * X 3 * X 3) = C c * X 1 * X 3 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 0 * X 0) = C c * X 2 * X 0 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 0 * X 1) = C c * X 2 * X 0 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 0 * X 2) = C c * X 2 * X 0 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 0 * X 3) = C c * X 2 * X 0 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 1 * X 0) = C c * X 2 * X 1 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 1 * X 1) = C c * X 2 * X 1 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 1 * X 2) = C c * X 2 * X 1 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 1 * X 3) = C c * X 2 * X 1 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 2 * X 0) = C c * X 2 * X 2 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 2 * X 1) = C c * X 2 * X 2 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 2 * X 2) = C c * X 2 * X 2 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 2 * X 3) = C c * X 2 * X 2 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 3 * X 0) = C c * X 2 * X 3 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 3 * X 1) = C c * X 2 * X 3 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 3 * X 2) = C c * X 2 * X 3 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 2 * X 3 * X 3) = C c * X 2 * X 3 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 0 * X 0) = C c * X 3 * X 0 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 0 * X 1) = C c * X 3 * X 0 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 0 * X 2) = C c * X 3 * X 0 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 0 * X 3) = C c * X 3 * X 0 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 1 * X 0) = C c * X 3 * X 1 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 1 * X 1) = C c * X 3 * X 1 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 1 * X 2) = C c * X 3 * X 1 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 1 * X 3) = C c * X 3 * X 1 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 2 * X 0) = C c * X 3 * X 2 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 2 * X 1) = C c * X 3 * X 2 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 2 * X 2) = C c * X 3 * X 2 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 2 * X 3) = C c * X 3 * X 2 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 3 * X 0) = C c * X 3 * X 3 * X 0
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 3 * X 1) = C c * X 3 * X 3 * X 1
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 3 * X 2) = C c * X 3 * X 3 * X 2
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring
    · change reconstruction (C c * X 3 * X 3 * X 3) = C c * X 3 * X 3 * X 3
      simp only [reconstruction,squarefreeCoefficients,polynomial,Fin.sum_univ_succ]
      simp only [coeff_triple]
      simp [coordinatePoint,Derivation.leibniz,exponent_eq_iff] <;> ring

/-- Four actual coordinate singular zeros eliminate every nonsquarefree
cubic monomial, in every characteristic. -/
theorem eq_squarefree_of_coordinate_singular
    (F : MvPolynomial (Fin 4) R) (hF : F.IsHomogeneous 3)
    (hzero : ∀ i : Fin 4, eval (Pi.single i 1) F = 0)
    (hsing : ∀ i j : Fin 4, eval (Pi.single i 1) (pderiv j F) = 0) :
    F = polynomial (squarefreeCoefficients F) := by
  have he := reconstruction_eq F hF
  simpa only [reconstruction,coordinatePoint,hzero,hsing,map_zero,zero_mul,
    ite_self,Finset.sum_const_zero,zero_add] using he.symm


/-- The same form for an actual linear-coordinate restriction.  The columns
need not be independent for this polynomial identity. -/
theorem restrict_eq_squarefree_of_singular_columns {n : ℕ}
    (B : Matrix (Fin n) (Fin 4) R) (F : MvPolynomial (Fin n) R)
    (hF : F.IsHomogeneous 3)
    (hzero : ∀ i : Fin 4, eval (B.mulVec (Pi.single i 1)) F = 0)
    (hsing : ∀ (i : Fin 4) (j : Fin n),
      eval (B.mulVec (Pi.single i 1)) (pderiv j F) = 0) :
    PolynomialRestriction.restrict B F =
      polynomial (squarefreeCoefficients (PolynomialRestriction.restrict B F)) := by
  apply eq_squarefree_of_coordinate_singular _
    (PolynomialRestriction.homogeneous_restrict B F hF)
  · intro i
    simpa only [PolynomialRestriction.eval_restrict] using hzero i
  · intro i j
    simp only [PolynomialRestriction.pderiv_restrict,map_sum,map_mul,
      PolynomialRestriction.eval_restrict,hsing,zero_mul,Finset.sum_const_zero]

private theorem coordinate_dvd_of_coefficient_zero (c : Fin 4 → R)
    (i : Fin 4) (hc : c i = 0) : X i ∣ polynomial c := by
  fin_cases i
  · change c 0 = 0 at hc
    change X (0 : Fin 4) ∣ polynomial c
    refine ⟨C (c 1)*X 2*X 3 + C (c 2)*X 1*X 3 + C (c 3)*X 1*X 2, ?_⟩
    simp only [polynomial,hc,map_zero,zero_mul,zero_add]
    ring
  · change c 1 = 0 at hc
    change X (1 : Fin 4) ∣ polynomial c
    refine ⟨C (c 0)*X 2*X 3 + C (c 2)*X 0*X 3 + C (c 3)*X 0*X 2, ?_⟩
    simp only [polynomial,hc,map_zero,zero_mul,add_zero]
    ring
  · change c 2 = 0 at hc
    change X (2 : Fin 4) ∣ polynomial c
    refine ⟨C (c 0)*X 1*X 3 + C (c 1)*X 0*X 3 + C (c 3)*X 0*X 1, ?_⟩
    simp only [polynomial,hc,map_zero,zero_mul,add_zero]
    ring
  · change c 3 = 0 at hc
    change X (3 : Fin 4) ∣ polynomial c
    refine ⟨C (c 0)*X 1*X 2 + C (c 1)*X 0*X 2 + C (c 2)*X 0*X 1, ?_⟩
    simp only [polynomial,hc,map_zero,zero_mul,add_zero]
    ring

/-- Irreducibility forces all four coefficients of the squarefree form
nonzero; a missing coefficient would leave the opposite variable as a factor. -/
theorem coefficients_ne_zero_of_irreducible {K : Type*} [Field K]
    (c : Fin 4 → K) (hc : Irreducible (polynomial c)) : ∀ i, c i ≠ 0 := by
  intro i hi
  have hXi : Irreducible (X i : MvPolynomial (Fin 4) K) :=
    PlaneCubicSingularGeometry.irreducible_of_totalDegree_eq_one _ (totalDegree_X i)
  have hback := hXi.dvd_symm hc (coordinate_dvd_of_coefficient_zero c i hi)
  have hdeg := totalDegree_le_of_dvd_of_isDomain hback (X_ne_zero i)
  have hFdeg := (polynomial_isHomogeneous c).totalDegree hc.ne_zero
  rw [hFdeg,totalDegree_X] at hdeg
  omega

/-- A coordinate singular frame in an irreducible cubic leaves exactly the
four coordinate axes as its affine singular zeros. -/
theorem singular_iff_axis_of_coordinate_frame {K : Type*} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F)
    (hzero : ∀ i : Fin 4, eval (Pi.single i 1) F = 0)
    (hsing : ∀ i j : Fin 4, eval (Pi.single i 1) (pderiv j F) = 0)
    (x : Fin 4 → K) :
    eval x F = 0 ∧ HessianTheorem11.gradient F x = 0 ↔
      ∃ i t, x = Pi.single i t := by
  have he := eq_squarefree_of_coordinate_singular F hF hzero hsing
  have hc := coefficients_ne_zero_of_irreducible (squarefreeCoefficients F) (he ▸ hirr)
  rw [he]
  exact singular_iff_coordinate_axis _ hc x

end CubicTenVariables.CubicFourSingularCoordinates
