import CubicTenVariables.FixedLeadingSurfaceNormalizationBlock
import TranslatedDepthSeven.HomogeneousLinearElimination
import TranslatedDepthSeven.FieldPolynomialNatGridInternal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# A fixed integral coordinate choice for a ternary leading form

The matrix with columns `e₁,e₂,(1,a,b)` has determinant one. Nonvanishing
of a homogeneous equation on its first affine chart supplies integer `a,b`
for which its pullback has a nonzero pure last-coordinate coefficient.
The coordinate choice depends only on the fixed leading form.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceCoordinateChoice
open MvPolynomial TranslatedDepthSeven
open scoped BigOperators Matrix

variable {R : Type*} [CommRing R]

def coordinateMatrix (a b : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 1, 0, a; 0, 1, b]

theorem coordinateMatrix_det (a b : R) : (coordinateMatrix a b).det = 1 := by
  simp [coordinateMatrix, Matrix.det_fin_three]

def coordinateForms (a b : R) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![X 2, X 0 + C a * X 2, X 1 + C b * X 2]

def inverseForms (a b : R) : Fin 3 → MvPolynomial (Fin 3) R :=
  ![X 1 - C a * X 0, X 2 - C b * X 0, X 0]

/-- Literal polynomial substitution with an integral polynomial inverse. -/
def coordinateEquiv (a b : R) :
    MvPolynomial (Fin 3) R ≃ₐ[R] MvPolynomial (Fin 3) R :=
  AlgEquiv.ofAlgHom (aeval (coordinateForms a b)) (aeval (inverseForms a b))
    (by ext i; fin_cases i <;> simp [coordinateForms, inverseForms])
    (by ext i; fin_cases i <;> simp [coordinateForms, inverseForms])

theorem coordinateEquiv_apply (a b : R) (f : MvPolynomial (Fin 3) R) :
    coordinateEquiv a b f = aeval (coordinateForms a b) f := rfl

theorem coordinateForms_isHomogeneous (a b : R) (i : Fin 3) :
    (coordinateForms a b i).IsHomogeneous 1 := by
  fin_cases i
  · exact isHomogeneous_X _ _
  · exact (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)
  · exact (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)

theorem coordinateEquiv_isHomogeneous (a b : R)
    {d : ℕ} {f : MvPolynomial (Fin 3) R} (hf : f.IsHomogeneous d) :
    (coordinateEquiv a b f).IsHomogeneous d := by
  simpa only [coordinateEquiv_apply, one_mul] using
    hf.aeval (coordinateForms a b) (coordinateForms_isHomogeneous a b)

theorem eval_coordinateEquiv (a b : R) (y : Fin 3 → R)
    (f : MvPolynomial (Fin 3) R) :
    eval y (coordinateEquiv a b f) = eval ((coordinateMatrix a b).mulVec y) f := by
  have he : (eval y).comp (aeval (coordinateForms a b)).toRingHom =
      eval ((coordinateMatrix a b).mulVec y) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i <;> simp [coordinateForms, coordinateMatrix,
        dotProduct, Fin.sum_univ_three]
  exact RingHom.congr_fun he f

/-- On a homogeneous ternary form, evaluation at the last coordinate
point reads precisely its pure last-power coefficient. -/
theorem eval_last_eq_pure_power_coeff {d : ℕ} (f : MvPolynomial (Fin 3) R)
    (hf : f.IsHomogeneous d) :
    eval (![0, 0, 1] : Fin 3 → R) f = f.coeff (Finsupp.single 2 d) := by
  classical
  rw [MvPolynomial.eval_eq]
  rw [Finset.sum_eq_single (Finsupp.single 2 d)]
  · change f.coeff (Finsupp.single 2 d) *
      (Finsupp.single (2 : Fin 3) d).prod (fun i e => (![0, 0, 1] : Fin 3 → R) i ^ e) = _
    simp
  · intro m hm hne
    by_cases h0 : m 0 = 0
    · by_cases h1 : m 1 = 0
      · exfalso
        apply hne
        have hdeg : m.degree = d := by
          simpa only [Finsupp.degree_eq_weight_one] using hf (mem_support_iff.mp hm)
        have h2 : m 2 = d := by
          simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype, Fin.sum_univ_three,
            h0, h1] using hdeg
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      · change f.coeff m * m.prod (fun i e => (![0, 0, 1] : Fin 3 → R) i ^ e) = 0
        rw [Finsupp.prod_fintype]
        · simp [Fin.prod_univ_three, h1]
        · intro i
          simp
    · change f.coeff m * m.prod (fun i e => (![0, 0, 1] : Fin 3 → R) i ^ e) = 0
      rw [Finsupp.prod_fintype]
      · simp [Fin.prod_univ_three, h0]
      · intro i
        simp
  · intro hm
    simp [notMem_support_iff.mp hm]

/-- The coefficient selected by the coordinate change is evaluation at
the actual primitive integral vector `(1,a,b)`. -/
theorem pure_power_coeff_coordinateEquiv (a b : R) {d : ℕ}
    (f : MvPolynomial (Fin 3) R) (hf : f.IsHomogeneous d) :
    (coordinateEquiv a b f).coeff (Finsupp.single 2 d) = eval ![1, a, b] f := by
  rw [← eval_last_eq_pure_power_coeff _ (coordinateEquiv_isHomogeneous a b hf),
    eval_coordinateEquiv]
  apply congrArg (fun y : Fin 3 → R => eval y f)
  ext i
  fin_cases i <;> simp [coordinateMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

/-- A nonzero homogeneous integral form is nonzero at an integer point
of the fixed chart `X₀=1`. -/
theorem exists_integral_first_chart_eval_ne_zero
    (f : MvPolynomial (Fin 3) ℤ) {d : ℕ}
    (hf : f.IsHomogeneous d) (hne : f ≠ 0) :
    ∃ a b : ℤ, eval ![1, a, b] f ≠ 0 := by
  classical
  let fq := map (Int.castRingHom ℚ) f
  let fo := rename (_root_.finSuccEquiv 2) fq
  have hfq : fq ≠ 0 := fun hz => hne
    (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
      (by simpa only [map_zero] using hz))
  have hfo : fo ≠ 0 := fun hz => hfq
    (rename_injective _ (_root_.finSuccEquiv 2).injective
      (by simpa only [map_zero] using hz))
  have hfqhom : fq.IsHomogeneous d := hf.map (Int.castRingHom ℚ)
  have hfohom : fo.IsHomogeneous d := hfqhom.rename_isHomogeneous
  have hdehom : multivariateDehomogenization fo ≠ 0 :=
    multivariateDehomogenization_ne_zero_of_isHomogeneous fo d hfohom hfo
  obtain ⟨x, _hbound, hx⟩ := exists_nonzero_eval_on_boundedNatGrid_over_field
    (multivariateDehomogenization fo) hdehom (le_refl _)
  have hx' : eval (![1, (x 0 : ℚ), (x 1 : ℚ)] : Fin 3 → ℚ) fq ≠ 0 := by
    rw [eval_multivariateDehomogenization] at hx
    dsimp only [fo] at hx
    rw [eval_rename] at hx
    have hpoint : (affineChartVector (fun i => (x i : ℚ))) ∘
        (_root_.finSuccEquiv 2) = (![1, (x 0 : ℚ), (x 1 : ℚ)] : Fin 3 → ℚ) := by
      ext i
      fin_cases i <;> rfl
    simpa only [hpoint] using hx
  refine ⟨(x 0 : ℤ), (x 1 : ℤ), ?_⟩
  intro hz
  apply hx'
  have he := MvPolynomial.map_eval (Int.castRingHom ℚ)
    (![1, (x 0 : ℤ), (x 1 : ℤ)] : Fin 3 → ℤ) f
  rw [hz, map_zero] at he
  have hp : ((fun z : ℤ => (z : ℚ)) ∘ ![1, (x 0 : ℤ), (x 1 : ℤ)]) =
      (![1, (x 0 : ℚ), (x 1 : ℚ)] : Fin 3 → ℚ) := by
    ext i
    fin_cases i <;> simp
  simpa [fq, hp] using he.symm

/-- A single determinant-one integral coordinate change supplies the
pure-power hypothesis for every subsequent scalar/lower-term family. -/
theorem exists_fixed_integral_pure_power_coordinate
    (f : MvPolynomial (Fin 3) ℤ) {d : ℕ}
    (hf : f.IsHomogeneous d) (hne : f ≠ 0) :
    ∃ a b : ℤ, (coordinateMatrix a b).det = 1 ∧
      (coordinateEquiv a b f).IsHomogeneous d ∧
      (coordinateEquiv a b f).coeff (Finsupp.single 2 d) ≠ 0 := by
  obtain ⟨a, b, hab⟩ := exists_integral_first_chart_eval_ne_zero f hf hne
  exact ⟨a, b, coordinateMatrix_det a b, coordinateEquiv_isHomogeneous a b hf,
    by simpa only [pure_power_coeff_coordinateEquiv a b f hf] using hab⟩

end CubicTenVariables.FixedLeadingSurfaceCoordinateChoice
