import CubicTenVariables.FixedLeadingSurfaceCoordinateChoice
import CubicTenVariables.IntegralFirstCoordinateShear
import TranslatedDepthSeven.HypersurfaceSurfaceResidueDiscFirstChart
import TranslatedDepthSeven.AffineChartPilaComponentCount

/-!
# The fixed leading-form coordinates on actual homogenized equations

The ternary coordinate change is lifted with the first homogeneous variable
fixed. Coefficient extension, homogeneous pieces and fixed-degree
homogenization commute with the literal substitutions. The final statement
supplies exactly the variable-degree premise of the surface packet theorem,
uniformly over all lower coefficients and nonzero rational leading scalars.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceCoordinateTransport
open MvPolynomial TranslatedDepthSeven
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceNormalizationBlock
open scoped BigOperators Matrix

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The affine substitution commutes with every coefficient homomorphism. -/
theorem map_coordinateEquiv (φ : R →+* S) (a b : R)
    (f : MvPolynomial (Fin 3) R) :
    map φ (coordinateEquiv a b f) =
      coordinateEquiv (φ a) (φ b) (map φ f) := by
  have h : (map φ).comp (coordinateEquiv a b).toRingHom =
      (coordinateEquiv (φ a) (φ b)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coordinateEquiv_apply]
    · intro i
      fin_cases i <;> simp [coordinateEquiv_apply,
        FixedLeadingSurfaceCoordinateChoice.coordinateForms]
  exact RingHom.congr_fun h f

/-- Literal homogeneous-coordinate forms; the coordinate X₀ is fixed. -/
def projectiveForms (a b : R) : Fin 4 → MvPolynomial (Fin 4) R :=
  ![X 0, X 3, X 1 + C a * X 3, X 2 + C b * X 3]

def projectiveInverseForms (a b : R) : Fin 4 → MvPolynomial (Fin 4) R :=
  ![X 0, X 2 - C a * X 1, X 3 - C b * X 1, X 1]

def projectiveEquiv (a b : R) :
    MvPolynomial (Fin 4) R ≃ₐ[R] MvPolynomial (Fin 4) R :=
  AlgEquiv.ofAlgHom (aeval (projectiveForms a b))
    (aeval (projectiveInverseForms a b))
    (by ext i; fin_cases i <;> simp [projectiveForms, projectiveInverseForms])
    (by ext i; fin_cases i <;> simp [projectiveForms, projectiveInverseForms])

theorem projectiveEquiv_apply (a b : R) (F : MvPolynomial (Fin 4) R) :
    projectiveEquiv a b F = aeval (projectiveForms a b) F := rfl

@[simp] theorem projectiveEquiv_X_zero (a b : R) :
    projectiveEquiv a b (X 0) = X 0 := by
  simp [projectiveEquiv_apply, projectiveForms]

theorem projectiveForms_isHomogeneous (a b : R) (i : Fin 4) :
    (projectiveForms a b i).IsHomogeneous 1 := by
  fin_cases i
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_X _ _
  · exact (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)
  · exact (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)

theorem projectiveEquiv_isHomogeneous (a b : R)
    {d : ℕ} {F : MvPolynomial (Fin 4) R} (hF : F.IsHomogeneous d) :
    (projectiveEquiv a b F).IsHomogeneous d := by
  simpa only [projectiveEquiv_apply, one_mul] using
    hF.aeval (projectiveForms a b) (projectiveForms_isHomogeneous a b)

theorem map_projectiveEquiv (φ : R →+* S) (a b : R)
    (F : MvPolynomial (Fin 4) R) :
    map φ (projectiveEquiv a b F) =
      projectiveEquiv (φ a) (φ b) (map φ F) := by
  have h : (map φ).comp (projectiveEquiv a b).toRingHom =
      (projectiveEquiv (φ a) (φ b)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [projectiveEquiv_apply]
    · intro i
      fin_cases i <;> simp [projectiveEquiv_apply, projectiveForms]
  exact RingHom.congr_fun h F

theorem projectiveEquiv_rename_succ (a b : R) (f : MvPolynomial (Fin 3) R) :
    projectiveEquiv a b (rename Fin.succ f) =
      rename Fin.succ (coordinateEquiv a b f) := by
  have h : (projectiveEquiv a b).toRingHom.comp (rename Fin.succ).toRingHom =
      (rename Fin.succ).toRingHom.comp (coordinateEquiv a b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [projectiveEquiv_apply, coordinateEquiv_apply]
    · intro i
      fin_cases i <;> simp [projectiveEquiv_apply, coordinateEquiv_apply,
        projectiveForms, FixedLeadingSurfaceCoordinateChoice.coordinateForms]
  exact RingHom.congr_fun h f

/-- Fixed-degree homogenization in `Fin 4`, coordinate zero homogenizing. -/
def homogenize (d : ℕ) (g : MvPolynomial (Fin 3) R) : MvPolynomial (Fin 4) R :=
  ∑ j ∈ Finset.range (d + 1),
    X 0 ^ (d - j) * rename Fin.succ (homogeneousComponent j g)

theorem homogenize_eq_standard (d : ℕ) (g : MvPolynomial (Fin 3) R) :
    homogenize d g = rename (_root_.finSuccEquiv 3).symm
      (multivariateHomogenization g d) := by
  simp only [homogenize, multivariateHomogenization, map_sum, map_mul,
    map_pow, rename_X, rename_rename]
  rfl

theorem homogenize_isHomogeneous (d : ℕ) (g : MvPolynomial (Fin 3) R) :
    (homogenize d g).IsHomogeneous d := by
  rw [homogenize_eq_standard]
  exact (multivariateHomogenization_isHomogeneous g d).rename_isHomogeneous

theorem map_homogenize (φ : R →+* S) (d : ℕ) (g : MvPolynomial (Fin 3) R) :
    map φ (homogenize d g) = homogenize d (map φ g) := by
  simp only [homogenize, map_sum, map_mul, map_pow, map_X,
    map_rename, map_homogeneousComponent_boundary]

/-- The standard affine chart of the literal homogenization recovers g;
the degree condition ensures no terms have been discarded. -/
theorem standardDehomogenizationHom_homogenize (d : ℕ)
    (g : MvPolynomial (Fin 3) R) (hg : g.totalDegree ≤ d) :
    standardDehomogenizationHom R 3 (homogenize d g) = g := by
  have hr (f : MvPolynomial (Fin 3) R) :
      standardDehomogenizationHom R 3 (rename Fin.succ f) = f := by
    have he : (standardDehomogenizationHom R 3).comp
        (rename Fin.succ).toRingHom = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [standardDehomogenizationHom]
      · intro i
        simp [standardDehomogenizationHom]
    exact RingHom.congr_fun he f
  have hX : standardDehomogenizationHom R 3 (X 0) = 1 := by
    simp [standardDehomogenizationHom]
  simp only [homogenize, map_sum, map_mul, map_pow, hX, hr, one_pow, one_mul]
  exact sum_homogeneousComponent_up_to g d hg

/-- Literal restriction to the hyperplane at infinity. -/
def boundaryHom (R : Type*) [CommRing R] :
    MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 3) R :=
  eval₂Hom C (Fin.cases 0 X)

theorem boundaryHom_rename_succ (g : MvPolynomial (Fin 3) R) :
    boundaryHom R (rename Fin.succ g) = g := by
  have he : (boundaryHom R).comp (rename Fin.succ).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [boundaryHom]
    · intro i
      simp [boundaryHom]
  exact RingHom.congr_fun he g

/-- The boundary of a fixed-degree homogenization is exactly its degree-d
component, over every commutative coefficient ring. -/
theorem boundaryHom_homogenize (d : ℕ) (g : MvPolynomial (Fin 3) R) :
    boundaryHom R (homogenize d g) = homogeneousComponent d g := by
  have hX : boundaryHom R (X 0) = 0 := by simp [boundaryHom]
  simp only [homogenize, map_sum, map_mul, map_pow, hX, boundaryHom_rename_succ]
  rw [Finset.sum_eq_single d]
  · simp
  · intro j hj hne
    have hjd : j < d := by have := Finset.mem_range.mp hj; omega
    rw [zero_pow (Nat.sub_ne_zero_of_lt hjd), zero_mul]
  · simp

section Field
variable {K : Type*} [Field K]

theorem homogeneousComponent_coordinateEquiv (a b : K) (d : ℕ)
    (g : MvPolynomial (Fin 3) K) :
    homogeneousComponent d (coordinateEquiv a b g) =
      coordinateEquiv a b (homogeneousComponent d g) := by
  exact homogeneousComponent_aeval_degreeOne _ (coordinateForms_isHomogeneous a b) g d

theorem homogeneousComponent_projectiveEquiv (a b : K) (d : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    homogeneousComponent d (projectiveEquiv a b F) =
      projectiveEquiv a b (homogeneousComponent d F) := by
  exact homogeneousComponent_aeval_degreeOne _ (projectiveForms_isHomogeneous a b) F d

theorem totalDegree_coordinateEquiv_le (a b : K) (g : MvPolynomial (Fin 3) K) :
    (coordinateEquiv a b g).totalDegree ≤ g.totalDegree := by
  nth_rw 1 [← g.sum_homogeneousComponent]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro j hj
  exact (coordinateEquiv_isHomogeneous a b
    (homogeneousComponent_isHomogeneous j g)).totalDegree_le.trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem projectiveEquiv_homogenize (a b : K) (d : ℕ)
    (g : MvPolynomial (Fin 3) K) :
    projectiveEquiv a b (homogenize d g) = homogenize d (coordinateEquiv a b g) := by
  simp only [homogenize, map_sum, map_mul, map_pow,
    projectiveEquiv_X_zero (R := K) a b, projectiveEquiv_rename_succ,
    homogeneousComponent_coordinateEquiv]

theorem scalar_leading_form_coordinateEquiv (a b : K) {d : ℕ}
    {g k : MvPolynomial (Fin 3) K} {c : K}
    (htop : homogeneousComponent d g = C c * k) :
    homogeneousComponent d (coordinateEquiv a b g) = C c * coordinateEquiv a b k := by
  rw [homogeneousComponent_coordinateEquiv, htop, map_mul]
  simp [coordinateEquiv_apply]

/-- A pure top coefficient survives fixed-degree homogenization exactly. -/
theorem coeff_homogenize_last (d : ℕ) (g : MvPolynomial (Fin 3) K)
    (hdegree : g.totalDegree ≤ d) :
    (homogenize d g).coeff (Finsupp.single 3 d) = g.coeff (Finsupp.single 2 d) := by
  rw [homogenize_eq_standard]
  have hren := coeff_rename_mapDomain (_root_.finSuccEquiv 3).symm
    (_root_.finSuccEquiv 3).symm.injective (multivariateHomogenization g d)
    (Finsupp.single (some (2 : Fin 3)) d)
  rw [Finsupp.mapDomain_single, _root_.finSuccEquiv_symm_some] at hren
  have hj : (2 : Fin 3).succ = (3 : Fin 4) := by decide
  rw [hj] at hren
  rw [hren]
  have hc := coeff_multivariateDehomogenization_of_isHomogeneous
    (multivariateHomogenization g d) d (multivariateHomogenization_isHomogeneous g d)
    (Finsupp.single (some (2 : Fin 3)) d) (by simp)
  rw [multivariateDehomogenization_homogenization g d hdegree] at hc
  simpa using hc.symm

/-- The packet variable-degree assumption for the actual transformed
homogenization. No lower coefficient occurs in the pure-power condition. -/
theorem degreeOf_projectiveEquiv_homogenize_of_scalar_leading_form
    (a b : K) {d : ℕ} {g k : MvPolynomial (Fin 3) K} {c : K}
    (hdegree : g.totalDegree ≤ d) (hc : c ≠ 0)
    (htop : homogeneousComponent d g = C c * k)
    (hkcoeff : (coordinateEquiv a b k).coeff (Finsupp.single 2 d) ≠ 0) :
    (projectiveEquiv a b (homogenize d g)).degreeOf 3 = d := by
  rw [projectiveEquiv_homogenize]
  apply degreeOf_eq_of_pure_power_coeff_ne_zero 3 (homogenize_isHomogeneous d _).totalDegree_le
  rw [coeff_homogenize_last d _ ((totalDegree_coordinateEquiv_le a b g).trans hdegree)]
  have he := congrArg (coeff (Finsupp.single 2 d))
    (scalar_leading_form_coordinateEquiv a b htop)
  have he' : (coordinateEquiv a b g).coeff (Finsupp.single 2 d) =
      c * (coordinateEquiv a b k).coeff (Finsupp.single 2 d) := by
    simpa [coeff_homogeneousComponent] using he
  rw [he']
  exact mul_ne_zero hc hkcoeff
end Field

/-- The homogeneous lift agrees with homogenizing the transformed integral equation. -/
theorem integral_projectiveEquiv_homogenize (a b : ℤ) (d : ℕ)
    (g : MvPolynomial (Fin 3) ℤ) :
    projectiveEquiv a b (homogenize d g) = homogenize d (coordinateEquiv a b g) := by
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [map_projectiveEquiv, map_homogenize, map_homogenize, map_coordinateEquiv,
    projectiveEquiv_homogenize]

/-- Integral equations, rational scalar leading forms, and precisely the
rational variable degree consumed by the packet construction. -/
theorem rational_degreeOf_integral_transformed_homogenization
    (a b : ℤ) {d : ℕ} {g k : MvPolynomial (Fin 3) ℤ} {c : ℚ}
    (hdegree : (map (Int.castRingHom ℚ) g).totalDegree ≤ d) (hc : c ≠ 0)
    (htop : homogeneousComponent d (map (Int.castRingHom ℚ) g) =
      C c * map (Int.castRingHom ℚ) k)
    (hkcoeff : (coordinateEquiv a b k).coeff (Finsupp.single 2 d) ≠ 0) :
    (map (Int.castRingHom ℚ) (projectiveEquiv a b (homogenize d g))).degreeOf 3 = d := by
  rw [map_projectiveEquiv, map_homogenize]
  apply degreeOf_projectiveEquiv_homogenize_of_scalar_leading_form
    (a : ℚ) (b : ℚ) hdegree hc htop
  have he : map (Int.castRingHom ℚ) (coordinateEquiv a b k) =
      coordinateEquiv (a : ℚ) (b : ℚ) (map (Int.castRingHom ℚ) k) :=
    map_coordinateEquiv (Int.castRingHom ℚ) a b k
  rw [← he, coeff_map]
  intro hz
  apply hkcoeff
  exact Int.cast_injective (by simpa using hz)

/-- Choose the coordinates once from k, before every affine equation and
its nonzero scalar. This discharges the packet theorem's exact hvariable. -/
theorem exists_fixed_coordinates_for_all_scalar_leading_equations
    (k : MvPolynomial (Fin 3) ℤ) {d : ℕ} (hk : k.IsHomogeneous d) (hk0 : k ≠ 0) :
    ∃ a b : ℤ, (coordinateMatrix a b).det = 1 ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
        (map (Int.castRingHom ℚ) g).totalDegree ≤ d →
        homogeneousComponent d (map (Int.castRingHom ℚ) g) =
          C c * map (Int.castRingHom ℚ) k →
        (map (Int.castRingHom ℚ) (projectiveEquiv a b (homogenize d g))).degreeOf 3 = d := by
  obtain ⟨a, b, hdet, _hhom, hcoeff⟩ := exists_fixed_integral_pure_power_coordinate k hk hk0
  exact ⟨a, b, hdet, fun g c hc hdeg htop =>
    rational_degreeOf_integral_transformed_homogenization a b hdeg hc htop hcoeff⟩

end CubicTenVariables.FixedLeadingSurfaceCoordinateTransport
