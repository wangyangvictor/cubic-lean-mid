import CubicTenVariables.IrreducibleFromTopHomogeneousPart
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Units
import TranslatedDepthSeven.FiniteAffineEquationComponentCountInternal

/-!
# Equations for lines parallel to one coordinate axis

The line through `(0,a,b)` in direction `(1,0,0)` lies on a surface
exactly when the coefficients in the first variable vanish at `(a,b)`.
This is a polynomial identity, so it remains valid over finite fields.
All these coefficient equations have bounded degree. For an irreducible
surface which depends on the first variable they have no common nonunit
divisor: such a divisor would make the surface a cylinder.

The component bound at the end counts components, not points or lines.
Turning it into a line count requires proving that every component of
the coefficient locus is zero-dimensional.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceParallelLines

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The literal polynomial obtained by restricting to the coordinate line
with transverse coordinates `a`. -/
def lineRestriction (g : MvPolynomial (Fin (n + 1)) R) (a : Fin n → R) :
    Polynomial R :=
  Polynomial.map (eval a) (MvPolynomial.finSuccEquiv R n g)

/-- A finite set of all possibly nonzero coefficient equations. -/
def coefficientEquations (g : MvPolynomial (Fin (n + 1)) R) :
    Finset (MvPolynomial (Fin n) R) := by
  classical
  exact (Finset.range (g.totalDegree + 1)).image
    (MvPolynomial.finSuccEquiv R n g).coeff

theorem eval_lineRestriction (g : MvPolynomial (Fin (n + 1)) R)
    (a : Fin n → R) (t : R) :
    (lineRestriction g a).eval t = eval (Fin.cons t a) g :=
  (eval_eq_eval_mv_eval' a t g).symm

theorem lineRestriction_eq_zero_iff (g : MvPolynomial (Fin (n + 1)) R)
    (a : Fin n → R) :
    lineRestriction g a = 0 ↔
      ∀ i, eval a ((MvPolynomial.finSuccEquiv R n g).coeff i) = 0 := by
  simp only [lineRestriction, Polynomial.ext_iff, Polynomial.coeff_map,
    Polynomial.coeff_zero]

theorem coefficient_totalDegree_le (g : MvPolynomial (Fin (n + 1)) R)
    (i : ℕ) :
    ((MvPolynomial.finSuccEquiv R n g).coeff i).totalDegree ≤ g.totalDegree := by
  by_cases hi : (MvPolynomial.finSuccEquiv R n g).coeff i = 0
  · simp [hi]
  · exact (Nat.le_add_right _ _).trans (totalDegree_coeff_finSuccEquiv_add_le g i hi)

theorem coefficient_eq_zero_of_totalDegree_lt
    (g : MvPolynomial (Fin (n + 1)) R) {i : ℕ} (hi : g.totalDegree < i) :
    (MvPolynomial.finSuccEquiv R n g).coeff i = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree g 0).trans_lt hi

theorem coefficientEquations_totalDegree_le
    (g : MvPolynomial (Fin (n + 1)) R)
    (f : MvPolynomial (Fin n) R) (hf : f ∈ coefficientEquations g) :
    f.totalDegree ≤ g.totalDegree := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
  exact coefficient_totalDegree_le g i

/-- Scheme-theoretic containment of the whole line is exactly a point
of the displayed finite coefficient locus. No infinitude hypothesis is
used to replace a polynomial identity by equality of its values. -/
theorem lineRestriction_eq_zero_iff_mem_coefficientLocus
    (g : MvPolynomial (Fin (n + 1)) R) (a : Fin n → R) :
    lineRestriction g a = 0 ↔
      a ∈ TranslatedDepthSeven.finiteAffineCommonZeroLocus (coefficientEquations g) := by
  classical
  rw [lineRestriction_eq_zero_iff]
  constructor
  · intro h f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact h i
  · intro h i
    by_cases hi : i < g.totalDegree + 1
    · exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
    · rw [coefficient_eq_zero_of_totalDegree_lt g (by omega), map_zero]

section Domain

variable {A : Type*} [CommRing A] [IsDomain A]

/-- A common nonunit coefficient divisor of an irreducible polynomial
forces it to be independent of its polynomial variable. -/
theorem isUnit_common_coefficient_divisor_or_natDegree_eq_zero
    (P : Polynomial A) (hP : Irreducible P) (q : A)
    (hq : ∀ i, q ∣ P.coeff i) : IsUnit q ∨ P.natDegree = 0 := by
  obtain ⟨Q, hQ⟩ := (Polynomial.C_dvd_iff_dvd_coeff q P).mpr hq
  rcases hP.isUnit_or_isUnit hQ with hunit | hunit
  · exact Or.inl (Polynomial.isUnit_C.mp hunit)
  · right
    apply Nat.eq_zero_of_le_zero
    calc
      P.natDegree = (Polynomial.C q * Q).natDegree := congrArg _ hQ
      _ ≤ Q.natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit

end Domain

section Field

variable {K : Type*} [Field K]

/-- The no-common-factor conclusion, with the precise noncylindrical
condition expressed as positive degree in the chosen line direction. -/
theorem isUnit_of_dvd_all_coefficients
    (g : MvPolynomial (Fin (n + 1)) K) (hg : Irreducible g)
    (hdir : 0 < g.degreeOf 0) (q : MvPolynomial (Fin n) K)
    (hq : ∀ i, q ∣ (MvPolynomial.finSuccEquiv K n g).coeff i) : IsUnit q := by
  have hP : Irreducible (MvPolynomial.finSuccEquiv K n g) :=
    hg.map (MvPolynomial.finSuccEquiv K n)
  rcases isUnit_common_coefficient_divisor_or_natDegree_eq_zero _ hP q hq with h | h
  · exact h
  · rw [natDegree_finSuccEquiv] at h
    omega

theorem isUnit_of_dvd_all_coefficients_of_irreducible_top
    (g : MvPolynomial (Fin (n + 1)) K)
    (htop : Irreducible (homogeneousComponent g.totalDegree g))
    (hdir : 0 < g.degreeOf 0) (q : MvPolynomial (Fin n) K)
    (hq : ∀ i, q ∣ (MvPolynomial.finSuccEquiv K n g).coeff i) : IsUnit q :=
  isUnit_of_dvd_all_coefficients g
    (IrreducibleFromTopHomogeneousPart.irreducible_of_irreducible_topComponent g htop)
    hdir q hq

end Field

/-- A proved Bézout bound for the number of components of the parameter
locus of parallel lines on a rational polynomial hypersurface. This
alone does not assert that those components are points. -/
theorem rational_coefficientLocus_component_card_le
    {d : ℕ} (hd : 1 ≤ d) (g : MvPolynomial (Fin (n + 1)) ℚ)
    (hdegree : g.totalDegree ≤ d) :
    (TranslatedDepthSeven.finiteMinimalPrimes
      (TranslatedDepthSeven.finiteEquationIdeal (coefficientEquations g))).card ≤ d ^ n :=
  TranslatedDepthSeven.finiteAffineEquation_component_card_le hd _
    (fun f hf ↦ (coefficientEquations_totalDegree_le g f hf).trans hdegree)

end CubicTenVariables.FixedLeadingSurfaceParallelLines
