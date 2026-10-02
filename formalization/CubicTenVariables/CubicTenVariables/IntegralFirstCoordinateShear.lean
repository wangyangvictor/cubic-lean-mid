import CubicTenVariables.AffineHypersurfaceParallelSliceTopPart
import TranslatedDepthSeven.GradedLinearSubstitution

/-!
# An explicit integral shear of the first coordinate

The coordinate change fixes every tail coordinate and adds their prescribed
integral linear combination to the first coordinate.  Its inverse negates
the coefficients.  The corresponding polynomial algebra equivalence
preserves homogeneous components and transports the exact leading-form
hypothesis used in the affine hypersurface counting theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace TranslatedDepthSeven

open MvPolynomial
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- Add a linear combination of the tail coordinates to coordinate zero. -/
def firstCoordinateShear (a : Fin n → R)
    (y : Fin (n + 1) → R) : Fin (n + 1) → R :=
  Fin.cases (y 0 + ∑ i, a i * y i.succ) (fun i => y i.succ)

@[simp]
theorem firstCoordinateShear_zero (a : Fin n → R)
    (y : Fin (n + 1) → R) :
    firstCoordinateShear a y 0 = y 0 + ∑ i, a i * y i.succ := rfl

@[simp]
theorem firstCoordinateShear_succ (a : Fin n → R)
    (y : Fin (n + 1) → R) (i : Fin n) :
    firstCoordinateShear a y i.succ = y i.succ := rfl

@[simp]
theorem firstCoordinateShear_neg_left (a : Fin n → R)
    (y : Fin (n + 1) → R) :
    firstCoordinateShear (-a) (firstCoordinateShear a y) = y := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp

@[simp]
theorem firstCoordinateShear_neg_right (a : Fin n → R)
    (y : Fin (n + 1) → R) :
    firstCoordinateShear a (firstCoordinateShear (-a) y) = y := by
  simpa only [neg_neg] using firstCoordinateShear_neg_left (-a) y

theorem firstCoordinateShear_injective (a : Fin n → R) :
    Function.Injective (firstCoordinateShear a) :=
  Function.LeftInverse.injective (firstCoordinateShear_neg_left a)

theorem firstCoordinateShear_bijective (a : Fin n → R) :
    Function.Bijective (firstCoordinateShear a) :=
  ⟨firstCoordinateShear_injective a, fun y =>
    ⟨firstCoordinateShear (-a) y, firstCoordinateShear_neg_right a y⟩⟩

/-- The literal linear forms specifying the polynomial substitution. -/
def firstCoordinateShearForms (a : Fin n → R) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
  Fin.cases (X 0 + ∑ i, C (a i) * X i.succ) (fun i => X i.succ)

/-- Polynomial pullback by the first-coordinate shear. -/
def firstCoordinateShearPolynomial (a : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R]
      MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.aeval (firstCoordinateShearForms a)

@[simp]
theorem firstCoordinateShearPolynomial_X_zero (a : Fin n → R) :
    firstCoordinateShearPolynomial a (X 0) =
      X 0 + ∑ i, C (a i) * X i.succ := by
  simp [firstCoordinateShearPolynomial, firstCoordinateShearForms]

@[simp]
theorem firstCoordinateShearPolynomial_X_succ (a : Fin n → R) (i : Fin n) :
    firstCoordinateShearPolynomial a (X i.succ) = X i.succ := by
  simp [firstCoordinateShearPolynomial, firstCoordinateShearForms]

@[simp]
theorem firstCoordinateShearPolynomial_C (a : Fin n → R) (r : R) :
    firstCoordinateShearPolynomial a (C r) = C r := by
  simp [firstCoordinateShearPolynomial]

theorem firstCoordinateShearPolynomial_comp_neg_left (a : Fin n → R) :
    (firstCoordinateShearPolynomial (-a)).comp
        (firstCoordinateShearPolynomial a) =
      AlgHom.id R (MvPolynomial (Fin (n + 1)) R) := by
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp

theorem firstCoordinateShearPolynomial_comp_neg_right (a : Fin n → R) :
    (firstCoordinateShearPolynomial a).comp
        (firstCoordinateShearPolynomial (-a)) =
      AlgHom.id R (MvPolynomial (Fin (n + 1)) R) := by
  simpa only [neg_neg] using firstCoordinateShearPolynomial_comp_neg_left (-a)

/-- The shear is an algebra equivalence over the original coefficient
ring; its inverse is the shear with all coefficients negated. -/
def firstCoordinateShearPolynomialEquiv (a : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R]
      MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom (firstCoordinateShearPolynomial a)
    (firstCoordinateShearPolynomial (-a))
    (firstCoordinateShearPolynomial_comp_neg_right a)
    (firstCoordinateShearPolynomial_comp_neg_left a)

@[simp]
theorem firstCoordinateShearPolynomialEquiv_apply (a : Fin n → R)
    (f : MvPolynomial (Fin (n + 1)) R) :
    firstCoordinateShearPolynomialEquiv a f =
      firstCoordinateShearPolynomial a f := rfl

/-- The pullback evaluates at exactly the sheared point. -/
theorem eval_firstCoordinateShearPolynomialEquiv (a : Fin n → R)
    (y : Fin (n + 1) → R) (f : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval y (firstCoordinateShearPolynomialEquiv a f) =
      MvPolynomial.eval (firstCoordinateShear a y) f := by
  let lhs : MvPolynomial (Fin (n + 1)) R →+* R :=
    (MvPolynomial.eval y).comp (firstCoordinateShearPolynomial a).toRingHom
  let rhs : MvPolynomial (Fin (n + 1)) R →+* R :=
    MvPolynomial.eval (firstCoordinateShear a y)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp [lhs, rhs]
  exact RingHom.congr_fun hhom f

/-- Coefficient extension commutes with shear pullback. -/
theorem map_firstCoordinateShearPolynomialEquiv
    (g : R →+* S) (a : Fin n → R)
    (f : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.map g (firstCoordinateShearPolynomialEquiv a f) =
      firstCoordinateShearPolynomialEquiv (fun i => g (a i))
        (MvPolynomial.map g f) := by
  let lhs : MvPolynomial (Fin (n + 1)) R →+*
      MvPolynomial (Fin (n + 1)) S :=
    (MvPolynomial.map g).comp (firstCoordinateShearPolynomial a).toRingHom
  let rhs : MvPolynomial (Fin (n + 1)) R →+*
      MvPolynomial (Fin (n + 1)) S :=
    (firstCoordinateShearPolynomial (fun i => g (a i))).toRingHom.comp
      (MvPolynomial.map g)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp [lhs, rhs]
  exact RingHom.congr_fun hhom f

theorem firstCoordinateShearForms_isHomogeneous
    (a : Fin n → R) (j : Fin (n + 1)) :
    (firstCoordinateShearForms a j).IsHomogeneous 1 := by
  classical
  refine Fin.cases ?_ (fun i => ?_) j
  · apply (MvPolynomial.isHomogeneous_X R (0 : Fin (n + 1))).add
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    exact (MvPolynomial.isHomogeneous_X R i.succ).C_mul (a i)
  · exact MvPolynomial.isHomogeneous_X R i.succ

/-- The rational shear preserves every homogeneous component, so its top
part is precisely the pullback of the original top part. -/
theorem homogeneousComponent_firstCoordinateShearPolynomialEquiv
    {K : Type*} [Field K] (a : Fin n → K) (d : ℕ)
    (f : MvPolynomial (Fin (n + 1)) K) :
    homogeneousComponent d (firstCoordinateShearPolynomialEquiv a f) =
      firstCoordinateShearPolynomialEquiv a (homogeneousComponent d f) := by
  exact homogeneousComponent_aeval_linear (firstCoordinateShearForms a)
    (firstCoordinateShearForms_isHomogeneous a) d f

/-- Exact transport of the integral hypersurface's leading-form predicate. -/
theorem isTopHomogeneousPart_firstCoordinateShearPolynomialEquiv
    (a : Fin n → ℤ) {d : ℕ}
    {f : MvPolynomial (Fin (n + 1)) ℤ}
    {h : MvPolynomial (Fin (n + 1)) ℚ}
    (htop : Published.IsTopHomogeneousPart f h d) :
    Published.IsTopHomogeneousPart
      (firstCoordinateShearPolynomialEquiv a f)
      (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) h) d := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_homogeneousComponent_boundary,
      map_firstCoordinateShearPolynomialEquiv,
      homogeneousComponent_firstCoordinateShearPolynomialEquiv,
      htop.1, map_homogeneousComponent_boundary]
    rfl
  · exact fun hz => htop.2.1
      ((firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ))).injective
        (by simpa only [map_zero] using hz))
  · intro k hdk
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [map_zero, map_homogeneousComponent_boundary,
      map_firstCoordinateShearPolynomialEquiv,
      homogeneousComponent_firstCoordinateShearPolynomialEquiv,
      ← map_homogeneousComponent_boundary, htop.2.2 k hdk, map_zero, map_zero]

/-- An invertible rational shear preserves absolute irreducibility. -/
theorem isAbsolutelyIrreducible_firstCoordinateShearPolynomialEquiv
    (a : Fin n → ℚ) {h : MvPolynomial (Fin (n + 1)) ℚ}
    (hirr : Published.IsAbsolutelyIrreducible h) :
    Published.IsAbsolutelyIrreducible (firstCoordinateShearPolynomialEquiv a h) := by
  unfold Published.IsAbsolutelyIrreducible at hirr ⊢
  rw [map_firstCoordinateShearPolynomialEquiv]
  exact hirr.map
    (firstCoordinateShearPolynomialEquiv
      (fun i => algebraMap ℚ (AlgebraicClosure ℚ) (a i))).toMulEquiv

end TranslatedDepthSeven
