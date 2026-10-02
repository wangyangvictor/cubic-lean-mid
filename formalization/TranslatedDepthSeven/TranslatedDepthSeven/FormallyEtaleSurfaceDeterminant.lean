import TranslatedDepthSeven.ArbitrarySurfacePolynomialDeterminant
import TranslatedDepthSeven.BivariateResidueDisc

/-!
# Determinants on a formally-etale surface chart

Let `P = ℤ[U,V]`, and let `A` be formally etale over `P`.  Suppose that a
finite family of maps

`A → ZMod (p ^ a)`

has parameter values represented by integral pairs `x_j`, all congruent to
one pair `y` modulo `p`, and that all maps reduce to the same point of `A`
over `ZMod p`.  Formal smoothness lifts this common point to the order-`a`
bivariate residue disc, while formal unramifiedness identifies each given
map with evaluation of that one lift at `x_j`.

Thus every finite family of functions in `A` is represented, simultaneously
for all columns, by a family of integral bivariate polynomials modulo `p ^ a`.
The arbitrary-polynomial determinant theorem then supplies the exact sum of
the first bivariate monomial weights.  The final theorem is stated both as
vanishing in `ZMod (p ^ a)` and as divisibility of an integer evaluation
determinant.

This formulation deliberately uses maps to `ZMod (p ^ a)`.  It therefore
applies to principal localizations: an inverted chart denominator only needs
to have nonzero reduction modulo `p`; it need not evaluate to a unit in `ℤ`.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The reduction map from an order-`a` residue disc, regarded as an algebra
homomorphism over `ℤ[U,V]`. -/
def bivariateResidueDiscReductionAlgHom
    (p a : ℕ) (ha : 0 < a) (y : Fin 2 → ℤ) :
    letI : Algebra BivariateIntPolynomial (ZMod p) :=
      (evalBivariateIntPolynomialZMod p y).toAlgebra
    (BivariateIntPolynomial ⧸ bivariateResidueIdeal p y ^ a) →ₐ[BivariateIntPolynomial]
      ZMod p := by
  letI : Algebra BivariateIntPolynomial (ZMod p) :=
    (evalBivariateIntPolynomialZMod p y).toAlgebra
  exact { bivariateResidueDiscReduction p a ha y with
    commutes' := fun _ ↦ rfl }

/-- A common residue point, regarded as an `ℤ[U,V]`-algebra map. -/
def bivariateResiduePointAlgHom
    {A : Type*} [CommRing A] [Algebra BivariateIntPolynomial A]
    (p : ℕ) (y : Fin 2 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod p y) :
    letI : Algebra BivariateIntPolynomial (ZMod p) :=
      (evalBivariateIntPolynomialZMod p y).toAlgebra
    A →ₐ[BivariateIntPolynomial] ZMod p := by
  letI : Algebra BivariateIntPolynomial (ZMod p) :=
    (evalBivariateIntPolynomialZMod p y).toAlgebra
  exact { point with
    commutes' := fun g ↦ RingHom.congr_fun hpoint g }

/-- The unique formal-etale expansion of a common residue point in the
order-`a` bivariate residue disc. -/
def bivariateEtaleDiscLift
    {A : Type*} [CommRing A] [Algebra BivariateIntPolynomial A]
    [Algebra.FormallyEtale BivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (y : Fin 2 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod p y) :
    A →ₐ[BivariateIntPolynomial]
      BivariateIntPolynomial ⧸ bivariateResidueIdeal p y ^ a := by
  letI : Algebra BivariateIntPolynomial (ZMod p) :=
    (evalBivariateIntPolynomialZMod p y).toAlgebra
  exact Algebra.FormallySmooth.liftOfSurjective
    (bivariateResiduePointAlgHom p y point hpoint)
    (bivariateResidueDiscReductionAlgHom p a ha y)
    (bivariateResidueDiscReduction_surjective p a ha y)
    (ker_bivariateResidueDiscReduction_isNilpotent p a ha y)

theorem bivariateResidueDiscReduction_comp_bivariateEtaleDiscLift
    {A : Type*} [CommRing A] [Algebra BivariateIntPolynomial A]
    [Algebra.FormallyEtale BivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (y : Fin 2 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod p y) :
    letI : Algebra BivariateIntPolynomial (ZMod p) :=
      (evalBivariateIntPolynomialZMod p y).toAlgebra
    (bivariateResidueDiscReductionAlgHom p a ha y).comp
      (bivariateEtaleDiscLift p a ha y point hpoint) =
        bivariateResiduePointAlgHom p y point hpoint := by
  letI : Algebra BivariateIntPolynomial (ZMod p) :=
    (evalBivariateIntPolynomialZMod p y).toAlgebra
  exact Algebra.FormallySmooth.comp_liftOfSurjective
    (bivariateResiduePointAlgHom p y point hpoint)
    (bivariateResidueDiscReductionAlgHom p a ha y)
    (bivariateResidueDiscReduction_surjective p a ha y)
    (ker_bivariateResidueDiscReduction_isNilpotent p a ha y)

/-- A simultaneous integral bivariate polynomial representative, modulo the
`a`-th power of the residue ideal, of one function on the etale chart. -/
def bivariateEtaleDiscRepresentative
    {A : Type*} [CommRing A] [Algebra BivariateIntPolynomial A]
    [Algebra.FormallyEtale BivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (y : Fin 2 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod p y)
    (f : A) : BivariateIntPolynomial :=
  Classical.choose (Ideal.Quotient.mk_surjective
    (bivariateEtaleDiscLift p a ha y point hpoint f))

theorem bivariateEtaleDiscRepresentative_spec
    {A : Type*} [CommRing A] [Algebra BivariateIntPolynomial A]
    [Algebra.FormallyEtale BivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (y : Fin 2 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod p y)
    (f : A) :
    Ideal.Quotient.mk (bivariateResidueIdeal p y ^ a)
        (bivariateEtaleDiscRepresentative p a ha y point hpoint f) =
      bivariateEtaleDiscLift p a ha y point hpoint f :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective
    (bivariateEtaleDiscLift p a ha y point hpoint f))

/-- Evaluation of the bivariate residue disc at a lift `x`, regarded as an
algebra homomorphism over the corresponding evaluation of `ℤ[U,V]`. -/
def bivariateResidueDiscEvaluationAlgHom
    (p a : ℕ) (ha : 0 < a) (x y : Fin 2 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    (BivariateIntPolynomial ⧸ bivariateResidueIdeal p y ^ a) →ₐ[BivariateIntPolynomial]
      ZMod (p ^ a) := by
  letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  exact { bivariateResidueDiscEvaluation p a ha x y hxy with
    commutes' := fun _ ↦ rfl }

/-- Reduction `ZMod (p ^ a) → ZMod p`, with the two compatible bivariate
parameter algebra structures. -/
def zmodPrimePowerReductionAlgHom
    (p a : ℕ) (ha : 0 < a) (x y : Fin 2 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    letI : Algebra BivariateIntPolynomial (ZMod p) :=
      (evalBivariateIntPolynomialZMod p y).toAlgebra
    ZMod (p ^ a) →ₐ[BivariateIntPolynomial] ZMod p := by
  letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  letI : Algebra BivariateIntPolynomial (ZMod p) :=
    (evalBivariateIntPolynomialZMod p y).toAlgebra
  exact { zmodPrimePowerReduction p a ha with
    commutes' := fun g ↦ RingHom.congr_fun
      (zmodPrimePowerReduction_comp_evalBivariateIntPolynomialZMod
        p a ha x y hxy) g }

theorem zmodPrimePowerReductionAlgHom_comp_bivariateResidueDiscEvaluationAlgHom
    (p a : ℕ) (ha : 0 < a) (x y : Fin 2 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    letI : Algebra BivariateIntPolynomial (ZMod p) :=
      (evalBivariateIntPolynomialZMod p y).toAlgebra
    (zmodPrimePowerReductionAlgHom p a ha x y hxy).comp
        (bivariateResidueDiscEvaluationAlgHom p a ha x y hxy) =
      bivariateResidueDiscReductionAlgHom p a ha y := by
  letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  letI : Algebra BivariateIntPolynomial (ZMod p) :=
    (evalBivariateIntPolynomialZMod p y).toAlgebra
  apply AlgHom.ext
  exact RingHom.congr_fun
    (zmodPrimePowerReduction_comp_bivariateResidueDiscEvaluation
      p a ha x y hxy)

/-- A given modular point of the chart, regarded as an algebra map over its
two displayed parameter values. -/
def bivariateModularSpecializationAlgHom
    {A : Type*} [CommRing A] [Algebra BivariateIntPolynomial A]
    (p a : ℕ) (x : Fin 2 → ℤ)
    (φ : A →+* ZMod (p ^ a))
    (hφbase : φ.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod (p ^ a) x) :
    letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    A →ₐ[BivariateIntPolynomial] ZMod (p ^ a) := by
  letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  exact { φ with
    commutes' := fun g ↦ RingHom.congr_fun hφbase g }

/-- Formal-etale uniqueness identifies a modular specialization with
evaluation of the universal residue-disc lift. -/
theorem bivariateModularSpecialization_eq_discEvaluation_comp_etaleLift
    {A : Type*} [CommRing A] [Algebra BivariateIntPolynomial A]
    [Algebra.FormallyEtale BivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (x y : Fin 2 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod p y)
    (φ : A →+* ZMod (p ^ a))
    (hφbase : φ.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod (p ^ a) x)
    (hφred : (zmodPrimePowerReduction p a ha).comp φ = point) :
    letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    letI : Algebra BivariateIntPolynomial (ZMod p) :=
      (evalBivariateIntPolynomialZMod p y).toAlgebra
    bivariateModularSpecializationAlgHom p a x φ hφbase =
      (bivariateResidueDiscEvaluationAlgHom p a ha x y hxy).comp
        (bivariateEtaleDiscLift p a ha y point hpoint) := by
  letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  letI : Algebra BivariateIntPolynomial (ZMod p) :=
    (evalBivariateIntPolynomialZMod p y).toAlgebra
  apply Algebra.FormallyUnramified.lift_unique'
    (zmodPrimePowerReductionAlgHom p a ha x y hxy)
    (ker_zmodPrimePowerReduction_isNilpotent p a ha)
  rw [show (zmodPrimePowerReductionAlgHom p a ha x y hxy).comp
      (bivariateModularSpecializationAlgHom p a x φ hφbase) =
        bivariateResiduePointAlgHom p y point hpoint by
    apply AlgHom.ext
    exact RingHom.congr_fun hφred]
  rw [← AlgHom.comp_assoc,
    zmodPrimePowerReductionAlgHom_comp_bivariateResidueDiscEvaluationAlgHom,
    bivariateResidueDiscReduction_comp_bivariateEtaleDiscLift]

/-- Every function on the formal-etale chart is, at all modular points in
the same residue disc, represented by one integral bivariate polynomial. -/
theorem bivariateModularSpecialization_apply_eq_eval_representative
    {A : Type*} [CommRing A] [Algebra BivariateIntPolynomial A]
    [Algebra.FormallyEtale BivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (x y : Fin 2 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod p y)
    (φ : A →+* ZMod (p ^ a))
    (hφbase : φ.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod (p ^ a) x)
    (hφred : (zmodPrimePowerReduction p a ha).comp φ = point)
    (f : A) :
    φ f = evalBivariateIntPolynomialZMod (p ^ a) x
      (bivariateEtaleDiscRepresentative p a ha y point hpoint f) := by
  letI : Algebra BivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalBivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  letI : Algebra BivariateIntPolynomial (ZMod p) :=
    (evalBivariateIntPolynomialZMod p y).toAlgebra
  have heq := AlgHom.congr_fun
    (bivariateModularSpecialization_eq_discEvaluation_comp_etaleLift
      p a ha x y hxy point hpoint φ hφbase hφred) f
  change φ f = bivariateResidueDiscEvaluationAlgHom p a ha x y hxy
    (bivariateEtaleDiscLift p a ha y point hpoint f) at heq
  rw [← bivariateEtaleDiscRepresentative_spec
    p a ha y point hpoint f] at heq
  simpa [bivariateResidueDiscEvaluationAlgHom,
    bivariateResidueDiscEvaluation] using heq

theorem evalBivariateIntPolynomialZMod_eq_intCast_eval
    (n : ℕ) (x : Fin 2 → ℤ) (f : BivariateIntPolynomial) :
    evalBivariateIntPolynomialZMod n x f =
      ((MvPolynomial.eval x f : ℤ) : ZMod n) := by
  exact (MvPolynomial.eval₂_comp (Int.castRingHom (ZMod n)) x f).symm

/-- Exact first-`r` bivariate-filtration determinant vanishing for arbitrary
functions on an actual formally-etale two-parameter chart.  The number of
rows and columns is

`affinePlaneMonomialCount k + s`,

and the modulus exponent is exactly

`affinePlaneMonomialWeight k + (k + 1) * s`.
-/
theorem formallyEtaleSurfaceSpecializations_det_eq_zero
    {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [Algebra BivariateIntPolynomial A]
    [Algebra.FormallyEtale BivariateIntPolynomial A]
    (k s : ℕ)
    (hcard : Fintype.card ι = affinePlaneMonomialCount k + s)
    (hpositive : 0 < affinePlaneMonomialWeight k + (k + 1) * s)
    (p : ℕ) (y : Fin 2 → ℤ) (x : ι → Fin 2 → ℤ)
    (hxy : ∀ j i, (p : ℤ) ∣ x j i - y i)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod p y)
    (F : ι → A)
    (φ : ι → A →+* ZMod
      (p ^ (affinePlaneMonomialWeight k + (k + 1) * s)))
    (hφbase : ∀ j, (φ j).comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod
        (p ^ (affinePlaneMonomialWeight k + (k + 1) * s)) (x j))
    (hφred : ∀ j,
      (zmodPrimePowerReduction p
        (affinePlaneMonomialWeight k + (k + 1) * s) hpositive).comp
          (φ j) = point) :
    (Matrix.of (fun i j ↦ φ j (F i))).det = 0 := by
  let exponent := affinePlaneMonomialWeight k + (k + 1) * s
  change 0 < exponent at hpositive
  let G : ι → BivariateIntPolynomial := fun i ↦
    bivariateEtaleDiscRepresentative
      p exponent hpositive y point hpoint (F i)
  have hentry (i j : ι) :
      φ j (F i) = evalBivariateIntPolynomialZMod
          (p ^ exponent) (x j) (G i) :=
    bivariateModularSpecialization_apply_eq_eval_representative
      p exponent hpositive (x j) y (hxy j) point hpoint
      (φ j) (hφbase j) (hφred j) (F i)
  have hmatrix : Matrix.of (fun i j ↦ φ j (F i)) =
      (filteredPolynomialEvaluationMatrix G x).map
        (Int.castRingHom (ZMod (p ^ exponent))) := by
    ext i j
    change φ j (F i) =
      ((MvPolynomial.eval (x j) (G i) : ℤ) : ZMod (p ^ exponent))
    rw [hentry]
    exact evalBivariateIntPolynomialZMod_eq_intCast_eval
      (p ^ exponent) (x j) (G i)
  rw [hmatrix]
  change ((Int.castRingHom (ZMod (p ^ exponent))).mapMatrix
    (filteredPolynomialEvaluationMatrix G x)).det = 0
  rw [← (Int.castRingHom (ZMod (p ^ exponent))).map_det]
  exact arbitraryBivariatePolynomialEvaluation_det_eq_zero_zmod
    exponent k s hcard le_rfl y x G hxy

/-- Integer form of `formallyEtaleSurfaceSpecializations_det_eq_zero`.
The entries need only agree modulo the displayed prime power with evaluations
on the localized chart; no map from the chart to `ℤ` is assumed. -/
theorem formallyEtaleSurfaceIntegerEvaluations_det_dvd
    {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [Algebra BivariateIntPolynomial A]
    [Algebra.FormallyEtale BivariateIntPolynomial A]
    (k s : ℕ)
    (hcard : Fintype.card ι = affinePlaneMonomialCount k + s)
    (hpositive : 0 < affinePlaneMonomialWeight k + (k + 1) * s)
    (p : ℕ) (y : Fin 2 → ℤ) (x : ι → Fin 2 → ℤ)
    (hxy : ∀ j i, (p : ℤ) ∣ x j i - y i)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod p y)
    (F : ι → A)
    (φ : ι → A →+* ZMod
      (p ^ (affinePlaneMonomialWeight k + (k + 1) * s)))
    (hφbase : ∀ j, (φ j).comp (algebraMap BivariateIntPolynomial A) =
      evalBivariateIntPolynomialZMod
        (p ^ (affinePlaneMonomialWeight k + (k + 1) * s)) (x j))
    (hφred : ∀ j,
      (zmodPrimePowerReduction p
        (affinePlaneMonomialWeight k + (k + 1) * s) hpositive).comp
          (φ j) = point)
    (value : Matrix ι ι ℤ)
    (hvalue : ∀ i j,
      ((value i j : ℤ) : ZMod
        (p ^ (affinePlaneMonomialWeight k + (k + 1) * s))) =
          φ j (F i)) :
    (p : ℤ) ^ (affinePlaneMonomialWeight k + (k + 1) * s) ∣
      value.det := by
  let exponent := affinePlaneMonomialWeight k + (k + 1) * s
  change ((p ^ exponent : ℕ) : ℤ) ∣ value.det
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [show ((value.det : ℤ) : ZMod (p ^ exponent)) =
      ((Int.castRingHom (ZMod (p ^ exponent))).mapMatrix value).det by
    exact (Int.castRingHom (ZMod (p ^ exponent))).map_det value]
  have hmatrix :
      (Int.castRingHom (ZMod (p ^ exponent))).mapMatrix value =
        Matrix.of (fun i j ↦ φ j (F i)) := by
    ext i j
    exact hvalue i j
  rw [hmatrix]
  exact formallyEtaleSurfaceSpecializations_det_eq_zero
    k s hcard hpositive p y x hxy point hpoint F φ hφbase hφred

end

end TranslatedDepthSeven
