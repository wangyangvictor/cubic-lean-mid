import TranslatedDepthSeven.ArbitraryCurvePolynomialDeterminant
import TranslatedDepthSeven.UnivariateResidueDisc

/-!
# Determinants on a formally-étale curve chart

Let `P = ℤ[T]`, and let `A` be formally étale over `P`.  A finite family of
maps `A → ZMod (p^a)` with the same reduction modulo `p` is represented,
simultaneously, by integral univariate polynomials modulo `p^a`.  The
arbitrary univariate determinant theorem then gives the exact exponent
`0 + ⋯ + (r-1)` for `r` functions and `r` points.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Reduction from an order-`a` univariate residue disc, as an algebra map. -/
def univariateResidueDiscReductionAlgHom
    (p a : ℕ) (ha : 0 < a) (y : Fin 1 → ℤ) :
    letI : Algebra UnivariateIntPolynomial (ZMod p) :=
      (evalUnivariateIntPolynomialZMod p y).toAlgebra
    (UnivariateIntPolynomial ⧸ univariateResidueIdeal p y ^ a) →ₐ[UnivariateIntPolynomial]
      ZMod p := by
  letI : Algebra UnivariateIntPolynomial (ZMod p) :=
    (evalUnivariateIntPolynomialZMod p y).toAlgebra
  exact { univariateResidueDiscReduction p a ha y with
    commutes' := fun _ ↦ rfl }

def univariateResiduePointAlgHom
    {A : Type*} [CommRing A] [Algebra UnivariateIntPolynomial A]
    (p : ℕ) (y : Fin 1 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod p y) :
    letI : Algebra UnivariateIntPolynomial (ZMod p) :=
      (evalUnivariateIntPolynomialZMod p y).toAlgebra
    A →ₐ[UnivariateIntPolynomial] ZMod p := by
  letI : Algebra UnivariateIntPolynomial (ZMod p) :=
    (evalUnivariateIntPolynomialZMod p y).toAlgebra
  exact { point with
    commutes' := fun g ↦ RingHom.congr_fun hpoint g }

/-- The unique formal-étale expansion of the common residue point. -/
def univariateEtaleDiscLift
    {A : Type*} [CommRing A] [Algebra UnivariateIntPolynomial A]
    [Algebra.FormallyEtale UnivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (y : Fin 1 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod p y) :
    A →ₐ[UnivariateIntPolynomial]
      UnivariateIntPolynomial ⧸ univariateResidueIdeal p y ^ a := by
  letI : Algebra UnivariateIntPolynomial (ZMod p) :=
    (evalUnivariateIntPolynomialZMod p y).toAlgebra
  exact Algebra.FormallySmooth.liftOfSurjective
    (univariateResiduePointAlgHom p y point hpoint)
    (univariateResidueDiscReductionAlgHom p a ha y)
    (univariateResidueDiscReduction_surjective p a ha y)
    (ker_univariateResidueDiscReduction_isNilpotent p a ha y)

theorem univariateResidueDiscReduction_comp_univariateEtaleDiscLift
    {A : Type*} [CommRing A] [Algebra UnivariateIntPolynomial A]
    [Algebra.FormallyEtale UnivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (y : Fin 1 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod p y) :
    letI : Algebra UnivariateIntPolynomial (ZMod p) :=
      (evalUnivariateIntPolynomialZMod p y).toAlgebra
    (univariateResidueDiscReductionAlgHom p a ha y).comp
      (univariateEtaleDiscLift p a ha y point hpoint) =
        univariateResiduePointAlgHom p y point hpoint := by
  letI : Algebra UnivariateIntPolynomial (ZMod p) :=
    (evalUnivariateIntPolynomialZMod p y).toAlgebra
  exact Algebra.FormallySmooth.comp_liftOfSurjective
    (univariateResiduePointAlgHom p y point hpoint)
    (univariateResidueDiscReductionAlgHom p a ha y)
    (univariateResidueDiscReduction_surjective p a ha y)
    (ker_univariateResidueDiscReduction_isNilpotent p a ha y)

def univariateEtaleDiscRepresentative
    {A : Type*} [CommRing A] [Algebra UnivariateIntPolynomial A]
    [Algebra.FormallyEtale UnivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (y : Fin 1 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod p y)
    (f : A) : UnivariateIntPolynomial :=
  Classical.choose (Ideal.Quotient.mk_surjective
    (univariateEtaleDiscLift p a ha y point hpoint f))

theorem univariateEtaleDiscRepresentative_spec
    {A : Type*} [CommRing A] [Algebra UnivariateIntPolynomial A]
    [Algebra.FormallyEtale UnivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (y : Fin 1 → ℤ)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod p y)
    (f : A) :
    Ideal.Quotient.mk (univariateResidueIdeal p y ^ a)
        (univariateEtaleDiscRepresentative p a ha y point hpoint f) =
      univariateEtaleDiscLift p a ha y point hpoint f :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective
    (univariateEtaleDiscLift p a ha y point hpoint f))

def univariateResidueDiscEvaluationAlgHom
    (p a : ℕ) (ha : 0 < a) (x y : Fin 1 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    (UnivariateIntPolynomial ⧸ univariateResidueIdeal p y ^ a) →ₐ[UnivariateIntPolynomial]
      ZMod (p ^ a) := by
  letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  exact { univariateResidueDiscEvaluation p a ha x y hxy with
    commutes' := fun _ ↦ rfl }

def univariateZmodPrimePowerReductionAlgHom
    (p a : ℕ) (ha : 0 < a) (x y : Fin 1 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    letI : Algebra UnivariateIntPolynomial (ZMod p) :=
      (evalUnivariateIntPolynomialZMod p y).toAlgebra
    ZMod (p ^ a) →ₐ[UnivariateIntPolynomial] ZMod p := by
  letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  letI : Algebra UnivariateIntPolynomial (ZMod p) :=
    (evalUnivariateIntPolynomialZMod p y).toAlgebra
  exact { zmodPrimePowerReduction p a ha with
    commutes' := fun g ↦ RingHom.congr_fun
      (zmodPrimePowerReduction_comp_evalUnivariateIntPolynomialZMod
        p a ha x y hxy) g }

theorem univariateZmodPrimePowerReductionAlgHom_comp_discEvaluation
    (p a : ℕ) (ha : 0 < a) (x y : Fin 1 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i) :
    letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    letI : Algebra UnivariateIntPolynomial (ZMod p) :=
      (evalUnivariateIntPolynomialZMod p y).toAlgebra
    (univariateZmodPrimePowerReductionAlgHom p a ha x y hxy).comp
        (univariateResidueDiscEvaluationAlgHom p a ha x y hxy) =
      univariateResidueDiscReductionAlgHom p a ha y := by
  letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  letI : Algebra UnivariateIntPolynomial (ZMod p) :=
    (evalUnivariateIntPolynomialZMod p y).toAlgebra
  apply AlgHom.ext
  exact RingHom.congr_fun
    (zmodPrimePowerReduction_comp_univariateResidueDiscEvaluation
      p a ha x y hxy)

def univariateModularSpecializationAlgHom
    {A : Type*} [CommRing A] [Algebra UnivariateIntPolynomial A]
    (p a : ℕ) (x : Fin 1 → ℤ)
    (φ : A →+* ZMod (p ^ a))
    (hφbase : φ.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod (p ^ a) x) :
    letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    A →ₐ[UnivariateIntPolynomial] ZMod (p ^ a) := by
  letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  exact { φ with
    commutes' := fun g ↦ RingHom.congr_fun hφbase g }

theorem univariateModularSpecialization_eq_discEvaluation_comp_etaleLift
    {A : Type*} [CommRing A] [Algebra UnivariateIntPolynomial A]
    [Algebra.FormallyEtale UnivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (x y : Fin 1 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod p y)
    (φ : A →+* ZMod (p ^ a))
    (hφbase : φ.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod (p ^ a) x)
    (hφred : (zmodPrimePowerReduction p a ha).comp φ = point) :
    letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
      (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
    letI : Algebra UnivariateIntPolynomial (ZMod p) :=
      (evalUnivariateIntPolynomialZMod p y).toAlgebra
    univariateModularSpecializationAlgHom p a x φ hφbase =
      (univariateResidueDiscEvaluationAlgHom p a ha x y hxy).comp
        (univariateEtaleDiscLift p a ha y point hpoint) := by
  letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  letI : Algebra UnivariateIntPolynomial (ZMod p) :=
    (evalUnivariateIntPolynomialZMod p y).toAlgebra
  apply Algebra.FormallyUnramified.lift_unique'
    (univariateZmodPrimePowerReductionAlgHom p a ha x y hxy)
    (ker_zmodPrimePowerReduction_isNilpotent p a ha)
  rw [show (univariateZmodPrimePowerReductionAlgHom p a ha x y hxy).comp
      (univariateModularSpecializationAlgHom p a x φ hφbase) =
        univariateResiduePointAlgHom p y point hpoint by
    apply AlgHom.ext
    exact RingHom.congr_fun hφred]
  rw [← AlgHom.comp_assoc,
    univariateZmodPrimePowerReductionAlgHom_comp_discEvaluation,
    univariateResidueDiscReduction_comp_univariateEtaleDiscLift]

theorem univariateModularSpecialization_apply_eq_eval_representative
    {A : Type*} [CommRing A] [Algebra UnivariateIntPolynomial A]
    [Algebra.FormallyEtale UnivariateIntPolynomial A]
    (p a : ℕ) (ha : 0 < a) (x y : Fin 1 → ℤ)
    (hxy : ∀ i, (p : ℤ) ∣ x i - y i)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod p y)
    (φ : A →+* ZMod (p ^ a))
    (hφbase : φ.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod (p ^ a) x)
    (hφred : (zmodPrimePowerReduction p a ha).comp φ = point)
    (f : A) :
    φ f = evalUnivariateIntPolynomialZMod (p ^ a) x
      (univariateEtaleDiscRepresentative p a ha y point hpoint f) := by
  letI : Algebra UnivariateIntPolynomial (ZMod (p ^ a)) :=
    (evalUnivariateIntPolynomialZMod (p ^ a) x).toAlgebra
  letI : Algebra UnivariateIntPolynomial (ZMod p) :=
    (evalUnivariateIntPolynomialZMod p y).toAlgebra
  have heq := AlgHom.congr_fun
    (univariateModularSpecialization_eq_discEvaluation_comp_etaleLift
      p a ha x y hxy point hpoint φ hφbase hφred) f
  change φ f = univariateResidueDiscEvaluationAlgHom p a ha x y hxy
    (univariateEtaleDiscLift p a ha y point hpoint f) at heq
  rw [← univariateEtaleDiscRepresentative_spec
    p a ha y point hpoint f] at heq
  simpa [univariateResidueDiscEvaluationAlgHom,
    univariateResidueDiscEvaluation] using heq

theorem evalUnivariateIntPolynomialZMod_eq_intCast_eval
    (n : ℕ) (x : Fin 1 → ℤ) (f : UnivariateIntPolynomial) :
    evalUnivariateIntPolynomialZMod n x f =
      ((MvPolynomial.eval x f : ℤ) : ZMod n) := by
  exact (MvPolynomial.eval₂_comp (Int.castRingHom (ZMod n)) x f).symm

/-- Exact determinant vanishing for arbitrary functions on a formally
étale one-parameter chart. -/
theorem formallyEtaleCurveSpecializations_det_eq_zero
    {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [Algebra UnivariateIntPolynomial A]
    [Algebra.FormallyEtale UnivariateIntPolynomial A]
    (hpositive : 0 < affineLineJetWeight (Fintype.card ι))
    (p : ℕ) (y : Fin 1 → ℤ) (x : ι → Fin 1 → ℤ)
    (hxy : ∀ j i, (p : ℤ) ∣ x j i - y i)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod p y)
    (F : ι → A)
    (φ : ι → A →+* ZMod (p ^ affineLineJetWeight (Fintype.card ι)))
    (hφbase : ∀ j, (φ j).comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod
        (p ^ affineLineJetWeight (Fintype.card ι)) (x j))
    (hφred : ∀ j,
      (zmodPrimePowerReduction p
        (affineLineJetWeight (Fintype.card ι)) hpositive).comp (φ j) =
          point) :
    (Matrix.of (fun i j ↦ φ j (F i))).det = 0 := by
  let exponent := affineLineJetWeight (Fintype.card ι)
  change 0 < exponent at hpositive
  let G : ι → UnivariateIntPolynomial := fun i ↦
    univariateEtaleDiscRepresentative
      p exponent hpositive y point hpoint (F i)
  have hentry (i j : ι) :
      φ j (F i) = evalUnivariateIntPolynomialZMod
          (p ^ exponent) (x j) (G i) :=
    univariateModularSpecialization_apply_eq_eval_representative
      p exponent hpositive (x j) y (hxy j) point hpoint
      (φ j) (hφbase j) (hφred j) (F i)
  have hmatrix : Matrix.of (fun i j ↦ φ j (F i)) =
      (filteredPolynomialEvaluationMatrix G x).map
        (Int.castRingHom (ZMod (p ^ exponent))) := by
    ext i j
    change φ j (F i) =
      ((MvPolynomial.eval (x j) (G i) : ℤ) : ZMod (p ^ exponent))
    rw [hentry]
    exact evalUnivariateIntPolynomialZMod_eq_intCast_eval
      (p ^ exponent) (x j) (G i)
  rw [hmatrix]
  change ((Int.castRingHom (ZMod (p ^ exponent))).mapMatrix
    (filteredPolynomialEvaluationMatrix G x)).det = 0
  rw [← (Int.castRingHom (ZMod (p ^ exponent))).map_det]
  exact arbitraryUnivariatePolynomialEvaluation_det_eq_zero_zmod
    exponent le_rfl y x G hxy

/-- Integer divisibility form of the formally-étale curve determinant. -/
theorem formallyEtaleCurveIntegerEvaluations_det_dvd
    {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [Algebra UnivariateIntPolynomial A]
    [Algebra.FormallyEtale UnivariateIntPolynomial A]
    (hpositive : 0 < affineLineJetWeight (Fintype.card ι))
    (p : ℕ) (y : Fin 1 → ℤ) (x : ι → Fin 1 → ℤ)
    (hxy : ∀ j i, (p : ℤ) ∣ x j i - y i)
    (point : A →+* ZMod p)
    (hpoint : point.comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod p y)
    (F : ι → A)
    (φ : ι → A →+* ZMod (p ^ affineLineJetWeight (Fintype.card ι)))
    (hφbase : ∀ j, (φ j).comp (algebraMap UnivariateIntPolynomial A) =
      evalUnivariateIntPolynomialZMod
        (p ^ affineLineJetWeight (Fintype.card ι)) (x j))
    (hφred : ∀ j,
      (zmodPrimePowerReduction p
        (affineLineJetWeight (Fintype.card ι)) hpositive).comp (φ j) =
          point)
    (value : Matrix ι ι ℤ)
    (hvalue : ∀ i j,
      ((value i j : ℤ) :
        ZMod (p ^ affineLineJetWeight (Fintype.card ι))) = φ j (F i)) :
    (p : ℤ) ^ affineLineJetWeight (Fintype.card ι) ∣ value.det := by
  let exponent := affineLineJetWeight (Fintype.card ι)
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
  exact formallyEtaleCurveSpecializations_det_eq_zero
    hpositive p y x hxy point hpoint F φ hφbase hφred

end

end TranslatedDepthSeven
