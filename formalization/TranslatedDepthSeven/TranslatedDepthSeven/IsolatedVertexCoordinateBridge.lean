import TranslatedDepthSeven.FirstCoordinateProduct
import TranslatedDepthSeven.TaggedLineCount
import TranslatedDepthSeven.IntegralHomogeneousIdealModel
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Unimodular coordinates for an isolated vertex direction

This file supplies the algebraic seam before `FirstCoordinateProduct`.
An integral unimodular matrix is turned into an explicit polynomial-ring
automorphism, with an exact evaluation and common-zero transport theorem.
If a finite homogeneous family is rationally translation-invariant along a
primitive integral direction, the standard primitive-vector completion
theorem then moves that direction to `e₀`; the transformed family is proved
to be the literal lift of a homogeneous family in one fewer variable.

The only assumed inputs are the universal textbook lattice statement that a
primitive vector extends to a unimodular basis and the elementary cylinder
lemma for a homogeneous translation-stable ideal.  Ideal stability must not
be confused with pointwise constancy of every member of the ideal (the latter
is destroyed by multiplication by a coordinate).  The cylinder lemma instead
extracts homogeneous generators which are individually constant in the
direction.  No point-counting assertion occurs here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1000000

def matrixLinearPolynomial {R : Type*} [CommSemiring R] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (i : Fin m) : MvPolynomial (Fin m) R :=
  ∑ j, C (A i j) * X j

@[simp]
theorem eval_matrixLinearPolynomial {R : Type*} [CommSemiring R] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (x : Fin m → R) (i : Fin m) :
    eval x (matrixLinearPolynomial A i) = Matrix.mulVec A x i := by
  simp [matrixLinearPolynomial, Matrix.mulVec, dotProduct]

def polynomialMatrixSubstitution {R : Type*} [CommSemiring R] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) :
    MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
  MvPolynomial.bind₁ (matrixLinearPolynomial A)

@[simp]
theorem eval_polynomialMatrixSubstitution {R : Type*} [CommSemiring R] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (x : Fin m → R)
    (f : MvPolynomial (Fin m) R) :
    eval x (polynomialMatrixSubstitution A f) = eval (Matrix.mulVec A x) f := by
  change eval₂Hom (RingHom.id R) x
      (MvPolynomial.bind₁ (matrixLinearPolynomial A) f) =
    eval₂Hom (RingHom.id R) (Matrix.mulVec A x) f
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

theorem matrixLinearPolynomial_isHomogeneous
    {R : Type*} [CommSemiring R] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    (matrixLinearPolynomial A i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
  intro j _hj
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem polynomialMatrixSubstitution_isHomogeneous
    {R : Type*} [CommSemiring R] {m d : ℕ}
    (A : Matrix (Fin m) (Fin m) R)
    {f : MvPolynomial (Fin m) R} (hf : f.IsHomogeneous d) :
    (polynomialMatrixSubstitution A f).IsHomogeneous d := by
  simpa using hf.aeval (matrixLinearPolynomial A)
    (matrixLinearPolynomial_isHomogeneous A)

theorem polynomialMatrixSubstitution_matrixLinearPolynomial
    {R : Type*} [CommRing R] [IsDomain R] [Infinite R] {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    polynomialMatrixSubstitution A (matrixLinearPolynomial B i) =
      matrixLinearPolynomial (B * A) i := by
  apply MvPolynomial.funext
  intro x
  rw [eval_polynomialMatrixSubstitution,
    eval_matrixLinearPolynomial, eval_matrixLinearPolynomial,
    Matrix.mulVec_mulVec]

theorem polynomialMatrixSubstitution_comp
    {R : Type*} [CommRing R] [IsDomain R] [Infinite R] {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) R) :
    (polynomialMatrixSubstitution A).comp
        (polynomialMatrixSubstitution B) =
      polynomialMatrixSubstitution (B * A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa [polynomialMatrixSubstitution] using
    polynomialMatrixSubstitution_matrixLinearPolynomial A B i

structure IntegralUnimodularChange (m : ℕ) where
  forward : Matrix (Fin m) (Fin m) ℤ
  inverse : Matrix (Fin m) (Fin m) ℤ
  forward_mul_inverse : forward * inverse = 1
  inverse_mul_forward : inverse * forward = 1

namespace IntegralUnimodularChange

def pointEquiv {m : ℕ} (U : IntegralUnimodularChange m) :
    (Fin m → ℤ) ≃ (Fin m → ℤ) where
  toFun x := Matrix.mulVec U.forward x
  invFun y := Matrix.mulVec U.inverse y
  left_inv x := by
    change Matrix.mulVec U.inverse (Matrix.mulVec U.forward x) = x
    rw [Matrix.mulVec_mulVec, U.inverse_mul_forward,
      Matrix.one_mulVec]
  right_inv y := by
    change Matrix.mulVec U.forward (Matrix.mulVec U.inverse y) = y
    rw [Matrix.mulVec_mulVec, U.forward_mul_inverse,
      Matrix.one_mulVec]

def polynomialEquiv {m : ℕ} (U : IntegralUnimodularChange m) :
    MvPolynomial (Fin m) ℤ ≃ₐ[ℤ] MvPolynomial (Fin m) ℤ :=
  AlgEquiv.ofAlgHom
    (polynomialMatrixSubstitution U.inverse)
    (polynomialMatrixSubstitution U.forward)
    (by
      rw [polynomialMatrixSubstitution_comp, U.forward_mul_inverse]
      apply MvPolynomial.algHom_ext
      intro i
      classical
      simp [polynomialMatrixSubstitution, matrixLinearPolynomial,
        Matrix.one_apply])
    (by
      rw [polynomialMatrixSubstitution_comp, U.inverse_mul_forward]
      apply MvPolynomial.algHom_ext
      intro i
      classical
      simp [polynomialMatrixSubstitution, matrixLinearPolynomial,
        Matrix.one_apply])

@[simp]
theorem eval_polynomialEquiv {m : ℕ} (U : IntegralUnimodularChange m)
    (x : Fin m → ℤ) (f : MvPolynomial (Fin m) ℤ) :
    eval x (U.polynomialEquiv f) = eval (Matrix.mulVec U.inverse x) f := by
  exact eval_polynomialMatrixSubstitution U.inverse x f

end IntegralUnimodularChange

/-- The primitive direction of the distinguished first coordinate. -/
def firstCoordinateIntDirection {n : ℕ} : IntVector (n + 1) :=
  Fin.cons 1 0

@[simp]
theorem firstCoordinateIntDirection_zero {n : ℕ} :
    firstCoordinateIntDirection (n := n) 0 = 1 := rfl

@[simp]
theorem firstCoordinateIntDirection_succ {n : ℕ} (i : Fin n) :
    firstCoordinateIntDirection (n := n) i.succ = 0 := rfl

/-- Polynomial invariance under every integral translate in a direction. -/
def PolynomialTranslationInvariant {m : ℕ}
    (h : IntVector m) (f : MvPolynomial (Fin m) ℤ) : Prop :=
  ∀ (x : IntVector m) (t : ℤ),
    eval (x + t • h) f = eval x f

/-- Rational translation invariance of an integral polynomial along its
integral direction vector.  This is the form supplied by a rational vertex. -/
def RationalPolynomialTranslationInvariantOverQ {m : ℕ}
    (h : Fin m → ℚ) (f : MvPolynomial (Fin m) ℚ) : Prop :=
  ∀ (x : Fin m → ℚ) (t : ℚ),
    eval (x + t • h) f = eval x f

def RationalPolynomialTranslationInvariant {m : ℕ}
    (h : IntVector m) (f : MvPolynomial (Fin m) ℤ) : Prop :=
  RationalPolynomialTranslationInvariantOverQ (fun i ↦ (h i : ℚ))
    (MvPolynomial.map (Int.castRingHom ℚ) f)

/-- Pullback by the affine translation `x ↦ x + t h`. -/
def rationalTranslationSubstitutionOverQ {m : ℕ}
    (h : Fin m → ℚ) (t : ℚ) :
    MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin m) ℚ :=
  MvPolynomial.aeval fun i ↦ MvPolynomial.X i + MvPolynomial.C (t * h i)

@[simp]
theorem eval_rationalTranslationSubstitutionOverQ {m : ℕ}
    (h : Fin m → ℚ) (t : ℚ) (x : Fin m → ℚ)
    (f : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.eval x (rationalTranslationSubstitutionOverQ h t f) =
      MvPolynomial.eval (x + t • h) f := by
  rw [rationalTranslationSubstitutionOverQ,
    MvPolynomial.aeval_eq_bind₁]
  change MvPolynomial.eval₂Hom (RingHom.id ℚ) x
      (MvPolynomial.bind₁
        (fun i ↦ MvPolynomial.X i + MvPolynomial.C (t * h i)) f) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp [Pi.add_apply, Pi.smul_apply]

/-- A rational ideal is stable under every translation in the displayed
direction.  Equality, rather than one inclusion, makes this literal
invariance under the additive-group action. -/
def RationalIdealTranslationInvariant {m : ℕ}
    (h : IntVector m) (I : Ideal (MvPolynomial (Fin m) ℚ)) : Prop :=
  ∀ t : ℚ,
    Ideal.map
      (rationalTranslationSubstitutionOverQ (fun i ↦ (h i : ℚ)) t) I = I

namespace StandardAG

/-- The elementary cylinder lemma in characteristic zero.  A homogeneous
ideal stable under all translations along a nonzero rational direction has
a finite homogeneous generating family whose members are individually
independent of that direction.

After a rational linear change taking the direction to the first coordinate,
this is coefficient extraction in `Q[x₀,…,xₙ]` for an ideal stable under
all substitutions `x₀ ↦ x₀+t`.  A Vandermonde argument extracts the
coefficients in `x₀`, and Noetherianity supplies a finite family. -/
def TranslationStableHomogeneousIdealCylinderGenerators : Prop :=
  ∀ (m : ℕ) (I : Ideal (MvPolynomial (Fin m) ℚ))
      (h : IntVector m),
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℚ) →
    h ≠ 0 →
    RationalIdealTranslationInvariant h I →
      ∃ equations : Finset (MvPolynomial (Fin m) ℚ),
        (∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) ∧
        Ideal.span (equations : Set (MvPolynomial (Fin m) ℚ)) = I ∧
        ∀ f ∈ equations,
          RationalPolynomialTranslationInvariantOverQ
            (fun i ↦ (h i : ℚ)) f

end StandardAG

theorem RationalPolynomialTranslationInvariant.integral
    {m : ℕ} {h : IntVector m} {f : MvPolynomial (Fin m) ℤ}
    (hf : RationalPolynomialTranslationInvariant h f) :
    PolynomialTranslationInvariant h f := by
  intro x t
  have hrat := hf (fun i ↦ (x i : ℚ)) (t : ℚ)
  have hvector :
      (⇑(Int.castRingHom ℚ)) ∘ (x + t • h) =
        (fun i ↦ (x i : ℚ)) + (t : ℚ) • (fun i ↦ (h i : ℚ)) := by
    funext i
    simp [Function.comp_apply, Pi.add_apply, Pi.smul_apply]
  apply Int.cast_injective (α := ℚ)
  change (Int.castRingHom ℚ) (eval (x + t • h) f) =
    (Int.castRingHom ℚ) (eval x f)
  rw [MvPolynomial.eval₂_comp, MvPolynomial.eval₂_comp,
    ← MvPolynomial.eval_map, ← MvPolynomial.eval_map]
  rw [hvector]
  simpa [Function.comp_apply] using hrat

theorem rationalTranslationInvariant_clearRationalMvPolynomial
    {m : ℕ} {h : IntVector m} {f : MvPolynomial (Fin m) ℚ}
    (hf : RationalPolynomialTranslationInvariantOverQ
      (fun i ↦ (h i : ℚ)) f) :
    RationalPolynomialTranslationInvariant h
      (clearRationalMvPolynomial f) := by
  intro x t
  rw [map_clearRationalMvPolynomial]
  simpa only [map_mul, eval_C] using congrArg
    (fun a : ℚ ↦ (mvPolynomialRationalCommonDenominator f : ℚ) * a)
    (hf x t)

/-- Set the distinguished first variable equal to zero. -/
def restrictFirstPolynomialToZero {R : Type*} [CommSemiring R] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) R) : MvPolynomial (Fin n) R :=
  MvPolynomial.aeval (Fin.cases 0 MvPolynomial.X) f

theorem restrictFirstPolynomialToZero_isHomogeneous
    {R : Type*} [CommSemiring R] {n d : ℕ}
    {f : MvPolynomial (Fin (n + 1)) R} (hf : f.IsHomogeneous d) :
    (restrictFirstPolynomialToZero f).IsHomogeneous d := by
  change (MvPolynomial.aeval (Fin.cases 0 MvPolynomial.X) f).IsHomogeneous d
  convert hf.aeval (Fin.cases 0 MvPolynomial.X) (fun i ↦ by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · show (0 : MvPolynomial (Fin n) R).IsHomogeneous 1
        exact (MvPolynomial.homogeneousSubmodule (Fin n) R 1).zero_mem
      · exact MvPolynomial.isHomogeneous_X R j) using 1
  omega

@[simp]
theorem eval_restrictFirstPolynomialToZero
    {R : Type*} [CommSemiring R] {n : ℕ}
    (z : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval z (restrictFirstPolynomialToZero f) =
      eval (Fin.cons 0 z) f := by
  change eval₂Hom (RingHom.id R) z
      (MvPolynomial.bind₁ (Fin.cases 0 MvPolynomial.X) f) =
    eval₂Hom (RingHom.id R) (Fin.cons 0 z) f
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp

/-- Translation invariance in the first direction forces literal
independence of the first variable over `ℤ`. -/
theorem eq_lift_restrictFirstPolynomialToZero_of_translationInvariant
    {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : PolynomialTranslationInvariant firstCoordinateIntDirection f) :
    f = liftPolynomialAfterFirst (restrictFirstPolynomialToZero f) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_liftPolynomialAfterFirst,
    eval_restrictFirstPolynomialToZero]
  have htranslate := hf x (-(x 0))
  have hvector :
      x + (-(x 0)) • firstCoordinateIntDirection =
        prependFirstIntVector 0 (dropFirstIntVector x) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [prependFirstIntVector]
    · simp [prependFirstIntVector, dropFirstIntVector]
  rw [hvector] at htranslate
  exact htranslate.symm

/-- Canonical lower-dimensional family obtained by setting the first
coordinate equal to zero. -/
def restrictFirstEquationFinsetToZero {n : ℕ}
    (equations : Finset (MvPolynomial (Fin (n + 1)) ℤ)) :
    Finset (MvPolynomial (Fin n) ℤ) := by
  classical
  exact equations.image restrictFirstPolynomialToZero

theorem equationFinset_eq_lift_restrictFirst_of_translationInvariant
    {n : ℕ} (equations : Finset (MvPolynomial (Fin (n + 1)) ℤ))
    (hinvariant : ∀ f ∈ equations,
      PolynomialTranslationInvariant firstCoordinateIntDirection f) :
    equations = liftEquationFinsetAfterFirst
      (restrictFirstEquationFinsetToZero equations) := by
  classical
  apply Finset.ext
  intro f
  constructor
  · intro hf
    rw [eq_lift_restrictFirstPolynomialToZero_of_translationInvariant
      f (hinvariant f hf)]
    apply Finset.mem_map.mpr
    refine ⟨restrictFirstPolynomialToZero f, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
  · intro hf
    obtain ⟨g, hg, hgf⟩ := Finset.mem_map.mp hf
    obtain ⟨p, hp, hpg⟩ := Finset.mem_image.mp hg
    have heq := eq_lift_restrictFirstPolynomialToZero_of_translationInvariant
      p (hinvariant p hp)
    have hlift : liftPolynomialAfterFirst g = f := by
      simpa [liftPolynomialAfterFirstEmbedding] using hgf
    have hfp : f = p :=
      hlift.symm.trans
        ((congrArg liftPolynomialAfterFirst hpg).symm.trans heq.symm)
    simpa [hfp] using hp

namespace IntegralUnimodularChange

/-- Transport a finite integral equation family to the new coordinates. -/
def transformEquationFinset {m : ℕ} (U : IntegralUnimodularChange m)
    (equations : Finset (MvPolynomial (Fin m) ℤ)) :
    Finset (MvPolynomial (Fin m) ℤ) :=
  equations.map U.polynomialEquiv.toEmbedding

/-- Exact common-zero transport under a unimodular integral coordinate
change. -/
theorem integralCommonZero_transform_iff {m : ℕ}
    (U : IntegralUnimodularChange m)
    (equations : Finset (MvPolynomial (Fin m) ℤ))
    (x : IntVector m) :
    IntegralCommonZero (U.transformEquationFinset equations)
        (U.pointEquiv x) ↔ IntegralCommonZero equations x := by
  constructor
  · intro hx f hf
    have hmem : U.polynomialEquiv f ∈
        U.transformEquationFinset equations :=
      Finset.mem_map.mpr ⟨f, hf, rfl⟩
    have := hx (U.polynomialEquiv f) hmem
    simpa [pointEquiv, Matrix.mulVec_mulVec,
      U.inverse_mul_forward] using this
  · intro hx g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hg
    simpa [pointEquiv, Matrix.mulVec_mulVec,
      U.inverse_mul_forward] using hx f hf

/-- The inverse matrix carries the normalized first direction back to the
original primitive direction. -/
theorem inverse_mulVec_first_eq {n : ℕ}
    (U : IntegralUnimodularChange (n + 1)) (h : IntVector (n + 1))
    (hforward : Matrix.mulVec U.forward h = firstCoordinateIntDirection) :
    Matrix.mulVec U.inverse firstCoordinateIntDirection = h := by
  rw [← hforward, Matrix.mulVec_mulVec,
    U.inverse_mul_forward, Matrix.one_mulVec]

/-- Translation invariance transports to the first coordinate once the
unimodular matrix sends the direction to `e₀`. -/
theorem polynomialEquiv_translationInvariant_first {n : ℕ}
    (U : IntegralUnimodularChange (n + 1)) (h : IntVector (n + 1))
    (hforward : Matrix.mulVec U.forward h = firstCoordinateIntDirection)
    {f : MvPolynomial (Fin (n + 1)) ℤ}
    (hf : PolynomialTranslationInvariant h f) :
    PolynomialTranslationInvariant firstCoordinateIntDirection
      (U.polynomialEquiv f) := by
  intro y t
  simp only [eval_polynomialEquiv]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul,
    U.inverse_mulVec_first_eq h hforward]
  exact hf (Matrix.mulVec U.inverse y) t

end IntegralUnimodularChange

/-- A homogeneous rational ideal which is already known to be cylindrical
in a rational direction admits finite integral homogeneous generators which
are individually invariant in that direction.  This is denominator clearing,
not an additional geometry assumption. -/
theorem exists_integral_invariant_homogeneous_generators
    (hcylinder : StandardAG.TranslationStableHomogeneousIdealCylinderGenerators)
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℚ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℚ))
    (h : IntVector m) (hh : h ≠ 0)
    (hinvariant : RationalIdealTranslationInvariant h I) :
    ∃ equations : Finset (MvPolynomial (Fin m) ℤ),
      (∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) ∧
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (equations : Set (MvPolynomial (Fin m) ℤ))) = I ∧
      ∀ f ∈ equations, RationalPolynomialTranslationInvariant h f := by
  classical
  letI : DecidableEq (Fin m) := Classical.decEq _
  obtain ⟨rationalEquations, hhomogeneous, hspan,
      hequationInvariant⟩ :=
    hcylinder m I h hI hh hinvariant
  let equations := clearedIntegralEquationFinset rationalEquations
  refine ⟨equations, ?_, ?_, ?_⟩
  · intro f hf
    apply clearedIntegralEquationFinset_each_isHomogeneous
      rationalEquations hhomogeneous
    simpa [equations] using hf
  · rw [show equations = clearedIntegralEquationFinset rationalEquations from rfl,
      map_finiteEquationIdeal_clearedIntegralEquationFinset]
    simpa [finiteEquationIdeal] using hspan
  · intro g hg
    have hgset : g ∈
        (clearedIntegralEquationFinset rationalEquations :
          Set (MvPolynomial (Fin m) ℤ)) := by
      simpa [equations] using hg
    rw [Finset.mem_coe, clearedIntegralEquationFinset,
      Finset.mem_image] at hgset
    obtain ⟨f, hf, rfl⟩ := hgset
    apply rationalTranslationInvariant_clearRationalMvPolynomial
    exact hequationInvariant f hf

namespace StandardLattice

/-- The standard primitive-vector completion theorem over `ℤ`: a primitive
vector is the first column of a unimodular basis, equivalently some integral
unimodular matrix carries it to `e₀`. -/
def PrimitiveDirectionUnimodularCompletion : Prop :=
  ∀ (n : ℕ) (h : IntVector (n + 1)), PrimitiveDirection h →
    ∃ U : IntegralUnimodularChange (n + 1),
      Matrix.mulVec U.forward h = firstCoordinateIntDirection

end StandardLattice

/-- Exact isolated-vertex coordinate reduction, given a displayed
unimodular completion of the direction.  The new equations are literally
lifts from `n` variables, their common-zero set is the old one in the new
coordinates, and homogeneity is preserved. -/
theorem exists_firstCoordinateEquationReduction_of_unimodular
    {n : ℕ}
    (equations : Finset (MvPolynomial (Fin (n + 1)) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (h : IntVector (n + 1))
    (U : IntegralUnimodularChange (n + 1))
    (hforward : Matrix.mulVec U.forward h = firstCoordinateIntDirection)
    (hinvariant : ∀ f ∈ equations,
      RationalPolynomialTranslationInvariant h f) :
    ∃ lowerEquations : Finset (MvPolynomial (Fin n) ℤ),
      U.transformEquationFinset equations =
          liftEquationFinsetAfterFirst lowerEquations ∧
      (∀ g ∈ lowerEquations, ∃ d : ℕ, g.IsHomogeneous d) ∧
      ∀ x : IntVector (n + 1),
        IntegralCommonZero (liftEquationFinsetAfterFirst lowerEquations)
            (U.pointEquiv x) ↔
          IntegralCommonZero equations x := by
  let transformed := U.transformEquationFinset equations
  have htransformedInvariant : ∀ f ∈ transformed,
      PolynomialTranslationInvariant firstCoordinateIntDirection f := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hf
    exact U.polynomialEquiv_translationInvariant_first h hforward
      ((hinvariant g hg).integral)
  let lowerEquations := restrictFirstEquationFinsetToZero transformed
  have hfamily : transformed =
      liftEquationFinsetAfterFirst lowerEquations :=
    equationFinset_eq_lift_restrictFirst_of_translationInvariant
      transformed htransformedInvariant
  refine ⟨lowerEquations, hfamily, ?_, ?_⟩
  · intro g hg
    obtain ⟨f, hf, hfg⟩ := Finset.mem_image.mp hg
    obtain ⟨p, hp, hpf⟩ := Finset.mem_map.mp hf
    obtain ⟨d, hpd⟩ := hhomogeneous p hp
    refine ⟨d, ?_⟩
    rw [← hfg, ← hpf]
    apply restrictFirstPolynomialToZero_isHomogeneous
    simpa [IntegralUnimodularChange.polynomialEquiv] using
      polynomialMatrixSubstitution_isHomogeneous U.inverse hpd
  · intro x
    rw [← hfamily]
    exact U.integralCommonZero_transform_iff equations x

/-- Consolidated primitive-direction form.  Its only non-formal input is the
universal textbook lattice theorem `PrimitiveDirectionUnimodularCompletion`;
no counting statement is assumed. -/
theorem exists_unimodular_firstCoordinateEquationReduction
    (hcompletion : StandardLattice.PrimitiveDirectionUnimodularCompletion)
    {n : ℕ}
    (equations : Finset (MvPolynomial (Fin (n + 1)) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (h : IntVector (n + 1)) (hprimitive : PrimitiveDirection h)
    (hinvariant : ∀ f ∈ equations,
      RationalPolynomialTranslationInvariant h f) :
    ∃ (U : IntegralUnimodularChange (n + 1))
        (lowerEquations : Finset (MvPolynomial (Fin n) ℤ)),
      Matrix.mulVec U.forward h = firstCoordinateIntDirection ∧
      U.transformEquationFinset equations =
          liftEquationFinsetAfterFirst lowerEquations ∧
      (∀ g ∈ lowerEquations, ∃ d : ℕ, g.IsHomogeneous d) ∧
      ∀ x : IntVector (n + 1),
        IntegralCommonZero (liftEquationFinsetAfterFirst lowerEquations)
            (U.pointEquiv x) ↔
          IntegralCommonZero equations x := by
  obtain ⟨U, hforward⟩ := hcompletion n h hprimitive
  obtain ⟨lowerEquations, hfamily, hhomLower, hzero⟩ :=
    exists_firstCoordinateEquationReduction_of_unimodular
      equations hhomogeneous h U hforward hinvariant
  exact ⟨U, lowerEquations, hforward, hfamily, hhomLower, hzero⟩

/-- Ideal-level isolated-vertex bridge.  A homogeneous rational ideal known
to be translation-invariant in a primitive integral direction is first given
an invariant integral homogeneous generating family, then a unimodular
coordinate change makes that family literally independent of `x₀`. -/
theorem exists_unimodular_firstCoordinateEquationReduction_of_ideal
    (hcylinder : StandardAG.TranslationStableHomogeneousIdealCylinderGenerators)
    (hcompletion : StandardLattice.PrimitiveDirectionUnimodularCompletion)
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℚ))
    (h : IntVector (n + 1)) (hprimitive : PrimitiveDirection h)
    (hinvariant : RationalIdealTranslationInvariant h I) :
    ∃ (equations : Finset (MvPolynomial (Fin (n + 1)) ℤ))
        (U : IntegralUnimodularChange (n + 1))
        (lowerEquations : Finset (MvPolynomial (Fin n) ℤ)),
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (equations :
            Set (MvPolynomial (Fin (n + 1)) ℤ))) = I ∧
      Matrix.mulVec U.forward h = firstCoordinateIntDirection ∧
      U.transformEquationFinset equations =
          liftEquationFinsetAfterFirst lowerEquations ∧
      (∀ g ∈ lowerEquations, ∃ d : ℕ, g.IsHomogeneous d) ∧
      ∀ x : IntVector (n + 1),
        IntegralCommonZero (liftEquationFinsetAfterFirst lowerEquations)
            (U.pointEquiv x) ↔
          IntegralCommonZero equations x := by
  have hh : h ≠ 0 := by
    intro hhzero
    obtain ⟨i, hi⟩ := hprimitive.exists_ne_zero
    exact hi (congrFun hhzero i)
  obtain ⟨equations, hhomogeneous, hideal, hequationInvariant⟩ :=
    exists_integral_invariant_homogeneous_generators hcylinder I hI h
      hh hinvariant
  obtain ⟨U, lowerEquations, hforward, hfamily, hhomLower, hzero⟩ :=
    exists_unimodular_firstCoordinateEquationReduction hcompletion
      equations hhomogeneous h hprimitive hequationInvariant
  exact ⟨equations, U, lowerEquations, hideal, hforward,
    hfamily, hhomLower, hzero⟩

end

end TranslatedDepthSeven
