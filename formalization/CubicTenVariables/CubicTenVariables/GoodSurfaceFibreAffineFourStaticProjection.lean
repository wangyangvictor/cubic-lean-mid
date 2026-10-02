import CubicTenVariables.GoodSurfaceFibreAffineFourProjection
import TranslatedDepthSeven.AffineTransformTopHomogeneousPart
import TranslatedDepthSeven.AffineIdealProjectiveClosureInternal
import TranslatedDepthSeven.BoundedAffineChartProjectionPrimeInternal
import TranslatedDepthSeven.AffineChartProjectionBoundaryTopPart
import TranslatedDepthSeven.AffineChartProjectionSaturatedBoundaryTopPart
import TranslatedDepthSeven.MarkedProjectionCountingBridge

/-!
# Static affine-four projection models

The affine-four adapter previously asked for a new integral equation and
top homogeneous part for every base point and every modulus.  Those data
are elementary consequences of one fixed affine image equation.  This file
records the fixed model and derives the entire dynamic model internally.

The only boundary-at-infinity condition retained is the mathematically
essential one used by Salberger 2023, Theorem 0.4: the fixed image equation
has an absolutely irreducible top homogeneous part.  No translated equation,
translated irreducibility statement, or normalized fibre count is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

namespace CubicTenVariables.GoodSurfaceFibreAffineFourStaticProjection

open MvPolynomial TranslatedDepthSeven Published
open FixedConeSurfaceSlicingReduction
open GoodSurfaceFibreAffineFourProjection

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The fixed affine translation appearing in the image of an affine-chart
projective linear map. -/
def affineProjectionValue
    (offset : IntVector 4) (matrix : Matrix (Fin 4) (Fin 10) ℤ)
    (x : Fin 10 → ℤ) : IntVector 4 :=
  offset + matrix.mulVec x

/-- One static affine hypersurface image of an affine threefold.  The
equation, top form, integral affine map, and fibre bound are chosen once.
The local fibre condition contains no box or global point-count estimate. -/
structure StaticAffineFourHypersurfaceProjectionModel
    (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (degreeBound coefficientBound fibreBound : ℕ) where
  degree : ℕ
  degree_at_least_four : 4 ≤ degree
  degree_le : degree ≤ degreeBound
  matrix : Matrix (Fin 4) (Fin 10) ℤ
  offset : IntVector 4
  matrix_coefficient_bound :
    integerProjectionCoefficientBound matrix ≤ coefficientBound
  equation : MvPolynomial (Fin 4) ℤ
  topPart : MvPolynomial (Fin 4) ℚ
  equation_topPart : IsTopHomogeneousPart equation topPart degree
  topPart_absolutelyIrreducible : IsAbsolutelyIrreducible topPart
  projection_zero : ∀ x : Fin 10 → ℤ,
    (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus J →
      eval (affineProjectionValue offset matrix x) equation = 0
  projection_fibre_card_le : ∀ (S : Finset (Fin 10 → ℤ)),
    (∀ x ∈ S, (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus J) →
    ∀ z : IntVector 4,
      (S.filter fun x ↦ affineProjectionValue offset matrix x = z).card ≤
        fibreBound

/-- The fixed image point about which the static equation is translated. -/
def translatedProjectionBase
    {J : Ideal (MvPolynomial (Fin 10) ℚ)}
    {degreeBound coefficientBound fibreBound : ℕ}
    (model : StaticAffineFourHypersurfaceProjectionModel J
      degreeBound coefficientBound fibreBound)
    (x0 : Fin 10 → ℤ) : IntVector 4 :=
  affineProjectionValue model.offset model.matrix x0

/-- Adding the fixed offset to the normalized linear displacement gives the
exact affine image of the source point. -/
theorem integralAffineMap_translatedProjectionBase_normalizedProjection
    {J : Ideal (MvPolynomial (Fin 10) ℚ)}
    {degreeBound coefficientBound fibreBound : ℕ}
    (model : StaticAffineFourHypersurfaceProjectionModel J
      degreeBound coefficientBound fibreBound)
    (x x0 b : Fin 10 → ℤ) (m : ℕ)
    (hx : ∀ i, (m : ℤ) ∣ x i - b i)
    (hx0 : ∀ i, (m : ℤ) ∣ x0 i - b i) :
    integralAffineMap (translatedProjectionBase model x0)
        (normalizedProjection model.matrix x0 x m) m =
      affineProjectionValue model.offset model.matrix x := by
  have hlinear := integralAffineMap_normalizedProjection
    model.matrix x x0 b m hx hx0
  funext i
  have hi := congrFun hlinear i
  change model.offset i + model.matrix.mulVec x0 i +
      (m : ℤ) * normalizedProjection model.matrix x0 x m i =
    model.offset i + model.matrix.mulVec x i
  calc
    model.offset i + model.matrix.mulVec x0 i +
        (m : ℤ) * normalizedProjection model.matrix x0 x m i =
      model.offset i + (model.matrix.mulVec x0 i +
        (m : ℤ) * normalizedProjection model.matrix x0 x m i) := by ring
    _ = model.offset i + model.matrix.mulVec x i := by
      rw [show model.matrix.mulVec x0 i +
          (m : ℤ) * normalizedProjection model.matrix x0 x m i =
          model.matrix.mulVec x i by
        simpa [integralAffineMap] using hi]

/-- A fibre of the linear part is exactly a fibre of the fixed affine map
after translating the target by the fixed offset. -/
theorem linearProjection_fibre_card_le
    {J : Ideal (MvPolynomial (Fin 10) ℚ)}
    {degreeBound coefficientBound fibreBound : ℕ}
    (model : StaticAffineFourHypersurfaceProjectionModel J
      degreeBound coefficientBound fibreBound)
    (S : Finset (Fin 10 → ℤ))
    (hsource : ∀ x ∈ S,
      (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus J)
    (z : IntVector 4) :
    (S.filter fun x ↦ model.matrix.mulVec x = z).card ≤ fibreBound := by
  have h := model.projection_fibre_card_le S hsource (model.offset + z)
  convert h using 1
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro _hx
  simp only [affineProjectionValue]
  constructor
  · intro heq
    rw [heq]
  · intro heq
    exact add_left_cancel heq

/-- Every base point and modulus-dependent field of the former model is
derived from one fixed affine image equation. -/
def StaticAffineFourHypersurfaceProjectionModel.toDynamic
    {J : Ideal (MvPolynomial (Fin 10) ℚ)}
    {degreeBound coefficientBound fibreBound : ℕ}
    (model : StaticAffineFourHypersurfaceProjectionModel J
      degreeBound coefficientBound fibreBound) :
    AffineFourHypersurfaceProjectionModel J
      degreeBound coefficientBound fibreBound where
  degree := model.degree
  degree_at_least_four := model.degree_at_least_four
  degree_le := model.degree_le
  matrix := model.matrix
  matrix_coefficient_bound := model.matrix_coefficient_bound
  equation x0 m := integralAffineTransform
    (translatedProjectionBase model x0) m model.equation
  topPart _ m := C ((m : ℚ) ^ model.degree) * model.topPart
  equation_topPart := by
    intro x0 _hx0 m hm
    exact isTopHomogeneousPart_integralAffineTransform
      (translatedProjectionBase model x0) hm model.equation_topPart
  topPart_absolutelyIrreducible := by
    intro _x0 _hx0 m hm
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    exact model.topPart_absolutelyIrreducible.const_mul _
      (pow_ne_zero model.degree hmQ)
  normalizedProjection_zero := by
    intro x0 x _hx0 hx m _hm hres
    change MvPolynomial.aeval (normalizedProjection model.matrix x0 x m)
      (integralAffineTransform
        (translatedProjectionBase model x0) m model.equation) = 0
    rw [aeval_integralAffineTransform]
    have hreconstruct :=
      integralAffineMap_translatedProjectionBase_normalizedProjection
        model x x0 x0 m hres (fun i ↦ by simp)
    rw [hreconstruct]
    exact model.projection_zero x hx
  projection_fibre_card_le := by
    intro S hsource z
    exact linearProjection_fibre_card_le model S hsource z

/-- Static models for every good fibre of one fixed slicing certificate. -/
structure GoodFibreStaticAffineFourProjectionModels
    {r d : ℕ} (I : Ideal (MvPolynomial (Fin 10) ℚ))
    (slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I) where
  degreeBound : ℕ
  coefficientBound : ℕ
  fibreBound : ℕ
  coefficientBound_pos : 1 ≤ coefficientBound
  models : ∀ (y : Fin (r - 2) → ℚ),
    eval y slicing.discriminant ≠ 0 →
      StaticAffineFourHypersurfaceProjectionModel
        (rationalSliceIdeal I slicing.matrix y)
        degreeBound coefficientBound fibreBound

/-- Forgetting the static origin produces the former dynamic family. -/
def GoodFibreStaticAffineFourProjectionModels.toDynamic
    {r d : ℕ} {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    {slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I}
    (family : GoodFibreStaticAffineFourProjectionModels I slicing) :
    GoodFibreAffineFourProjectionModels I slicing where
  degreeBound := family.degreeBound
  coefficientBound := family.coefficientBound
  fibreBound := family.fibreBound
  coefficientBound_pos := family.coefficientBound_pos
  models y hy := (family.models y hy).toDynamic

/-- Joint slicing-and-static-model boundary for the actual high-degree
component.  Compared with `AffineFourProjectionModelsN10`, every equation
and irreducibility assertion is now chosen once per fibre. -/
def StaticAffineFourProjectionModelsN10 : Prop :=
  ∀ (I : Ideal (MvPolynomial (Fin 10) ℚ)) (r d : ℕ),
    (r = 4 ∨ r = 5) →
    I.IsPrime →
    GeometricallyPrimeMvPolynomialIdeal I →
    I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ) →
    HasProjectiveDimensionDegree I r d →
    4 ≤ d →
    ∃ slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I,
      Nonempty (GoodFibreStaticAffineFourProjectionModels I slicing)

/-- The static boundary strictly implies the former dynamic boundary. -/
theorem affineFourProjectionModelsN10_of_static
    (models : StaticAffineFourProjectionModelsN10) :
    AffineFourProjectionModelsN10 := by
  intro I r d hr hprime hgeometric hhom hdegree hd
  obtain ⟨slicing, ⟨family⟩⟩ :=
    models I r d hr hprime hgeometric hhom hdegree hd
  exact ⟨slicing, ⟨family.toDynamic⟩⟩

/-! ## Extraction from the internal BHB--Marmon projection -/

/-- The variable part of an integral affine-chart projection. -/
def affineChartProjectionTailMatrix
    (A : Matrix (Fin 5) (Fin 11) ℤ) : Matrix (Fin 4) (Fin 10) ℤ :=
  fun i j ↦ A i.succ j.succ

/-- The constant part of the same affine-chart projection. -/
def affineChartProjectionTailOffset
    (A : Matrix (Fin 5) (Fin 11) ℤ) : IntVector 4 :=
  fun i ↦ A i.succ 0

/-- The fixed integral equation on the four-dimensional affine target. -/
def affineChartProjectionEquation
    (G : MvPolynomial (Fin 5) ℚ) : MvPolynomial (Fin 4) ℤ :=
  clearRationalMvPolynomial (rationalSpecializeFirstCoordinate 1 G)

/-- Its literal rational top homogeneous part. -/
def affineChartProjectionTopPart
    (G : MvPolynomial (Fin 5) ℚ) (degree : ℕ) :
    MvPolynomial (Fin 4) ℚ :=
  map (Int.castRingHom ℚ)
    (homogeneousComponent degree (affineChartProjectionEquation G))

/-- The full homogeneous target on an affine source point is `(1,b+Mx)`. -/
theorem integralAffineChartProjection_eq_firstCoordinate_tail
    (A : Matrix (Fin 5) (Fin 11) ℤ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate
      (A.map (Int.castRingHom ℚ)))
    (x : Fin 10 → ℤ) :
    integralAffineChartProjection A x =
      Fin.cases 1 (affineProjectionValue
        (affineChartProjectionTailOffset A)
        (affineChartProjectionTailMatrix A) x) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact integralAffineChartProjection_zero A hfirst x
  · simp only [integralAffineChartProjection, integralAffineChartVector,
      affineProjectionValue, affineChartProjectionTailOffset,
      affineChartProjectionTailMatrix, Matrix.mulVec, dotProduct,
      Fin.cases_succ, Pi.add_apply]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    ring

/-- An affine zero of `J` is the standard-chart point of its internally
constructed projective closure. -/
theorem isRationalConePoint_affineIdealProjectiveClosure
    (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (x : Fin 10 → ℚ) (hx : x ∈ affineIdealZeroLocus J) :
    IsRationalConePoint (affineIdealProjectiveClosure J)
      (rationalFinStandardAffineRepresentative x) := by
  intro f hf
  apply RingHom.mem_ker.mpr
  change eval (Fin.cases 1 x) f = 0
  rw [← eval_standardDehomogenizationHom]
  apply hx
  have hmap := Ideal.mem_map_of_mem (standardDehomogenizationHom ℚ 10) hf
  rw [map_affineIdealProjectiveClosure_standardDehomogenization] at hmap
  exact hmap

/-- The fixed cleared affine image equation vanishes at every integral
source point. -/
theorem eval_affineChartProjectionEquation_eq_zero
    {degree : ℕ}
    (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (hJ : J.IsPrime)
    (A : Matrix (Fin 5) (Fin 11) ℤ)
    (G : MvPolynomial (Fin 5) ℚ)
    (hprojection : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) (affineIdealProjectiveClosure J)
        (affineIdealProjectiveClosure_isPrime J hJ) A G)
    (x : Fin 10 → ℤ)
    (hx : (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus J) :
    eval (affineProjectionValue
      (affineChartProjectionTailOffset A)
      (affineChartProjectionTailMatrix A) x)
      (affineChartProjectionEquation G) = 0 := by
  let target : IntVector 4 := affineProjectionValue
    (affineChartProjectionTailOffset A)
    (affineChartProjectionTailMatrix A) x
  have hsource : IsRationalConePoint (affineIdealProjectiveClosure J)
      (fun j ↦ (integralAffineChartVector x j : ℚ)) := by
    have h := isRationalConePoint_affineIdealProjectiveClosure J
      (fun i ↦ (x i : ℚ)) hx
    convert h using 1
    funext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;>
      simp [rationalFinStandardAffineRepresentative,
        integralAffineChartVector]
  have hGzero := eval_imageEquation_integralAffineChartProjection_eq_zero
    (affineIdealProjectiveClosure J)
    (affineIdealProjectiveClosure_isPrime J hJ) A G hprojection x hsource
  have htarget := integralAffineChartProjection_eq_firstCoordinate_tail
    A hprojection.1 x
  have hrat : eval (fun i ↦ (target i : ℚ))
      (rationalSpecializeFirstCoordinate 1 G) = 0 := by
    rw [eval_rationalSpecializeFirstCoordinate]
    have hcast : (fun i ↦ (integralAffineChartProjection A x i : ℚ)) =
        Fin.cases 1 (fun i ↦ (target i : ℚ)) := by
      have hcast0 := congrArg
        (fun z : Fin 5 → ℤ ↦ fun i ↦ (z i : ℚ)) htarget
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa [target] using congrFun hcast0 (0 : Fin 5)
      · simpa [target] using congrFun hcast0 j.succ
    rw [← hcast]
    exact hGzero
  have hcast : ((eval target (affineChartProjectionEquation G) : ℤ) : ℚ) = 0 := by
    rw [affineChartProjectionEquation, intCast_eval_clearRationalMvPolynomial,
      hrat, mul_zero]
  exact_mod_cast hcast

/-- The static equation has the advertised top part; nonvanishing is
supplied by the absolute-irreducibility boundary condition. -/
theorem affineChartProjectionEquation_isTopHomogeneousPart
    {degree : ℕ} {G : MvPolynomial (Fin 5) ℚ}
    (hG : G.IsHomogeneous degree)
    (hirr : IsAbsolutelyIrreducible
      (affineChartProjectionTopPart G degree)) :
    IsTopHomogeneousPart (affineChartProjectionEquation G)
      (affineChartProjectionTopPart G degree) degree := by
  refine ⟨rfl, hirr.ne_zero, ?_⟩
  intro k hk
  apply homogeneousComponent_eq_zero
  exact (totalDegree_clearRationalMvPolynomial_le
      (rationalSpecializeFirstCoordinate 1 G)).trans_lt
    ((rationalSpecializeFirstCoordinate_totalDegree_le 1 hG).trans_lt hk)

/-- The affine tail inherits the geometric degree bound on every finite
source set from the internally proved projective projection. -/
theorem affineChartProjectionTail_fibre_card_le_degree
    {degree : ℕ}
    (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (hJ : J.IsPrime)
    (A : Matrix (Fin 5) (Fin 11) ℤ)
    (G : MvPolynomial (Fin 5) ℚ)
    (hprojection : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) (affineIdealProjectiveClosure J)
        (affineIdealProjectiveClosure_isPrime J hJ) A G)
    (S : Finset (Fin 10 → ℤ))
    (hsource : ∀ x ∈ S,
      (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus J)
    (z : IntVector 4) :
    (S.filter fun x ↦ affineProjectionValue
      (affineChartProjectionTailOffset A)
      (affineChartProjectionTailMatrix A) x = z).card ≤ degree := by
  have hsource' : ∀ x ∈ S, IsRationalConePoint
      (affineIdealProjectiveClosure J)
      (fun j ↦ (integralAffineChartVector x j : ℚ)) := by
    intro x hx
    have h := isRationalConePoint_affineIdealProjectiveClosure J
      (fun i ↦ (x i : ℚ)) (hsource x hx)
    convert h using 1
    funext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;>
      simp [rationalFinStandardAffineRepresentative,
        integralAffineChartVector]
  have hfull := integralAffineChartProjection_fibre_card_le_degree
    (affineIdealProjectiveClosure J)
    (affineIdealProjectiveClosure_isPrime J hJ) A G hprojection
      S hsource' (Fin.cases 1 z)
  have hfibre_iff : ∀ x : Fin 10 → ℤ,
      integralAffineChartProjection A x = Fin.cases 1 z ↔
        affineProjectionValue
          (affineChartProjectionTailOffset A)
          (affineChartProjectionTailMatrix A) x = z := by
    intro x
    rw [integralAffineChartProjection_eq_firstCoordinate_tail A hprojection.1]
    constructor
    · intro h
      funext i
      exact congrFun h i.succ
    · intro h
      funext i
      refine Fin.cases rfl (fun j ↦ ?_) i
      exact congrFun h j
  convert hfull using 1
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro _hx
  exact (hfibre_iff x).symm

/-- A BHB--Marmon projection witness whose sole extra property is absolute
irreducibility of the dehomogenized leading form. -/
structure BoundaryIrreducibleAffineFourProjection
    (J : Ideal (MvPolynomial (Fin 10) ℚ)) (degree : ℕ) where
  source_prime : J.IsPrime
  matrix : Matrix (Fin 5) (Fin 11) ℤ
  equation : MvPolynomial (Fin 5) ℚ
  projection : StandardAG.IsAffineChartFiniteBirationalLinearProjection
    (degree := degree) (affineIdealProjectiveClosure J)
      (affineIdealProjectiveClosure_isPrime J source_prime) matrix equation
  boundary_irreducible :
    IsAbsolutelyIrreducible (affineChartProjectionTopPart equation degree)

/-- A simultaneous affine-chart projection of the projective closure and its
boundary at infinity supplies the exact boundary-irreducibility witness used
by the static affine-four model. -/
def BoundaryIrreducibleAffineFourProjection.ofSimultaneousBoundaryProjection
    (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (degree : ℕ)
    (hJ : J.IsPrime)
    (A : Matrix (Fin 5) (Fin 11) ℤ)
    (G : MvPolynomial (Fin 5) ℚ)
    (hsource : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) (affineIdealProjectiveClosure J)
        (affineIdealProjectiveClosure_isPrime J hJ) A G)
    (hboundaryPrime :
      (projectiveBoundaryIdeal (affineIdealProjectiveClosure J)).IsPrime)
    (hboundaryGeometric : GeometricallyPrimeMvPolynomialIdeal
      (projectiveBoundaryIdeal (affineIdealProjectiveClosure J)))
    (H : MvPolynomial (Fin 4) ℚ)
    (hboundary : StandardAG.IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree)
      (projectiveBoundaryIdeal (affineIdealProjectiveClosure J))
      hboundaryPrime
      (affineChartProjectionBoundaryMatrix
        (A.map (Int.castRingHom ℚ))) H) :
    BoundaryIrreducibleAffineFourProjection J degree where
  source_prime := hJ
  matrix := A
  equation := G
  projection := hsource
  boundary_irreducible := by
    have htop :=
      integralAffineProjectionTopPart_absolutelyIrreducible_of_simultaneousBoundaryProjection
        (affineIdealProjectiveClosure J)
        (affineIdealProjectiveClosure_isPrime J hJ)
        (affineIdealProjectiveClosure_X_zero_not_mem J hJ)
        A G hsource hboundaryPrime hboundaryGeometric H hboundary
    change IsAbsolutelyIrreducible
      (map (Int.castRingHom ℚ)
        (homogeneousComponent degree
          (clearRationalMvPolynomial
            (rationalSpecializeFirstCoordinate 1 G))))
    rw [← integralAffineProjectionTopPart_map_intCast A G]
    exact htop

/-- A simultaneous projection to an arbitrary geometrically integral
saturated boundary also supplies the required irreducible leading form.
The literal boundary of the projective closure need only be contained in
the chosen saturation. -/
def BoundaryIrreducibleAffineFourProjection.ofSimultaneousSaturatedBoundaryProjection
    (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (degree : ℕ)
    (hJ : J.IsPrime)
    (B : Ideal (MvPolynomial (Fin 10) ℚ))
    (hboundaryLe :
      projectiveBoundaryIdeal (affineIdealProjectiveClosure J) ≤ B)
    (hBprime : B.IsPrime)
    (hBgeometric : GeometricallyPrimeMvPolynomialIdeal B)
    (A : Matrix (Fin 5) (Fin 11) ℤ)
    (G : MvPolynomial (Fin 5) ℚ)
    (hsource : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) (affineIdealProjectiveClosure J)
        (affineIdealProjectiveClosure_isPrime J hJ) A G)
    (H : MvPolynomial (Fin 4) ℚ)
    (hboundary : StandardAG.IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree) B hBprime
      (affineChartProjectionBoundaryMatrix
        (A.map (Int.castRingHom ℚ))) H) :
    BoundaryIrreducibleAffineFourProjection J degree where
  source_prime := hJ
  matrix := A
  equation := G
  projection := hsource
  boundary_irreducible := by
    have htop :=
      integralAffineProjectionTopPart_absolutelyIrreducible_of_saturatedBoundaryProjection
        (affineIdealProjectiveClosure J) B hboundaryLe
        (affineIdealProjectiveClosure_isPrime J hJ)
        (affineIdealProjectiveClosure_X_zero_not_mem J hJ)
        A G hsource hBprime hBgeometric H hboundary
    change IsAbsolutelyIrreducible
      (map (Int.castRingHom ℚ)
        (homogeneousComponent degree
          (clearRationalMvPolynomial
            (rationalSpecializeFirstCoordinate 1 G))))
    rw [← integralAffineProjectionTopPart_map_intCast A G]
    exact htop

/-- A boundary-compatible BHB--Marmon projection gives the static affine
fourfold model.  All source equations, target translations and finite-fibre
bounds are derived here; the only additional geometric property of the
projection is absolute irreducibility of its leading form at infinity. -/
def BoundaryIrreducibleAffineFourProjection.toStatic
    {J : Ideal (MvPolynomial (Fin 10) ℚ)}
    {degree degreeBound coefficientBound fibreBound : ℕ}
    (witness : BoundaryIrreducibleAffineFourProjection J degree)
    (hdegree4 : 4 ≤ degree)
    (hdegreeBound : degree ≤ degreeBound)
    (hcoefficient : integerProjectionCoefficientBound
      (affineChartProjectionTailMatrix witness.matrix) ≤ coefficientBound)
    (hfibre : degree ≤ fibreBound) :
    StaticAffineFourHypersurfaceProjectionModel J
      degreeBound coefficientBound fibreBound where
  degree := degree
  degree_at_least_four := hdegree4
  degree_le := hdegreeBound
  matrix := affineChartProjectionTailMatrix witness.matrix
  offset := affineChartProjectionTailOffset witness.matrix
  matrix_coefficient_bound := hcoefficient
  equation := affineChartProjectionEquation witness.equation
  topPart := affineChartProjectionTopPart witness.equation degree
  equation_topPart := affineChartProjectionEquation_isTopHomogeneousPart
    witness.projection.2.2.2.2.1 witness.boundary_irreducible
  topPart_absolutelyIrreducible := witness.boundary_irreducible
  projection_zero := by
    intro x hx
    exact eval_affineChartProjectionEquation_eq_zero J witness.source_prime
      witness.matrix witness.equation witness.projection x hx
  projection_fibre_card_le := by
    intro S hsource z
    exact (affineChartProjectionTail_fibre_card_le_degree
      J witness.source_prime witness.matrix witness.equation
        witness.projection S hsource z).trans hfibre

/-! ## The fixed BHB menu and the exact remaining boundary condition -/

/-- The prime-only BHB--Marmon menu specialized to affine threefolds in
ten variables. -/
def affineFourPrimeProjectionMenu (degreeBound : ℕ) :
    Finset (Matrix (Fin 5) (Fin 11) ℤ) :=
  boundedDegreeAffineChartProjectionPrimeMenu 10 3 degreeBound (by omega)

/-- Projective closure plus the internal BHB--Marmon theorem automatically
supplies a finite birational affine-chart projection for every prime affine
threefold, with the same degree and with its matrix in the fixed menu.  No
geometric-primality or boundary-at-infinity premise occurs here. -/
theorem exists_mem_affineFourPrimeProjectionMenu
    {degree degreeBound : ℕ}
    (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (hdegree : HasAffineDimensionDegree J 3 degree)
    (hle : degree ≤ degreeBound) :
    ∃ A ∈ affineFourPrimeProjectionMenu degreeBound,
      ∃ G : MvPolynomial (Fin 5) ℚ,
        StandardAG.IsAffineChartFiniteBirationalLinearProjection
          (degree := degree) (affineIdealProjectiveClosure J)
            (affineIdealProjectiveClosure_isPrime J hdegree.1) A G ∧
        HasProjectiveDimensionDegree
          (RingHom.ker
            (StandardAG.projectiveMatrixCoordinateMap
              (affineIdealProjectiveClosure J)
              (A.map (Int.castRingHom ℚ))).toRingHom)
          3 degree := by
  simpa only [affineFourPrimeProjectionMenu] using
    exists_mem_boundedDegreeAffineChartProjectionPrimeMenu
      10 3 degreeBound (by omega)
      (affineIdealProjectiveClosure J)
      (affineIdealProjectiveClosure_isPrime J hdegree.1)
      (affineIdealProjectiveClosure_isHomogeneous J)
      (affineIdealProjectiveClosure_X_zero_not_mem J hdegree.1)
      degree
      (affineIdealProjectiveClosure_hasProjectiveDimensionDegree J hdegree)
      hle

/-- A boundary-good projection chosen from the already constructed fixed
BHB menu.  The membership field is what gives one coefficient bound for
all fibres. -/
structure MenuBoundaryIrreducibleAffineFourProjection
    (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (degree degreeBound : ℕ) where
  data : BoundaryIrreducibleAffineFourProjection J degree
  matrix_mem : data.matrix ∈ affineFourPrimeProjectionMenu degreeBound

/-- Uniform coefficient bound of the fixed BHB menu, made positive for the
downstream box-counting interface. -/
def affineFourPrimeProjectionCoefficientBound (degreeBound : ℕ) : ℕ :=
  max 1 ((affineFourPrimeProjectionMenu degreeBound).sup fun A ↦
    integerProjectionCoefficientBound (affineChartProjectionTailMatrix A))

theorem affineFourPrimeProjectionCoefficientBound_pos (degreeBound : ℕ) :
    1 ≤ affineFourPrimeProjectionCoefficientBound degreeBound := by
  exact Nat.le_max_left _ _

theorem integerProjectionCoefficientBound_tail_le_menu
    {degreeBound : ℕ} {A : Matrix (Fin 5) (Fin 11) ℤ}
    (hA : A ∈ affineFourPrimeProjectionMenu degreeBound) :
    integerProjectionCoefficientBound (affineChartProjectionTailMatrix A) ≤
      affineFourPrimeProjectionCoefficientBound degreeBound := by
  exact (Finset.le_sup
    (f := fun B ↦ integerProjectionCoefficientBound
      (affineChartProjectionTailMatrix B)) hA).trans (Nat.le_max_right _ _)

/-- A menu boundary witness gives a static model with the uniform menu
coefficient bound and the ambient degree bound as its fibre bound. -/
def MenuBoundaryIrreducibleAffineFourProjection.toStatic
    {J : Ideal (MvPolynomial (Fin 10) ℚ)}
    {degree degreeBound : ℕ}
    (witness : MenuBoundaryIrreducibleAffineFourProjection
      J degree degreeBound)
    (hdegree4 : 4 ≤ degree) (hdegreeBound : degree ≤ degreeBound) :
    StaticAffineFourHypersurfaceProjectionModel J degreeBound
      (affineFourPrimeProjectionCoefficientBound degreeBound) degreeBound :=
  witness.data.toStatic hdegree4 hdegreeBound
    (integerProjectionCoefficientBound_tail_le_menu witness.matrix_mem)
    hdegreeBound

/-- The exact per-slice condition left after projective closure and the
internal BHB construction.  The displayed degree is the actual affine
degree, it is at least four, and one member of the fixed BHB menu has
absolutely irreducible leading form after dehomogenization. -/
structure GoodFibreBoundaryCompatibleAffineFourProjections
    {r d : ℕ} (I : Ideal (MvPolynomial (Fin 10) ℚ))
    (slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I) where
  degree : ∀ (y : Fin (r - 2) → ℚ),
    eval y slicing.discriminant ≠ 0 → ℕ
  degree_at_least_four : ∀ (y : Fin (r - 2) → ℚ)
    (hy : eval y slicing.discriminant ≠ 0), 4 ≤ degree y hy
  degree_le : ∀ (y : Fin (r - 2) → ℚ)
    (hy : eval y slicing.discriminant ≠ 0), degree y hy ≤ d
  affine_dimension_degree : ∀ (y : Fin (r - 2) → ℚ)
    (hy : eval y slicing.discriminant ≠ 0),
      HasAffineDimensionDegree (rationalSliceIdeal I slicing.matrix y)
        3 (degree y hy)
  models : ∀ (y : Fin (r - 2) → ℚ)
    (hy : eval y slicing.discriminant ≠ 0),
      MenuBoundaryIrreducibleAffineFourProjection
        (rationalSliceIdeal I slicing.matrix y) (degree y hy) d

/-- The exact boundary-compatible data produces the static family. -/
def GoodFibreBoundaryCompatibleAffineFourProjections.toStatic
    {r d : ℕ} {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    {slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I}
    (family : GoodFibreBoundaryCompatibleAffineFourProjections I slicing) :
    GoodFibreStaticAffineFourProjectionModels I slicing where
  degreeBound := d
  coefficientBound := affineFourPrimeProjectionCoefficientBound d
  fibreBound := d
  coefficientBound_pos := affineFourPrimeProjectionCoefficientBound_pos d
  models y hy := (family.models y hy).toStatic
    (family.degree_at_least_four y hy) (family.degree_le y hy)

/-- Reduced replacement for the former dynamic projection premise.  Its
only content beyond the slicing certificate and the internally available
BHB projection is simultaneous boundary-good choice in the fixed menu and
the lower bound four for each actual slice degree. -/
def BoundaryCompatibleAffineFourProjectionModelsN10 : Prop :=
  ∀ (I : Ideal (MvPolynomial (Fin 10) ℚ)) (r d : ℕ),
    (r = 4 ∨ r = 5) →
    I.IsPrime →
    GeometricallyPrimeMvPolynomialIdeal I →
    I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ) →
    HasProjectiveDimensionDegree I r d →
    4 ≤ d →
    ∃ slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I,
      Nonempty (GoodFibreBoundaryCompatibleAffineFourProjections I slicing)

theorem staticAffineFourProjectionModelsN10_of_boundaryCompatible
    (models : BoundaryCompatibleAffineFourProjectionModelsN10) :
    StaticAffineFourProjectionModelsN10 := by
  intro I r d hr hprime hgeometric hhom hdegree hd
  obtain ⟨slicing, ⟨family⟩⟩ :=
    models I r d hr hprime hgeometric hhom hdegree hd
  exact ⟨slicing, ⟨family.toStatic⟩⟩

theorem affineFourProjectionModelsN10_of_boundaryCompatible
    (models : BoundaryCompatibleAffineFourProjectionModelsN10) :
    AffineFourProjectionModelsN10 :=
  affineFourProjectionModelsN10_of_static
    (staticAffineFourProjectionModelsN10_of_boundaryCompatible models)


end CubicTenVariables.GoodSurfaceFibreAffineFourStaticProjection
