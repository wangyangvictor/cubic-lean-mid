import TranslatedDepthSeven.HomogeneousProjectionCountingBridge
import TranslatedDepthSeven.SalbergerAffinePacketMembership

/-!
# A bounded affine-chart projection menu

For Salberger's set `S₁` the first target coordinate must literally be one.
Thus an arbitrary homogeneous projection is not sufficient: we use the
standard affine generic projection

`[X₀:X₁:...:X_N] ↦ [X₀:L₁(X):...:L_{r+1}(X)]`.

The external statement below is the bounded-degree form of this classical
construction.  It is strictly weaker than a marked projection theorem: no
local inverse, distinguished source point, or source integral model occurs.

For geometrically integral sources this is exactly the bounded affine
projection of Oscar Marmon, *The density
of integral points on hypersurfaces of degree at least four*, Acta Arith.
141 (2010), Proposition 6.2 and Section 6.1.  For an integral affine
`r`-fold over `Qbar` of degree `d`, Marmon constructs `x ↦ Ax+b`, with integral
coefficients bounded solely in terms of ambient dimension and `d`, which is
birational onto a closed affine hypersurface of degree `d` and has fibres
of size at most `d`.  He further checks that its homogenization extends to a
projective morphism preserving the hyperplane at infinity.  Since the
integer coefficient box is finite, the matrices for all degrees at most a
fixed bound form the menu below.  The proof adapts
Browning--Heath-Brown--Salberger, Duke Math. J. 132 (2006), Section 3.
An explicit centre-at-infinity proof with bounded bad-locus equations is
also given by Castryck--Cluckers--Dittmann--Nguyen, Algebra Number Theory
14 (2020), Proposition 4.3.1 and Section 5 (especially Lemmas 5.2--5.3 and
formula (5.4)).  We use only the ordinary affine birational projection and
fibre bound, not any assertion about separate components at infinity.

This file also records the elementary reason this normalization is the
right one: an integral affine source point `(1,z)` is sent to another
integral affine point `(1,w)`, with no division by a point-dependent
coordinate.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

namespace StandardAG

/-- A finite birational homogeneous projection which preserves the
distinguished affine chart and is represented by an integral matrix. -/
def IsAffineChartFiniteBirationalLinearProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ) : Prop :=
  FirstFinProjectionRowIsHomogenizingCoordinate
      (A.map (Int.castRingHom ℚ)) ∧
    IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree) I hI (A.map (Int.castRingHom ℚ)) G

/-- Degree-uniform finite menu for Marmon's bounded affine projections.  The menu
depends only on ambient dimension, source dimension and the degree bound;
it is chosen before the variety, its coefficients, and every arithmetic
parameter. -/
def BoundedDegreeAffineChartProjectionMenu : Prop :=
  ∀ (N r degreeBound : ℕ), r < N →
    ∃ menu : Finset (Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ),
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (hI : I.IsPrime),
        GeometricallyPrimeMvPolynomialIdeal I →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
        ∀ degree : ℕ,
          HasProjectiveDimensionDegree I r degree →
          degree ≤ degreeBound →
            ∃ A ∈ menu, ∃ G : MvPolynomial (Fin (r + 2)) ℚ,
              IsAffineChartFiniteBirationalLinearProjection
                (degree := degree) I hI A G ∧
              HasProjectiveDimensionDegree
                (RingHom.ker
                  (projectiveMatrixCoordinateMap I
                    (A.map (Int.castRingHom ℚ))).toRingHom)
                r degree

end StandardAG

/-- Maximum integral row mass of one affine-chart projection. -/
def affineChartProjectionCoefficientMass
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ) : ℕ :=
  Finset.univ.sup fun i ↦ ∑ j, (A i j).natAbs

/-- A single row-mass constant for a finite affine projection menu. -/
def affineChartProjectionMenuCoefficientMass
    {N r : ℕ}
    (menu : Finset (Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)) : ℕ :=
  menu.sup affineChartProjectionCoefficientMass

theorem affineChartProjectionCoefficientMass_le_menu
    {N r : ℕ}
    (menu : Finset (Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ))
    {A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ} (hA : A ∈ menu) :
    affineChartProjectionCoefficientMass A ≤
      affineChartProjectionMenuCoefficientMass menu :=
  Finset.le_sup (s := menu) (f := affineChartProjectionCoefficientMass) hA

/-- The literal integral image of an affine source representative under a
chart-preserving integral projection. -/
def integralAffineChartProjection
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (z : IntVector N) : IntVector (r + 2) :=
  Matrix.mulVec A (integralAffineChartVector z)

@[simp]
theorem integralAffineChartProjection_zero
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate
      (A.map (Int.castRingHom ℚ)))
    (z : IntVector N) :
    integralAffineChartProjection A z 0 = 1 := by
  have h00 : A 0 0 = 1 := by
    exact Int.cast_injective (by simpa using hfirst.1)
  have h0j : ∀ j : Fin N, A 0 j.succ = 0 := by
    intro j
    exact Int.cast_injective (by simpa using hfirst.2 j)
  simp only [integralAffineChartProjection, Matrix.mulVec, dotProduct,
    integralAffineChartVector]
  rw [Fin.sum_univ_succ]
  simp [h00, h0j]

/-- Casting the integral affine image gives the rational homogeneous
linear projection of `(1,z)`. -/
theorem intCast_integralAffineChartProjection
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (z : IntVector N) (i : Fin (r + 2)) :
    ((integralAffineChartProjection A z i : ℤ) : ℚ) =
      rationalLinearProjection (A.map (Int.castRingHom ℚ))
        (fun j ↦ (integralAffineChartVector z j : ℚ)) i := by
  simp [integralAffineChartProjection, Matrix.mulVec, dotProduct,
    rationalLinearProjection]

/-- The image hypersurface equation vanishes on the literal integral
affine image of every source point. -/
theorem eval_imageEquation_integralAffineChartProjection_eq_zero
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsAffineChartFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (z : IntVector N)
    (hz : IsRationalConePoint I
      (fun j ↦ (integralAffineChartVector z j : ℚ))) :
    MvPolynomial.eval
        (fun i ↦ (integralAffineChartProjection A z i : ℚ)) G = 0 := by
  have hzero := eval_homogeneousProjectionEquation_eq_zero
    I hI (A.map (Int.castRingHom ℚ)) G hprojection.2
      (fun j ↦ (integralAffineChartVector z j : ℚ)) hz
  rw [show (fun i ↦ (integralAffineChartProjection A z i : ℚ)) =
      rationalLinearProjection (A.map (Int.castRingHom ℚ))
        (fun j ↦ (integralAffineChartVector z j : ℚ)) from by
      funext i
      exact intCast_integralAffineChartProjection A z i]
  exact hzero

/-- Every fibre of the literal affine-chart projection on a finite source
point set has size at most the degree of the source component. -/
theorem integralAffineChartProjection_fibre_card_le_degree
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsAffineChartFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (points : Finset (IntVector N))
    (hsource : ∀ z ∈ points,
      IsRationalConePoint I
        (fun j ↦ (integralAffineChartVector z j : ℚ)))
    (target : IntVector (r + 2)) :
    (points.filter fun z ↦ integralAffineChartProjection A z = target).card ≤
      degree := by
  classical
  let targetQ : Fin (r + 2) → ℚ := fun i ↦ (target i : ℚ)
  let fibre : Set (Fin (N + 1) → ℚ) :=
    {x | IsRationalConePoint I x ∧
      rationalLinearProjection (A.map (Int.castRingHom ℚ)) x = targetQ}
  have hfibre := rationalConeProjection_fibres_of_homogeneousProjection
    I hI (A.map (Int.castRingHom ℚ)) G hprojection.2 targetQ
  have hinjectiveChart : Function.Injective
      (integralAffineChartVector : IntVector N → IntVector (N + 1)) := by
    intro z z' h
    funext i
    have hi := congrFun h i.succ
    simpa using hi
  let sourceMap : IntVector N → Fin (N + 1) → ℚ :=
    fun z j ↦ (integralAffineChartVector z j : ℚ)
  have hsourceMapInjective : Function.Injective sourceMap := by
    exact intVectorToRat_injective.comp hinjectiveChart
  have hmaps : Set.MapsTo sourceMap
      (↑(points.filter fun z ↦ integralAffineChartProjection A z = target) :
        Set (IntVector N))
      fibre := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    refine ⟨hsource z hz'.1, ?_⟩
    funext i
    rw [← intCast_integralAffineChartProjection A z i, congrFun hz'.2 i]
  have hfinite : fibre.Finite := by simpa only [fibre] using hfibre.1
  have hmaps' : Set.MapsTo sourceMap
      (↑(points.filter fun z ↦ integralAffineChartProjection A z = target) :
        Set (IntVector N))
      (↑hfinite.toFinset : Set (Fin (N + 1) → ℚ)) := by
    intro z hz
    exact hfinite.mem_toFinset.mpr (hmaps hz)
  calc
    (points.filter fun z ↦ integralAffineChartProjection A z = target).card ≤
        hfinite.toFinset.card :=
      Finset.card_le_card_of_injOn sourceMap
        hmaps'
        hsourceMapInjective.injOn
    _ = Set.ncard fibre := (Set.ncard_eq_toFinset_card fibre hfinite).symm
    _ ≤ degree := by simpa only [fibre] using hfibre.2

end

end TranslatedDepthSeven
