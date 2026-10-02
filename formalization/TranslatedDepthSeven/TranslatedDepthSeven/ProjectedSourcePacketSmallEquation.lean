import TranslatedDepthSeven.AffineChartProjectionMenu
import TranslatedDepthSeven.PrimitiveBoundedHypersurfaceAlternative
import TranslatedDepthSeven.ProjectedHypersurfaceSalbergerPullback
import TranslatedDepthSeven.BoundedProjectedHypersurfaceCertificate
import TranslatedDepthSeven.HypersurfaceProperDerivative

/-!
# A coefficient-free small equation on a projected source packet

Fix one integral source component and one of Marmon's bounded affine
projections.  We apply the elementary small-equation alternative to the
finite set of projected packet points, before choosing any modulus.

Either the small equation cuts the image hypersurface properly, in which
case its pullback is already the required proper source section, or it is a
primitive defining equation for the exact integral closure of the image.
Only the latter branch needs Salberger.  No height of the original source
component or of its initially displayed image equation occurs.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projected integral affine representative has a coefficient-uniform
box bound. -/
theorem integralAffineChartProjection_coordinate_natAbs_le
    {N r M : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (z : IntVector N) (hz : ∀ j, (z j).natAbs ≤ M) (i : Fin (r + 2)) :
    (integralAffineChartProjection A z i).natAbs ≤
      affineChartProjectionCoefficientMass A * max 1 M := by
  change (∑ j, A i j * integralAffineChartVector z j).natAbs ≤ _
  have hsource : ∀ j : Fin (N + 1),
      (integralAffineChartVector z j).natAbs ≤ max 1 M := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp
    · exact (hz k).trans (Nat.le_max_right 1 M)
  calc
    (∑ j, A i j * integralAffineChartVector z j).natAbs ≤
        ∑ j, (A i j * integralAffineChartVector z j).natAbs :=
      int_natAbs_sum_le_sum_natAbs Finset.univ _
    _ = ∑ j, (A i j).natAbs *
        (integralAffineChartVector z j).natAbs := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Int.natAbs_mul]
    _ ≤ ∑ j, (A i j).natAbs * max 1 M := by
      exact Finset.sum_le_sum fun j _hj ↦
        Nat.mul_le_mul_left (A i j).natAbs (hsource j)
    _ = (∑ j, (A i j).natAbs) * max 1 M := by
      rw [Finset.sum_mul]
    _ ≤ affineChartProjectionCoefficientMass A * max 1 M :=
      Nat.mul_le_mul_right _
        (Finset.le_sup (s := Finset.univ)
          (f := fun i ↦ ∑ j, (A i j).natAbs) (Finset.mem_univ i))

/-- The literal finite image of a source packet. -/
def projectedSourcePacket
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (X : Finset (IntVector N)) : Finset (IntVector (r + 2)) :=
  X.image (integralAffineChartProjection A)

theorem projectedSourcePacket_coordinate_natAbs_le
    {N r M : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (X : Finset (IntVector N))
    (hbox : ∀ z ∈ X, ∀ j, (z j).natAbs ≤ M) :
    ∀ y ∈ projectedSourcePacket A X, ∀ i,
      (y i).natAbs ≤ affineChartProjectionCoefficientMass A * max 1 M := by
  intro y hy i
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  exact integralAffineChartProjection_coordinate_natAbs_le A z (hbox z hz) i

/-- The denominator-cleared image equation vanishes on every projected
packet point. -/
theorem projectedSourcePacket_zero_of_projection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsAffineChartFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (X : Finset (IntVector N))
    (hsource : ∀ z ∈ X, ∀ f ∈ I,
      MvPolynomial.eval
        (fun j ↦ (integralAffineChartVector z j : ℚ)) f = 0) :
    ∀ y ∈ projectedSourcePacket A X,
      MvPolynomial.eval y (clearRationalMvPolynomial G) = 0 := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hGzero := eval_imageEquation_integralAffineChartProjection_eq_zero
    I hI A G hprojection z (hsource z hz)
  have hcast := intCast_eval_clearRationalMvPolynomial G
    (integralAffineChartProjection A z)
  rw [hGzero, mul_zero] at hcast
  exact_mod_cast hcast

/-- Clearing the rational image equation changes its principal ideal only
by a rational unit. -/
theorem span_map_clearRationalMvPolynomial_eq_span
    {N : ℕ} (G : MvPolynomial (Fin N) ℚ) :
    Ideal.span
        {(clearRationalMvPolynomial G).map (Int.castRingHom ℚ)} =
      Ideal.span {G} := by
  rw [map_clearRationalMvPolynomial]
  have hden : (mvPolynomialRationalCommonDenominator G : ℚ) ≠ 0 := by
    exact_mod_cast (mvPolynomialRationalCommonDenominator_pos G).ne'
  exact Ideal.span_singleton_mul_left_unit
    ((isUnit_iff_ne_zero.mpr hden).map MvPolynomial.C) G

/-- The cleared image equation remains irreducible over `ℚ`. -/
theorem irreducible_map_clearRationalMvPolynomial
    {N : ℕ} (G : MvPolynomial (Fin N) ℚ) (hG : Irreducible G) :
    Irreducible
      ((clearRationalMvPolynomial G).map (Int.castRingHom ℚ)) := by
  rw [map_clearRationalMvPolynomial]
  have hden : (mvPolynomialRationalCommonDenominator G : ℚ) ≠ 0 := by
    exact_mod_cast (mvPolynomialRationalCommonDenominator_pos G).ne'
  exact (irreducible_isUnit_mul
    ((isUnit_iff_ne_zero.mpr hden).map MvPolynomial.C)).mpr hG

/-- Static output of the small-equation construction on one fixed source
packet.  The first branch is already a proper source section.  In the
second branch `P` is the exact primitive integral equation of the literal
scheme-theoretic image and is ready for the derivative certificate.
-/
theorem exists_projectedSourcePacket_smallEquation_or_properCut
    {N r degree M : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsAffineChartFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (X : Finset (IntVector N))
    (hsource : ∀ z ∈ X, ∀ f ∈ I,
      MvPolynomial.eval
        (fun j ↦ (integralAffineChartVector z j : ℚ)) f = 0)
    (hbox : ∀ z ∈ X, ∀ j, (z j).natAbs ≤ M) :
    ∃ P : MvPolynomial (Fin (r + 2)) ℤ,
      P ≠ 0 ∧ IsPrimitiveIntegralMvPolynomial P ∧
      P.IsHomogeneous degree ∧
      (∀ z ∈ X,
        MvPolynomial.eval (integralAffineChartProjection A z) P = 0) ∧
      (∀ m, (P.coeff m).natAbs ≤
        (degree + 1) ^ (r + 2) * ((degree + 1) ^ (r + 2)).factorial *
          max 1 (affineChartProjectionCoefficientMass A * max 1 M) ^
            (degree * (degree + 1) ^ (r + 2))) ∧
      ((let F := projectiveMatrixPolynomialPullback
            (A.map (Int.castRingHom ℚ))
            (P.map (Int.castRingHom ℚ))
        F.IsHomogeneous degree ∧ F ∉ I ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun j ↦ (integralAffineChartVector z j : ℚ)) F = 0) ∨
        (Irreducible (P.map (Int.castRingHom ℚ)) ∧
          RingHom.ker
            (StandardAG.projectiveMatrixCoordinateMap I
              (A.map (Int.castRingHom ℚ))).toRingHom =
              Ideal.span {P.map (Int.castRingHom ℚ)} ∧
          projectiveIntegralClosureIdeal
            (RingHom.ker
              (StandardAG.projectiveMatrixCoordinateMap I
                (A.map (Int.castRingHom ℚ))).toRingHom) =
              Ideal.span {P})) := by
  have hGhom : G.IsHomogeneous degree := hprojection.2.2.2.2.1
  have hGirred : Irreducible G := hprojection.2.2.2.2.2.1
  have hclearNe : clearRationalMvPolynomial G ≠ 0 :=
    clearRationalMvPolynomial_ne_zero hGirred.ne_zero
  obtain ⟨P, hP, hprimitive, hPhom, hPzero, hPbound, halt⟩ :=
    exists_bounded_primitive_hypersurface_equation_or_proper_cut
      (clearRationalMvPolynomial G) hclearNe
      (clearRationalMvPolynomial_isHomogeneous hGhom)
      (irreducible_map_clearRationalMvPolynomial G hGirred)
      (projectedSourcePacket A X)
      (projectedSourcePacket_zero_of_projection I hI A G hprojection X
        hsource)
      (projectedSourcePacket_coordinate_natAbs_le A X hbox)
  refine ⟨P, hP, hprimitive, hPhom, ?_, hPbound, ?_⟩
  · intro z hz
    exact hPzero _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  have himage : RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I
        (A.map (Int.castRingHom ℚ))).toRingHom =
        Ideal.span {(clearRationalMvPolynomial G).map
          (Int.castRingHom ℚ)} := by
    rw [span_map_clearRationalMvPolynomial_eq_span]
    exact hprojection.2.2.2.1
  rcases halt with hproper | hdefining
  · left
    let F := projectiveMatrixPolynomialPullback
      (A.map (Int.castRingHom ℚ)) (P.map (Int.castRingHom ℚ))
    have hlinear := hprojection.2.1
    refine ⟨projectiveMatrixPolynomialPullback_isHomogeneous
      (A.map (Int.castRingHom ℚ)) hlinear
        (hPhom.map (Int.castRingHom ℚ)), ?_, ?_⟩
    · apply projectiveMatrixPolynomialPullback_not_mem_source I
        (A.map (Int.castRingHom ℚ))
      rw [himage]
      exact hproper
    · intro z hz
      rw [eval_projectiveMatrixPolynomialPullback]
      have hcoords :
          (fun i ↦ MvPolynomial.eval
            (fun j ↦ (integralAffineChartVector z j : ℚ))
            (StandardAG.projectiveMatrixLinearForm
              (A.map (Int.castRingHom ℚ)) i)) =
            fun i ↦ (integralAffineChartProjection A z i : ℚ) := by
        funext i
        simpa [rationalLinearProjection,
          StandardAG.projectiveMatrixLinearForm] using
            (intCast_integralAffineChartProjection A z i).symm
      rw [hcoords, eval_map_intCast, hPzero _
        (Finset.mem_image.mpr ⟨z, hz, rfl⟩), Int.cast_zero]
  · right
    obtain ⟨c, hc, hscalar⟩ := hdefining.1
    have hunit : IsUnit
        (MvPolynomial.C c : MvPolynomial (Fin (r + 2)) ℚ) :=
      (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
    have hspan : Ideal.span {P.map (Int.castRingHom ℚ)} =
        Ideal.span {(clearRationalMvPolynomial G).map
          (Int.castRingHom ℚ)} := by
      rw [hscalar]
      exact Ideal.span_singleton_mul_left_unit hunit _
    have hPirred : Irreducible (P.map (Int.castRingHom ℚ)) := by
      rw [hscalar]
      exact (irreducible_isUnit_mul hunit).mpr
        (irreducible_map_clearRationalMvPolynomial G hGirred)
    refine ⟨hPirred, himage.trans hspan.symm, ?_⟩
    rw [himage]
    exact hdefining.2

/-! ## The static image-gradient split -/

/-- Affine coordinates of the projected point; the omitted coordinate is
the fixed homogenizing coordinate one. -/
def projectedSourceAffineTail
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (z : IntVector N) : IntVector (r + 1) :=
  fun i ↦ integralAffineChartProjection A z i.succ

theorem integralAffineProjectivePoint_projectedSourceAffineTail
    {N r : ℕ} (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate
      (A.map (Int.castRingHom ℚ)))
    (z : IntVector N) :
    integralAffineProjectivePoint (projectedSourceAffineTail A z) =
      integralAffineChartProjection A z := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact integralAffineChartProjection_zero A hfirst z |>.symm
  · rfl

/-- At a projected point with nonzero image gradient, one spatial partial
derivative gives a bounded integer certificate.  Away from its prime
divisors the literal image hypersurface has Hilbert--Samuel multiplicity
one. -/
theorem exists_projectedSourcePoint_derivativeCertificate
    {N r degree M C : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsAffineChartFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (P : MvPolynomial (Fin (r + 2)) ℤ)
    (hprimitive : IsPrimitiveIntegralMvPolynomial P)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (hPhom : P.IsHomogeneous degree)
    (hPcoeff : ∀ m, (P.coeff m).natAbs ≤ C)
    (himage : RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I
        (A.map (Int.castRingHom ℚ))).toRingHom =
        Ideal.span {P.map (Int.castRingHom ℚ)})
    (z : IntVector N) (hbox : ∀ i, (z i).natAbs ≤ M)
    (hPzero : MvPolynomial.eval (integralAffineChartProjection A z) P = 0)
    (hgradient : ∃ i,
      MvPolynomial.eval (integralAffineChartProjection A z)
        (MvPolynomial.pderiv i P) ≠ 0) :
    ∃ j : Fin (r + 1),
      let Δ : ℤ := MvPolynomial.eval (integralAffineChartProjection A z)
        (MvPolynomial.pderiv j.succ P)
      Δ ≠ 0 ∧
      Δ.natAbs ≤ (degree + 1) ^ (r + 2) * degree * C *
        max 1 (affineChartProjectionCoefficientMass A * max 1 M) ^ degree ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
        HasHilbertSamuelMultiplicityAt hp
          (projectiveSpecialFiberIdeal
            (RingHom.ker
              (StandardAG.projectiveMatrixCoordinateMap I
                (A.map (Int.castRingHom ℚ))).toRingHom))
          (fun i ↦ (integralAffineChartProjection A z i : ZMod p)) r 1 := by
  let tail := projectedSourceAffineTail A z
  have hfull : integralAffineProjectivePoint tail =
      integralAffineChartProjection A z :=
    integralAffineProjectivePoint_projectedSourceAffineTail A
      hprojection.1 z
  have hR : ∀ i, (tail i).natAbs ≤
      affineChartProjectionCoefficientMass A * max 1 M := by
    intro i
    exact integralAffineChartProjection_coordinate_natAbs_le A z hbox i.succ
  obtain ⟨j, hΔ, hΔbound, hmultiplicity⟩ :=
    exists_bounded_projectedHypersurface_derivative_certificate
      P hprimitive hPirred hPhom hPcoeff tail
      (R := max 1 (affineChartProjectionCoefficientMass A * max 1 M))
      (Nat.le_max_left _ _) (fun i ↦ (hR i).trans (Nat.le_max_right _ _))
      (by simpa only [hfull] using hPzero)
      (by simpa only [hfull] using hgradient)
  refine ⟨j, ?_, ?_, ?_⟩
  · simpa only [hfull] using hΔ
  · have hmax :
        max 1 (max 1
          (affineChartProjectionCoefficientMass A * max 1 M)) =
            max 1 (affineChartProjectionCoefficientMass A * max 1 M) :=
      max_eq_right (Nat.le_max_left _ _)
    rw [hmax] at hΔbound
    simpa only [hfull] using hΔbound
  · intro p hp hpd
    rw [himage]
    simpa only [hfull] using hmultiplicity p hp (by simpa only [hfull] using hpd)

/-- All points where the projected image gradient vanishes lie on one
fixed proper derivative section of the source.  The derivative coordinate
is selected from the polynomial, not from the individual point. -/
theorem exists_properSourceCut_vanishing_on_projectedSingularPoints
    {N r degree : ℕ} (hdegree : 0 < degree)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsAffineChartFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (P : MvPolynomial (Fin (r + 2)) ℤ)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (hPhom : P.IsHomogeneous degree)
    (himage : RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I
        (A.map (Int.castRingHom ℚ))).toRingHom =
        Ideal.span {P.map (Int.castRingHom ℚ)}) :
    ∃ j : Fin (r + 2),
      let F := projectiveMatrixPolynomialPullback
        (A.map (Int.castRingHom ℚ))
        (MvPolynomial.pderiv j (P.map (Int.castRingHom ℚ)))
      F.IsHomogeneous (degree - 1) ∧ F ∉ I ∧
        ∀ z : IntVector N,
          (∀ i, MvPolynomial.eval (integralAffineChartProjection A z)
            (MvPolynomial.pderiv i P) = 0) →
          MvPolynomial.eval
            (fun k ↦ (integralAffineChartVector z k : ℚ)) F = 0 := by
  obtain ⟨j, hjne, hjproper⟩ :=
    exists_proper_partial_of_positive_homogeneous
      (P.map (Int.castRingHom ℚ)) hPirred.ne_zero
      (hPhom.map (Int.castRingHom ℚ)) hdegree
  refine ⟨j,
    projectiveMatrixPolynomialPullback_isHomogeneous
      (A.map (Int.castRingHom ℚ)) hprojection.2.1
      (hPhom.map (Int.castRingHom ℚ)).pderiv,
    ?_, ?_⟩
  · apply projectiveMatrixPolynomialPullback_not_mem_source I
      (A.map (Int.castRingHom ℚ))
    rw [himage]
    exact hjproper
  · intro z hsingular
    rw [eval_projectiveMatrixPolynomialPullback]
    have hcoords :
        (fun i ↦ MvPolynomial.eval
          (fun k ↦ (integralAffineChartVector z k : ℚ))
          (StandardAG.projectiveMatrixLinearForm
            (A.map (Int.castRingHom ℚ)) i)) =
          fun i ↦ (integralAffineChartProjection A z i : ℚ) := by
      funext i
      simpa [rationalLinearProjection,
        StandardAG.projectiveMatrixLinearForm] using
          (intCast_integralAffineChartProjection A z i).symm
    rw [hcoords, MvPolynomial.pderiv_map, eval_map_intCast, hsingular j,
      Int.cast_zero]

end

end TranslatedDepthSeven
