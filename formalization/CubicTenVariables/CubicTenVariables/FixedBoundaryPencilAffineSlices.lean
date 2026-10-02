import CubicTenVariables.FixedBoundaryPencilUniformity
import CubicTenVariables.FixedIntegralSurfacePointCount
import HessianTheorem11.UnconditionalOrbitIdeal

/-!
# Literal affine slices of the fixed-boundary projective pencil

The projective pencil member at `u⁻¹` and the plane `x₃ = u*x₀`
describe the same plane when `u ≠ 0`. Dehomogenizing the latter gives
exactly `F(1,x,y,u)`. All polynomial identities below are algebraic
substitution identities, so apply over finite fields as well.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedBoundaryPencilAffineSlices

open MvPolynomial TranslatedDepthSeven HessianTheorem11
open HessianTheorem11.PolynomialRestriction
open FixedBoundaryPencilUniformity FixedLeadingFormIntegralShear
open ProjectivePlaneCurveAffineChart
open scoped Matrix

/-- The literal plane `x₃ = u*x₀`, with coordinates `(x₀,x₁,x₂)`. -/
def affinePlaneFrame {R : Type*} [CommRing R] (u : R) : Matrix (Fin 4) (Fin 3) R :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![u, 0, 0]]

/-- The actual two-variable affine equation `F(1,x,y,u)`. -/
def affinePlaneSlice {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin 4) R) (u : R) : MvPolynomial (Fin 2) R :=
  aeval ![1, X 0, X 1, C u] F

theorem map_affinePlaneFrame {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (u : R) : (affinePlaneFrame u).map ρ = affinePlaneFrame (ρ u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [affinePlaneFrame, Matrix.map_apply]

theorem affinePlaneFrame_mulVec {R : Type*} [CommRing R]
    (u : R) (z : Fin 3 → R) :
    (affinePlaneFrame u).mulVec z = ![z 0, z 1, z 2, u * z 0] := by
  ext i
  fin_cases i <;> simp [affinePlaneFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem pencilFrame_mulVec {R : Type*} [CommRing R]
    (t : R) (z : Fin 3 → R) :
    (pencilFrame t).mulVec z = ![t * z 2, z 0, z 1, z 2] := by
  rw [pencilFrame, graphFrame_mulVec]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · fin_cases j <;> rfl

theorem affinePlaneFrame_injective {R : Type*} [CommRing R] (u : R) :
    Function.Injective (affinePlaneFrame u).mulVec := by
  intro x y hxy
  rw [affinePlaneFrame_mulVec, affinePlaneFrame_mulVec] at hxy
  ext i
  fin_cases i
  · exact congrFun hxy 0
  · exact congrFun hxy 1
  · exact congrFun hxy 2

theorem pencilFrame_injective {R : Type*} [CommRing R] (t : R) :
    Function.Injective (pencilFrame t).mulVec := by
  intro x y hxy
  rw [pencilFrame_mulVec, pencilFrame_mulVec] at hxy
  ext i
  fin_cases i
  · exact congrFun hxy 1
  · exact congrFun hxy 2
  · exact congrFun hxy 3

/-- The explicit change of plane coordinates is `(X,Y,Z) ↦ (Y,Z,u*X)`. -/
theorem affinePlaneFrame_range_eq_pencil {K : Type*} [Field K]
    (u : K) (hu : u ≠ 0) :
    LinearMap.range (affinePlaneFrame u).mulVecLin =
      LinearMap.range (pencilFrame u⁻¹).mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    refine ⟨![z 1, z 2, u * z 0], ?_⟩
    change (pencilFrame u⁻¹).mulVec _ = (affinePlaneFrame u).mulVec z
    rw [pencilFrame_mulVec, affinePlaneFrame_mulVec]
    ext i
    fin_cases i <;> simp [hu]
  · rintro _ ⟨z, rfl⟩
    refine ⟨![u⁻¹ * z 2, z 0, z 1], ?_⟩
    change (affinePlaneFrame u).mulVec _ = (pencilFrame u⁻¹).mulVec z
    rw [pencilFrame_mulVec, affinePlaneFrame_mulVec]
    ext i
    fin_cases i <;> simp [hu]

/-- Dehomogenizing this frame is the literal affine slice, as an identity
of polynomial substitution homomorphisms. -/
theorem affinePlaneSlice_eq_dehom {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin 4) R) (u : R) :
    affinePlaneSlice F u = standardDehomogenizationHom R 2 (restrict (affinePlaneFrame u) F) := by
  have he : (aeval (R := R) ![1, X 0, X 1, C u]).toRingHom =
      (standardDehomogenizationHom R 2).comp
        (aeval (linearForms (affinePlaneFrame u))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [standardDehomogenizationHom]
    · intro i
      fin_cases i <;>
        simp [standardDehomogenizationHom, linearForms, affinePlaneFrame, Fin.sum_univ_succ,
          Fin.cases] <;> rfl
  exact RingHom.congr_fun he F

theorem map_affinePlaneSlice {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (F : MvPolynomial (Fin 4) R) (u : R) :
    map ρ (affinePlaneSlice F u) = affinePlaneSlice (map ρ F) (ρ u) := by
  rw [affinePlaneSlice_eq_dehom, affinePlaneSlice_eq_dehom]
  have hc := RingHom.congr_fun (standardDehomogenizationHom_comp_map 2 ρ)
    (restrict (affinePlaneFrame u) F)
  have hc' : standardDehomogenizationHom S 2 (map ρ (restrict (affinePlaneFrame u) F)) =
      map ρ (standardDehomogenizationHom R 2 (restrict (affinePlaneFrame u) F)) := hc
  rw [← hc', map_restrict, map_affinePlaneFrame]

/-- Exact compatibility with the existing numerical slice-counting API. -/
theorem binarySlice_standardDehom_eq
    {K : Type*} [CommRing K] (F : MvPolynomial (Fin 4) K)
    (w : BinarySliceCounting.Complement FixedIntegralSurfacePointCount.planeCoordinates → K) :
    BinarySliceGeometry.slice FixedIntegralSurfacePointCount.planeCoordinates
      (standardDehomogenizationHom K 3 F) w =
      affinePlaneSlice F (FixedIntegralSurfacePointCount.parameterValue w) := by
  let e := FixedIntegralSurfacePointCount.planeCoordinates
  have h1 : Fin.cases (1 : MvPolynomial (Fin 3) K) (fun i => X i) (1 : Fin 4) = X 0 := rfl
  have h2 : Fin.cases (1 : MvPolynomial (Fin 3) K) (fun i => X i) (2 : Fin 4) = X 1 := rfl
  have h3 : Fin.cases (1 : MvPolynomial (Fin 3) K) (fun i => X i) (3 : Fin 4) = X 2 := rfl
  have he : (aeval (BinarySliceCounting.combine e X (fun i => C (w i)))).toRingHom.comp
      (standardDehomogenizationHom K 3) =
      (aeval ![1, X 0, X 1, C (FixedIntegralSurfacePointCount.parameterValue w)]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [standardDehomogenizationHom]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [standardDehomogenizationHom]
      · fin_cases j <;> simp [standardDehomogenizationHom, e,
          FixedIntegralSurfacePointCount.parameterValue, h1, h2, h3]
  exact RingHom.congr_fun he F

/-- Every affine slice is nonzero if the full homogeneous surface is
geometrically integral of degree at least two. -/
theorem affinePlaneSlice_ne_zero_of_geometricDomain
    {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous d)
    (hdegree : F.totalDegree = d)
    (hdom : IsDomain (MvPolynomial (Fin 4) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K)) F})) (u : K) :
    affinePlaneSlice F u ≠ 0 := by
  rw [affinePlaneSlice_eq_dehom]
  apply standardDehomogenization_ne_zero _ (homogeneous_restrict _ _ hF)
  exact FixedIntegralSurfaceAffinePencil.hyperplaneRestriction_ne_zero hd F hdegree hdom
    _ (affinePlaneFrame_injective u)

/-- An irreducible boundary curve of degree at least two prevents every
affine slice from being the zero polynomial, even an exceptional slice. -/
theorem affinePlaneSlice_ne_zero_of_irreducible_boundary
    {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous d)
    (hirr : Irreducible (map (algebraMap K (AlgebraicClosure K))
      (restrict (pencilFrame (0 : K)) F))) (u : K) :
    affinePlaneSlice F u ≠ 0 := by
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  intro hz
  have hAzero : restrict (affinePlaneFrame u) F = 0 := by
    by_contra hne
    apply standardDehomogenization_ne_zero _ (homogeneous_restrict _ _ hF) hne
    rwa [← affinePlaneSlice_eq_dehom]
  have hAzeroL : restrict (affinePlaneFrame (ι u)) (map ι F) = 0 := by
    rw [← map_affinePlaneFrame, ← map_restrict, hAzero, map_zero]
  have hBirr : Irreducible (restrict (pencilFrame (0 : L)) (map ι F)) := by
    simpa only [map_restrict, map_pencilFrame, map_zero] using hirr
  have hBdegree : (restrict (pencilFrame (0 : L)) (map ι F)).totalDegree = d :=
    (homogeneous_restrict _ _ (hF.map ι)).totalDegree hBirr.ne_zero
  have hproj : (LinearMap.proj (2 : Fin 3) : (Fin 3 → L) →ₗ[L] L) ≠ 0 := by
    intro he
    have he' := LinearMap.congr_fun he ![0, 0, 1]
    simp at he'
  have hle := PlaneCubicSingularGeometry.degree_le_one_of_vanishes_on_hyperplane
    _ hBirr (LinearMap.proj (2 : Fin 3)) hproj (by
      intro x hx
      change x 2 = 0 at hx
      have he := congrArg (eval ![0, x 0, x 1]) hAzeroL
      rw [eval_restrict, affinePlaneFrame_mulVec, map_zero] at he
      rw [eval_restrict, pencilFrame_mulVec]
      simpa [hx] using he)
  rw [hBdegree] at hle
  omega

/-- The fixed-boundary interface: a nonzero scalar multiple of one
geometrically irreducible ternary form excludes identically zero slices. -/
theorem affinePlaneSlice_ne_zero_of_boundary
    {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous d)
    (b : K) (k : MvPolynomial (Fin 3) K)
    (hboundary : restrict (pencilFrame (0 : K)) F = C b * k)
    (hb : b ≠ 0)
    (hirr : Irreducible (map (algebraMap K (AlgebraicClosure K)) k))
    (u : K) : affinePlaneSlice F u ≠ 0 := by
  apply affinePlaneSlice_ne_zero_of_irreducible_boundary hd F hF _ u
  rw [hboundary, map_mul, map_C]
  exact (irreducible_isUnit_mul
    ((isUnit_iff_ne_zero.mpr ((map_ne_zero (algebraMap K (AlgebraicClosure K))).2 hb)).map C)).2 hirr

/-- A good member of the projective pencil at `u⁻¹` gives the exact
positive-degree affine geometric-domain hypothesis for `F(1,x,y,u)`. -/
theorem affinePlaneSlice_good_of_pencil
    {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous d)
    (u : K) (hu : u ≠ 0)
    (hdegree : (restrict (pencilFrame u⁻¹) F).totalDegree = d)
    (hdom : IsDomain (MvPolynomial (Fin 3) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K))
        (restrict (pencilFrame u⁻¹) F)})) :
    1 ≤ (affinePlaneSlice F u).totalDegree ∧
      IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
        Ideal.span {map (algebraMap K (AlgebraicClosure K)) (affinePlaneSlice F u)}) := by
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  have huL : ι u ≠ 0 := (map_ne_zero ι).2 hu
  have hBne : restrict (pencilFrame u⁻¹) F ≠ 0 := by
    intro hz
    rw [hz, totalDegree_zero] at hdegree
    omega
  have hBbarne : map ι (restrict (pencilFrame u⁻¹) F) ≠ 0 := by
    exact fun hz => hBne ((map_injective _ ι.injective) (by simpa only [map_zero] using hz))
  have hBirr : Irreducible (restrict (pencilFrame (ι u)⁻¹) (map ι F)) := by
    have hirr := ((Ideal.span_singleton_prime hBbarne).mp
      ((Ideal.Quotient.isDomain_iff_prime _).mp hdom)).irreducible
    simpa only [map_restrict, map_pencilFrame, map_inv₀] using hirr
  have hAirr : Irreducible (restrict (affinePlaneFrame (ι u)) (map ι F)) :=
    FrameRestrictionIrreducibility.irreducible_of_same_range
      _ _ (affinePlaneFrame_injective _) (pencilFrame_injective _)
      (affinePlaneFrame_range_eq_pencil _ huL) _ hBirr
  have hAhom := homogeneous_restrict (affinePlaneFrame (ι u)) (map ι F) (hF.map ι)
  have hAdeg := hAhom.totalDegree hAirr.ne_zero
  have hAdom : IsDomain (MvPolynomial (Fin 3) L ⧸
      Ideal.span {restrict (affinePlaneFrame (ι u)) (map ι F)}) := by
    apply (Ideal.Quotient.isDomain_iff_prime _).mpr
    exact (Ideal.span_singleton_prime hAirr.ne_zero).mpr hAirr.prime
  have hchart := standardDehomogenization_isDomain hd _ hAhom hAdeg hAdom
  have hchartne := standardDehomogenization_ne_zero _ hAhom hAirr.ne_zero
  have hslice : map ι (affinePlaneSlice F u) =
      standardDehomogenizationHom L 2 (restrict (affinePlaneFrame (ι u)) (map ι F)) := by
    rw [map_affinePlaneSlice, affinePlaneSlice_eq_dehom]
  have hgeom : IsDomain (MvPolynomial (Fin 2) L ⧸
      Ideal.span {map ι (affinePlaneSlice F u)}) := by rwa [hslice]
  have hne : affinePlaneSlice F u ≠ 0 := by
    intro hz
    exact hchartne (by rw [← hslice, hz, map_zero])
  exact ⟨FixedIntegralSurfaceAffinePencil.totalDegree_pos_of_geometricDomain _ hne hgeom, hgeom⟩

end CubicTenVariables.FixedBoundaryPencilAffineSlices
