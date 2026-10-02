import TranslatedDepthSeven.MarkedProjectionCountingBridge
import TranslatedDepthSeven.AffineChartProjectionMenu
import TranslatedDepthSeven.BoundedHypersurfaceEquation
import TranslatedDepthSeven.GeometricProjectionIrreducibility
import TranslatedDepthSeven.IsolatedVertexCoordinateBridge
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Polynomial.Div

/-!
# The boundary equation of an affine-chart projection

For a projective linear projection whose first coordinate is literally the
homogenizing coordinate, specialization at that coordinate equal to zero
commutes with projection.  Consequently, if the same tail matrix projects
the boundary at infinity birationally onto a hypersurface, the leading form
of the dehomogenized integral image equation is a scalar multiple of the
boundary image equation.

The results in this file are algebraic bridge lemmas.  They do not assert
that a single projection matrix with the required source and boundary
properties exists.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

def optionFirstCoordinateToZero {K : Type*} [CommSemiring K] {n : ℕ} :
    MvPolynomial (Option (Fin n)) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval fun j => match j with
    | none => 0
    | some i => MvPolynomial.X i

@[simp]
theorem optionFirstCoordinateToZero_X_none
    {K : Type*} [CommSemiring K] {n : ℕ} :
    optionFirstCoordinateToZero (K := K) (n := n) (X none) = 0 := by
  simp [optionFirstCoordinateToZero]

@[simp]
theorem optionFirstCoordinateToZero_rename
    {K : Type*} [CommSemiring K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) :
    optionFirstCoordinateToZero (rename some f) = f := by
  change aeval (fun j => match j with
    | none => 0
    | some i => X i) (rename some f) = f
  rw [aeval_rename]
  exact aeval_X_left_apply f

theorem optionFirstCoordinateToZero_multivariateHomogenization
    {K : Type*} [CommSemiring K] {n d : ℕ}
    (f : MvPolynomial (Fin n) K) :
    optionFirstCoordinateToZero (multivariateHomogenization f d) =
      homogeneousComponent d f := by
  classical
  rw [multivariateHomogenization, map_sum]
  rw [Finset.sum_eq_single d]
  · rw [map_mul, map_pow, optionFirstCoordinateToZero_X_none,
      optionFirstCoordinateToZero_rename, Nat.sub_self, pow_zero, one_mul]
  · intro k hk hkd
    have hklt : k < d := by
      simp only [Finset.mem_range, Nat.lt_add_one_iff] at hk
      omega
    have hpos : 0 < d - k := Nat.sub_pos_of_lt hklt
    rw [map_mul, map_pow, optionFirstCoordinateToZero_X_none,
      optionFirstCoordinateToZero_rename]
    rw [zero_pow hpos.ne', zero_mul]
  · simp

theorem optionFirstCoordinateToZero_homogeneousFirstCoordinateRescaling
    {n : ℕ} (c : ℚ) (G : MvPolynomial (Fin (n + 1)) ℚ) :
    optionFirstCoordinateToZero (homogeneousFirstCoordinateRescaling c G) =
      rationalSpecializeFirstCoordinate 0 G := by
  let lhs : MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin n) ℚ :=
    optionFirstCoordinateToZero.comp (homogeneousFirstCoordinateRescaling c)
  have hhom : lhs = rationalSpecializeFirstCoordinate 0 := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [lhs, optionFirstCoordinateToZero,
        homogeneousFirstCoordinateRescaling,
        rationalSpecializeFirstCoordinate]
    · simp [lhs, optionFirstCoordinateToZero,
        homogeneousFirstCoordinateRescaling,
        rationalSpecializeFirstCoordinate]
  exact DFunLike.congr_fun hhom G

theorem homogeneousComponent_rationalSpecializeFirstCoordinate_of_isHomogeneous
    {n degree : ℕ} (c : ℚ)
    {G : MvPolynomial (Fin (n + 1)) ℚ}
    (hG : G.IsHomogeneous degree) :
    homogeneousComponent degree (rationalSpecializeFirstCoordinate c G) =
      rationalSpecializeFirstCoordinate 0 G := by
  let H := homogeneousFirstCoordinateRescaling c G
  have hH : H.IsHomogeneous degree :=
    homogeneousFirstCoordinateRescaling_isHomogeneous c hG
  have hrecover :=
    (multivariateHomogenization_dehomogenization_of_isHomogeneous H hH).2
  have hrecover' := congrArg optionFirstCoordinateToZero hrecover
  rw [optionFirstCoordinateToZero_multivariateHomogenization] at hrecover'
  rw [multivariateDehomogenization_homogeneousFirstCoordinateRescaling] at hrecover'
  rw [optionFirstCoordinateToZero_homogeneousFirstCoordinateRescaling] at hrecover'
  exact hrecover'

theorem map_homogeneousComponent_boundary
    {σ K L : Type*} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (d : ℕ) (p : MvPolynomial σ K) :
    map f (homogeneousComponent d p) = homogeneousComponent d (map f p) := by
  classical
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/-- The leading form of the cleared affine equation is the specialization at
infinity of the homogeneous image equation, up to its nonzero clearing
denominator. -/
theorem integralAffineProjectionTopPart_eq_const_mul_boundary
    {N r degree : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    {G : MvPolynomial (Fin (r + 2)) ℚ}
    (hG : G.IsHomogeneous degree) :
    integralAffineProjectionTopPart A G degree =
      C (mvPolynomialRationalCommonDenominator
          (rationalAffineProjectionEquation A G) : ℚ) *
        rationalSpecializeFirstCoordinate 0 G := by
  let f := rationalAffineProjectionEquation A G
  let D := mvPolynomialRationalCommonDenominator f
  change map (Int.castRingHom ℚ)
      (homogeneousComponent degree (clearRationalMvPolynomial f)) =
    C (D : ℚ) * rationalSpecializeFirstCoordinate 0 G
  rw [map_homogeneousComponent_boundary]
  rw [map_clearRationalMvPolynomial]
  rw [homogeneousComponent_C_mul]
  change C (D : ℚ) * homogeneousComponent degree
      (rationalSpecializeFirstCoordinate
        ((finProjectiveMatrixAsOption A).den : ℚ) G) = _
  rw [homogeneousComponent_rationalSpecializeFirstCoordinate_of_isHomogeneous _ hG]

/-- Reindexing an integral matrix and casting it to `ℚ` introduces no
denominator. -/
@[simp]
theorem finProjectiveMatrixAsOption_map_intCast_den
    {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ) :
    (finProjectiveMatrixAsOption
      (A.map (Int.castRingHom ℚ))).den = 1 := by
  change ((A.submatrix id (finSuccEquiv N).symm).map
    (Int.castRingHom ℚ)).den = 1
  exact Matrix.den_map_intCast _

/-- For an integral projection matrix, the general rational affine equation
is exactly specialization of the homogeneous image equation at `X₀ = 1`.
-/
theorem rationalAffineProjectionEquation_map_intCast
    {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ) :
    rationalAffineProjectionEquation (A.map (Int.castRingHom ℚ)) G =
      rationalSpecializeFirstCoordinate 1 G := by
  unfold rationalAffineProjectionEquation
  rw [finProjectiveMatrixAsOption_map_intCast_den]
  norm_num

theorem integralAffineProjectionEquation_map_intCast
    {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ) :
    integralAffineProjectionEquation (A.map (Int.castRingHom ℚ)) G =
      clearRationalMvPolynomial (rationalSpecializeFirstCoordinate 1 G) := by
  rw [integralAffineProjectionEquation,
    rationalAffineProjectionEquation_map_intCast]

/-- The general top-part construction specializes to the static
affine-chart top part when the matrix already has integral coefficients.
-/
theorem integralAffineProjectionTopPart_map_intCast
    {N r degree : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ) :
    integralAffineProjectionTopPart (A.map (Int.castRingHom ℚ)) G degree =
      map (Int.castRingHom ℚ)
        (homogeneousComponent degree
          (clearRationalMvPolynomial
            (rationalSpecializeFirstCoordinate 1 G))) := by
  rw [integralAffineProjectionTopPart,
    integralAffineProjectionEquation_map_intCast]

theorem integralAffineProjectionTopPart_absolutelyIrreducible_of_boundary
    {N r degree : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    {G : MvPolynomial (Fin (r + 2)) ℚ}
    (hG : G.IsHomogeneous degree)
    (hboundary : Published.IsAbsolutelyIrreducible
      (rationalSpecializeFirstCoordinate 0 G)) :
    Published.IsAbsolutelyIrreducible
      (integralAffineProjectionTopPart A G degree) := by
  rw [integralAffineProjectionTopPart_eq_const_mul_boundary A hG]
  apply hboundary.const_mul
  exact_mod_cast
    (mvPolynomialRationalCommonDenominator_pos
      (rationalAffineProjectionEquation A G)).ne'

/-- The ideal-theoretic hyperplane at infinity of a homogeneous source,
written in the remaining consecutive coordinates. -/
def projectiveBoundaryIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Ideal (MvPolynomial (Fin N) ℚ) :=
  I.map (rationalSpecializeFirstCoordinate 0).toRingHom

/-- The tail matrix induced at infinity by a projective matrix retaining
coordinate zero. -/
def affineChartProjectionBoundaryMatrix {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ) :
    Matrix (Fin (r + 1)) (Fin N) ℚ :=
  fun i j => A i.succ j.succ

/-- Specialization at infinity commutes with a projective linear map whose
first row is the distinguished coordinate. -/
theorem rationalSpecialize_projectiveMatrixPolynomial
    {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (G : MvPolynomial (Fin (r + 2)) ℚ) :
    rationalSpecializeFirstCoordinate 0
        (aeval (StandardAG.projectiveMatrixLinearForm A) G) =
      aeval (StandardAG.projectiveMatrixLinearForm
        (affineChartProjectionBoundaryMatrix A))
        (rationalSpecializeFirstCoordinate 0 G) := by
  let lhs : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin N) ℚ :=
    (rationalSpecializeFirstCoordinate 0).comp
      (MvPolynomial.aeval (StandardAG.projectiveMatrixLinearForm A))
  let rhs : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin N) ℚ :=
    (MvPolynomial.aeval (StandardAG.projectiveMatrixLinearForm
      (affineChartProjectionBoundaryMatrix A))).comp
        (rationalSpecializeFirstCoordinate 0)
  have hhom : lhs = rhs := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · dsimp only [lhs, rhs, AlgHom.comp_apply]
      simp only [aeval_X]
      rw [show rationalSpecializeFirstCoordinate 0 (X (0 : Fin (r + 2))) = 0 by
        simp [rationalSpecializeFirstCoordinate], map_zero]
      change rationalSpecializeFirstCoordinate 0
          (StandardAG.projectiveMatrixLinearForm A 0) = 0
      have hrow : StandardAG.projectiveMatrixLinearForm A 0 = X 0 := by
        rw [StandardAG.projectiveMatrixLinearForm, Fin.sum_univ_succ]
        rw [hfirst.1]
        simp_rw [hfirst.2]
        simp
      rw [hrow]
      simp [rationalSpecializeFirstCoordinate]
    · dsimp only [lhs, rhs, AlgHom.comp_apply]
      simp only [aeval_X]
      rw [show rationalSpecializeFirstCoordinate 0 (X k.succ) = X k by
        simp [rationalSpecializeFirstCoordinate], aeval_X]
      rw [StandardAG.projectiveMatrixLinearForm, Fin.sum_univ_succ]
      simp only [map_add, map_mul]
      simp [rationalSpecializeFirstCoordinate,
        affineChartProjectionBoundaryMatrix,
        StandardAG.projectiveMatrixLinearForm]
  exact DFunLike.congr_fun hhom G

/-- Kernel membership of an image equation specializes to kernel membership
for the tail projection of the boundary. -/
theorem boundary_specialization_mem_projection_kernel
    {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hG : G ∈ RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom) :
    rationalSpecializeFirstCoordinate 0 G ∈ RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap
        (projectiveBoundaryIdeal I)
        (affineChartProjectionBoundaryMatrix A)).toRingHom := by
  have hsource : aeval (StandardAG.projectiveMatrixLinearForm A) G ∈ I := by
    have hz := RingHom.mem_ker.mp hG
    change Ideal.Quotient.mk I
      (aeval (StandardAG.projectiveMatrixLinearForm A) G) = 0 at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hboundary : rationalSpecializeFirstCoordinate 0
      (aeval (StandardAG.projectiveMatrixLinearForm A) G) ∈
        projectiveBoundaryIdeal I :=
    Ideal.mem_map_of_mem (rationalSpecializeFirstCoordinate 0).toRingHom hsource
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk (projectiveBoundaryIdeal I)
    (aeval (StandardAG.projectiveMatrixLinearForm
      (affineChartProjectionBoundaryMatrix A))
      (rationalSpecializeFirstCoordinate 0 G)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← rationalSpecialize_projectiveMatrixPolynomial A hfirst G]
  exact hboundary

/-! ## Automatic nonvanishing at infinity -/

/-- Specializing the first homogeneous coordinate to zero is the constant
coefficient of the same polynomial viewed as a polynomial in that first
coordinate. -/
theorem rationalSpecializeFirstCoordinate_zero_eq_finSuccEquiv_coeff_zero
    {n : ℕ} (G : MvPolynomial (Fin (n + 1)) ℚ) :
    rationalSpecializeFirstCoordinate 0 G =
      (MvPolynomial.finSuccEquiv ℚ n G).coeff 0 := by
  let rhs : MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin n) ℚ :=
    { (Polynomial.constantCoeff.comp
        (MvPolynomial.finSuccEquiv ℚ n).toRingEquiv.toRingHom) with
      commutes' := by
        intro c
        simp [MvPolynomial.finSuccEquiv_apply] }
  have hrhs (f : MvPolynomial (Fin (n + 1)) ℚ) :
      rhs f = (MvPolynomial.finSuccEquiv ℚ n f).coeff 0 := by
    rfl
  rw [← hrhs]
  apply DFunLike.congr_fun
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [rhs, rationalSpecializeFirstCoordinate,
      MvPolynomial.finSuccEquiv_X_zero]
  · simp [rhs, rationalSpecializeFirstCoordinate,
      MvPolynomial.finSuccEquiv_X_succ]

/-- If a homogeneous polynomial vanishes identically after setting its
first coordinate to zero, that coordinate divides the polynomial. -/
theorem X_zero_dvd_of_rationalSpecializeFirstCoordinate_zero
    {n : ℕ} (G : MvPolynomial (Fin (n + 1)) ℚ)
    (hzero : rationalSpecializeFirstCoordinate 0 G = 0) :
    X (0 : Fin (n + 1)) ∣ G := by
  have hc : (MvPolynomial.finSuccEquiv ℚ n G).coeff 0 = 0 := by
    rw [← rationalSpecializeFirstCoordinate_zero_eq_finSuccEquiv_coeff_zero G,
      hzero]
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr hc
  refine ⟨(MvPolynomial.finSuccEquiv ℚ n).symm q, ?_⟩
  apply (MvPolynomial.finSuccEquiv ℚ n).injective
  rw [map_mul, MvPolynomial.finSuccEquiv_X_zero,
    (MvPolynomial.finSuccEquiv ℚ n).apply_symm_apply]
  exact hq

/-- The image equation of a chart-preserving finite birational projection
cannot vanish identically at infinity when the source meets that chart.
Indeed, irreducibility would make it associated to the first target
coordinate, forcing the first source coordinate into the source ideal. -/
theorem rationalSpecializeFirstCoordinate_zero_ne_of_affineChartProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (hX : X (0 : Fin (N + 1)) ∉ I)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hsource : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) I hI A G) :
    rationalSpecializeFirstCoordinate 0 G ≠ 0 := by
  intro hzero
  have hdiv : X (0 : Fin (r + 2)) ∣ G :=
    X_zero_dvd_of_rationalSpecializeFirstCoordinate_zero G hzero
  have hassoc : Associated (X (0 : Fin (r + 2))) G :=
    (MvPolynomial.X_prime.irreducible).associated_of_dvd
      hsource.2.2.2.2.2.1 hdiv
  have htarget : X (0 : Fin (r + 2)) ∈
      RingHom.ker
        (StandardAG.projectiveMatrixCoordinateMap I
          (A.map (Int.castRingHom ℚ))).toRingHom := by
    rw [hsource.2.2.2.1]
    exact Ideal.mem_span_singleton.mpr hassoc.symm.dvd
  have hsourcezero := RingHom.mem_ker.mp htarget
  have hrow : StandardAG.projectiveMatrixLinearForm
      (A.map (Int.castRingHom ℚ)) 0 = X 0 := by
    rw [StandardAG.projectiveMatrixLinearForm, Fin.sum_univ_succ]
    rw [hsource.1.1]
    simp_rw [hsource.1.2]
    simp
  have hsourcezero' :
      StandardAG.projectiveMatrixCoordinateMap I
        (A.map (Int.castRingHom ℚ)) (X 0) = 0 := hsourcezero
  rw [StandardAG.projectiveMatrixCoordinateMap, AlgHom.comp_apply,
    aeval_X, hrow] at hsourcezero'
  exact hX (Ideal.Quotient.eq_zero_iff_mem.mp hsourcezero')

/-- If the source projection and its restriction to the boundary are both
finite birational hypersurface projections of the same degree, then the
specialization at infinity of the source image equation is a nonzero scalar
multiple of the boundary image equation.  Nonvanishing follows internally
from chart preservation, irreducibility, and the source meeting the chart. -/
theorem boundary_specialization_eq_const_mul_of_simultaneousProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (hI : I.IsPrime)
    (hX : X (0 : Fin (N + 2)) ∉ I)
    (A : Matrix (Fin (r + 3)) (Fin (N + 2)) ℤ)
    (G : MvPolynomial (Fin (r + 3)) ℚ)
    (hsource : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) I hI A G)
    (hboundaryPrime : (projectiveBoundaryIdeal I).IsPrime)
    (H : MvPolynomial (Fin (r + 2)) ℚ)
    (hboundary : StandardAG.IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree) (projectiveBoundaryIdeal I) hboundaryPrime
      (affineChartProjectionBoundaryMatrix (A.map (Int.castRingHom ℚ))) H) :
    ∃ c : ℚ, c ≠ 0 ∧
      rationalSpecializeFirstCoordinate 0 G = C c * H := by
  have hGmem : G ∈ RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I
        (A.map (Int.castRingHom ℚ))).toRingHom := by
    rw [hsource.2.2.2.1]
    exact Ideal.mem_span_singleton_self G
  have hGboundaryMem := boundary_specialization_mem_projection_kernel
    I (A.map (Int.castRingHom ℚ)) hsource.1 G hGmem
  have hdiv : H ∣ rationalSpecializeFirstCoordinate 0 G := by
    rw [hboundary.2.2.1] at hGboundaryMem
    exact Ideal.mem_span_singleton.mp hGboundaryMem
  have hGhom : G.IsHomogeneous degree := hsource.2.2.2.2.1
  have hGboundary : rationalSpecializeFirstCoordinate 0 G ≠ 0 :=
    rationalSpecializeFirstCoordinate_zero_ne_of_affineChartProjection
      I hI hX A G hsource
  have hGboundaryHom :
      (rationalSpecializeFirstCoordinate 0 G).IsHomogeneous degree := by
    simpa [rationalSpecializeFirstCoordinate, restrictFirstPolynomialToZero]
      using restrictFirstPolynomialToZero_isHomogeneous hGhom
  have hHhom : H.IsHomogeneous degree := hboundary.2.2.2.1
  have hHne : H ≠ 0 := hboundary.2.2.2.2.1.ne_zero
  exact eq_scalar_mul_of_homogeneous_dvd_same_degree
    hGboundary hHne hGboundaryHom hHhom hdiv

/-- Geometric integrality of the boundary and a simultaneous finite
birational boundary projection make the leading form of the cleared affine
image equation absolutely irreducible. -/
theorem integralAffineProjectionTopPart_absolutelyIrreducible_of_simultaneousBoundaryProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (hI : I.IsPrime)
    (hX : X (0 : Fin (N + 2)) ∉ I)
    (A : Matrix (Fin (r + 3)) (Fin (N + 2)) ℤ)
    (G : MvPolynomial (Fin (r + 3)) ℚ)
    (hsource : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) I hI A G)
    (hboundaryPrime : (projectiveBoundaryIdeal I).IsPrime)
    (hboundaryGeometric :
      GeometricallyPrimeMvPolynomialIdeal (projectiveBoundaryIdeal I))
    (H : MvPolynomial (Fin (r + 2)) ℚ)
    (hboundary : StandardAG.IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree) (projectiveBoundaryIdeal I) hboundaryPrime
      (affineChartProjectionBoundaryMatrix (A.map (Int.castRingHom ℚ))) H) :
    Published.IsAbsolutelyIrreducible
      (integralAffineProjectionTopPart
        (A.map (Int.castRingHom ℚ)) G degree) := by
  obtain ⟨c, hc, hspecialize⟩ :=
    boundary_specialization_eq_const_mul_of_simultaneousProjection
      I hI hX A G hsource hboundaryPrime H hboundary
  have hHne : H ≠ 0 := hboundary.2.2.2.2.1.ne_zero
  have hHabsolute : Published.IsAbsolutelyIrreducible H := by
    apply absolutelyIrreducible_of_ker_eq_span_of_geometricallyPrime
      (projectiveBoundaryIdeal I) hboundaryGeometric
      (StandardAG.projectiveMatrixCoordinateMap
        (projectiveBoundaryIdeal I)
        (affineChartProjectionBoundaryMatrix (A.map (Int.castRingHom ℚ))))
      H hHne
    exact hboundary.2.2.1
  apply integralAffineProjectionTopPart_absolutelyIrreducible_of_boundary
    (A.map (Int.castRingHom ℚ)) hsource.2.2.2.2.1
  rw [hspecialize]
  exact hHabsolute.const_mul c hc

end
end TranslatedDepthSeven
