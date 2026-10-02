import CubicTenVariables.FixedLeadingSurfaceLineDirectionSum
import TranslatedDepthSeven.AffineTransformTopHomogeneousPart
import TranslatedDepthSeven.EquationFamilyProjectiveTangentSpace
import TranslatedDepthSeven.AffineChartProjectionBoundaryTopPart

/-!
# Directions of actual affine lines lie on the fixed leading curve

The top coefficient of the existing literal line polynomial is extracted
using the existing star-coefficient identities. Vanishing on infinitely
many rational parameters suffices. Projective incidence is stated for the
actual projective class and its chosen representative, including every
polynomial in the principal homogeneous ideal used by the counting API.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceLineDirectionIncidence
open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceLineDirectionSum
open scoped LinearAlgebra.Projectivization

variable {n d : ℕ}

/-- Exact leading coefficient of the actual integral affine-line restriction. -/
theorem linePolynomial_coeff_top
    (g : MvPolynomial (Fin n) ℤ) (base v : IntVector n)
    (hdegree : g.totalDegree ≤ d) :
    (linePolynomial g base v).coeff d = eval v (homogeneousComponent d g) := by
  rw [← eval_starCoefficient,
    starCoefficient_eq_homogeneousComponent_of_totalDegree_le base g hdegree]

/-- Infinitely many rational zeros force the actual integral line
restriction to be the zero polynomial. -/
theorem linePolynomial_eq_zero_of_infinite_rational_zeros
    (g : MvPolynomial (Fin n) ℤ) (base v : IntVector n)
    (hzeros : Set.Infinite {t : ℚ |
      eval (fun i => (base i : ℚ) + t * (v i : ℚ)) (map (Int.castRingHom ℚ) g) = 0}) :
    linePolynomial g base v = 0 := by
  have he : (linePolynomial g base v).map (Int.castRingHom ℚ) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    simpa only [Polynomial.IsRoot, eval_map_linePolynomial_at_rat] using hzeros
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simpa only [Polynomial.map_zero] using he

/-- In particular, literal containment of the whole rational affine line
implies the polynomial identity. -/
theorem linePolynomial_eq_zero_of_all_rational_parameters
    (g : MvPolynomial (Fin n) ℤ) (base v : IntVector n)
    (hline : ∀ t : ℚ,
      eval (fun i => (base i : ℚ) + t * (v i : ℚ)) (map (Int.castRingHom ℚ) g) = 0) :
    linePolynomial g base v = 0 := by
  apply linePolynomial_eq_zero_of_infinite_rational_zeros g base v
  have hs : {t : ℚ |
      eval (fun i => (base i : ℚ) + t * (v i : ℚ)) (map (Int.castRingHom ℚ) g) = 0} =
      Set.univ := by
    ext t
    exact ⟨fun _ => Set.mem_univ t, fun _ => hline t⟩
  rw [hs]
  exact Set.infinite_univ

/-- The direction of a contained line annihilates the fixed leading form;
the scalar and all lower coefficients are eliminated explicitly. -/
theorem eval_fixed_leading_form_eq_zero_of_linePolynomial_eq_zero
    (g k : MvPolynomial (Fin n) ℤ) (base v : IntVector n) {c : ℚ}
    (hdegree : (map (Int.castRingHom ℚ) g).totalDegree ≤ d)
    (hc : c ≠ 0)
    (htop : homogeneousComponent d (map (Int.castRingHom ℚ) g) =
      C c * map (Int.castRingHom ℚ) k)
    (hline : linePolynomial g base v = 0) :
    eval (fun i => (v i : ℚ)) (map (Int.castRingHom ℚ) k) = 0 := by
  have hdeg : g.totalDegree ≤ d := by
    simpa only [totalDegree,
      support_map_of_injective g (f := Int.castRingHom ℚ) Int.cast_injective] using hdegree
  have hzero : eval v (homogeneousComponent d g) = 0 := by
    rw [← linePolynomial_coeff_top g base v hdeg, hline]
    exact Polynomial.coeff_zero d
  have hcast := MvPolynomial.map_eval (Int.castRingHom ℚ) v (homogeneousComponent d g)
  rw [hzero, map_zero, map_homogeneousComponent_boundary] at hcast
  have hzeroQ : eval (fun i => (v i : ℚ))
      (homogeneousComponent d (map (Int.castRingHom ℚ) g)) = 0 := hcast.symm
  rw [htop, map_mul, eval_C] at hzeroQ
  exact (mul_eq_zero.mp hzeroQ).resolve_left hc

/-- Homogeneity carries direction vanishing to the actual representative
chosen by Projectivization.rep. -/
theorem eval_directionClass_rep_eq_zero
    (k : MvPolynomial (Fin n) ℚ) (hk : k.IsHomogeneous d)
    (v : IntVector n) (hp : PrimitiveDirection v)
    (hzero : eval (fun i => (v i : ℚ)) k = 0) :
    eval (directionClass v hp).rep k = 0 := by
  let w : Fin n → ℚ := fun i => (v i : ℚ)
  have hw : w ≠ 0 := intCast_ne_zero (primitiveDirection_ne_zero hp)
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℚ w hw
  have hre : (a : ℚ) • w = (Projectivization.mk ℚ w hw).rep := by simpa using ha
  change eval (Projectivization.mk ℚ w hw).rep k = 0
  rw [← hre]
  change eval (fun i => (a : ℚ) * w i) k = 0
  rw [eval_smul_of_isHomogeneous k w (a : ℚ) d hk, hzero, mul_zero]

/-- A zero of the displayed equation is a zero of every polynomial in its
literal principal ideal. -/
theorem eval_eq_zero_on_span_singleton
    {K σ : Type*} [CommRing K] (x : σ → K) (k : MvPolynomial σ K)
    (hk : eval x k = 0) :
    ∀ f ∈ Ideal.span {k}, eval x f = 0 := by
  have hle : Ideal.span {k} ≤ RingHom.ker (eval x) := by
    apply Ideal.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    exact hk
  intro f hf
  exact hle hf

/-- This is precisely the direction-incidence hypothesis consumed by the
active-line summation theorem, for the fixed principal leading ideal. -/
theorem directionClass_vanishes_on_fixed_leading_ideal
    (g k : MvPolynomial (Fin n) ℤ) (hk : k.IsHomogeneous d)
    (base v : IntVector n) (hp : PrimitiveDirection v) {c : ℚ}
    (hdegree : (map (Int.castRingHom ℚ) g).totalDegree ≤ d)
    (hc : c ≠ 0)
    (htop : homogeneousComponent d (map (Int.castRingHom ℚ) g) =
      C c * map (Int.castRingHom ℚ) k)
    (hline : linePolynomial g base v = 0) :
    ∀ f ∈ Ideal.span {map (Int.castRingHom ℚ) k},
      eval (directionClass v hp).rep f = 0 := by
  apply eval_eq_zero_on_span_singleton
  apply eval_directionClass_rep_eq_zero _ (hk.map (Int.castRingHom ℚ)) v hp
  exact eval_fixed_leading_form_eq_zero_of_linePolynomial_eq_zero
    g k base v hdegree hc htop hline

/-- Literal bounded rational-point membership, including the published
primitive height convention. -/
theorem directionClass_mem_rationalProjectivePoints
    (g k : MvPolynomial (Fin (n + 1)) ℤ) (hk : k.IsHomogeneous d)
    (base v : IntVector (n + 1)) (hp : PrimitiveDirection v) {c : ℚ}
    (hdegree : (map (Int.castRingHom ℚ) g).totalDegree ≤ d)
    (hc : c ≠ 0)
    (htop : homogeneousComponent d (map (Int.castRingHom ℚ) g) =
      C c * map (Int.castRingHom ℚ) k)
    (hline : linePolynomial g base v = 0)
    (B : ℝ) (hheight : (directionHeight v : ℝ) ≤ B) :
    directionClass v hp ∈ rationalProjectivePoints
      (Ideal.span {map (Int.castRingHom ℚ) k}) B := by
  refine ⟨directionClass_vanishes_on_fixed_leading_ideal
    g k hk base v hp hdegree hc htop hline, ?_⟩
  rw [height_directionClass]
  exact hheight

/-- For a whole finite or infinite indexed family of actual contained
lines, the fixed-curve direction source is now proved, not assumed. -/
theorem family_direction_incidence_of_contained_lines
    {ι : Type*} (g k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (base v : ι → IntVector 3) (hp : ∀ l, PrimitiveDirection (v l)) {c : ℚ}
    (hdegree : (map (Int.castRingHom ℚ) g).totalDegree ≤ d)
    (hc : c ≠ 0)
    (htop : homogeneousComponent d (map (Int.castRingHom ℚ) g) =
      C c * map (Int.castRingHom ℚ) k)
    (hline : ∀ l, linePolynomial g (base l) (v l) = 0) :
    ∀ l, ∀ f ∈ Ideal.span {map (Int.castRingHom ℚ) k},
      eval (directionClass (v l) (hp l)).rep f = 0 := by
  intro l
  exact directionClass_vanishes_on_fixed_leading_ideal
    g k hk (base l) (v l) (hp l) hdegree hc htop (hline l)

end CubicTenVariables.FixedLeadingSurfaceLineDirectionIncidence
