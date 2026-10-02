import CubicTenVariables.FixedConeSurfaceSliceAggregation
import CubicTenVariables.HomogeneousProgressionBoxCount

/-!
# A fixed-cone reduction from dimensions four and five to surface slices

For a fixed homogeneous cone, a rational matrix supplies the slicing
coordinates.  The fibre over a rational target is the literal ideal obtained
by adjoining the corresponding affine linear equations.  A slicing
certificate records a nonzero discriminant, the actual geometrically prime
three-dimensional affine fibres away from that discriminant (the affine
cones/normalizations attached to projective surface sections), and one fixed
homogeneous exceptional ideal of one lower dimension.

Given a uniform determinant estimate for those good surface fibres, the main
theorem proves the exact translated progression bound required by the n=10
consumer.  Thus the former high-dimensional Salberger premise is reduced to
one explicit fixed-family surface estimate plus the displayed slicing
certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.FixedConeSurfaceSlicingReduction

open MvPolynomial TranslatedDepthSeven Published
open FixedConeSurfaceSliceAggregation
attribute [local instance] MvPolynomial.gradedAlgebra

local instance fixedConeSurfaceSlicingReduction_propDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The affine linear equation defining row `i` of a rational slice. -/
def rationalSliceEquation {n s : ℕ}
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) (i : Fin s) :
    MvPolynomial (Fin n) ℚ :=
  (∑ j, C (A i j) * X j) - C (y i)

@[simp]
theorem eval_rationalSliceEquation {n s : ℕ}
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ)
    (x : Fin n → ℚ) (i : Fin s) :
    eval x (rationalSliceEquation A y i) =
      rationalLinearProjection A x i - y i := by
  simp [rationalSliceEquation, rationalLinearProjection]

/-- The literal ideal of the fibre of `I` over `y`. -/
def rationalSliceIdeal {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ))
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) :
    Ideal (MvPolynomial (Fin n) ℚ) :=
  I ⊔ Ideal.span (Set.range (rationalSliceEquation A y))

/-- Membership in the zero locus of the literal slice ideal is exactly source
membership together with equality of the displayed rational projection. -/
theorem mem_affineZeroLocus_rationalSliceIdeal_iff
    {n s : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ)
    (x : Fin n → ℚ) :
    x ∈ affineIdealZeroLocus (rationalSliceIdeal I A y) ↔
      x ∈ affineIdealZeroLocus I ∧ rationalLinearProjection A x = y := by
  constructor
  · intro hx
    constructor
    · intro f hf
      exact hx f ((show I ≤ rationalSliceIdeal I A y from le_sup_left) hf)
    · funext i
      have heq : rationalSliceEquation A y i ∈ rationalSliceIdeal I A y :=
        (show Ideal.span (Set.range (rationalSliceEquation A y)) ≤
          rationalSliceIdeal I A y from le_sup_right)
          (Ideal.subset_span ⟨i, rfl⟩)
      simpa only [eval_rationalSliceEquation, sub_eq_zero] using
        hx (rationalSliceEquation A y i) heq
  · rintro ⟨hxI, hprojection⟩
    intro f hf
    have hle : rationalSliceIdeal I A y ≤
        RingHom.ker (eval x) := by
      apply sup_le
      · intro g hg
        exact RingHom.mem_ker.mpr (hxI g hg)
      · apply Ideal.span_le.mpr
        intro g hg
        obtain ⟨i, rfl⟩ := hg
        apply RingHom.mem_ker.mpr
        simp only [eval_rationalSliceEquation, congrFun hprojection i, sub_self]
    exact RingHom.mem_ker.mp (hle hf)

/-- A literal fixed rational slicing certificate.

The discriminant and every fibre ideal are concrete polynomials/ideals.  The
exceptional set is contained in one fixed proper homogeneous ideal of affine
dimension at most `r`.  Away from the discriminant, every actual slice is a
geometrically prime affine variety of dimension three and degree at most the
degree of the original cone.  This is the precise standard-AG boundary; it
contains no point-count inequality. -/
structure RationalSurfaceSlicingCertificate
    {n r d : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) where
  matrix : Matrix (Fin (r - 2)) (Fin n) ℚ
  discriminant : MvPolynomial (Fin (r - 2)) ℚ
  discriminant_ne_zero : discriminant ≠ 0
  exceptionalIdeal : Ideal (MvPolynomial (Fin n) ℚ)
  exceptional_proper : exceptionalIdeal ≠ ⊤
  exceptional_homogeneous : exceptionalIdeal.IsHomogeneous
    (homogeneousSubmodule (Fin n) ℚ)
  exceptional_dimension :
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ exceptionalIdeal) ≤
      (r : WithBot ℕ∞)
  bad_mem_exceptional : ∀ x : Fin n → ℚ,
    x ∈ affineIdealZeroLocus I →
    eval (rationalLinearProjection matrix x) discriminant = 0 →
    x ∈ affineIdealZeroLocus exceptionalIdeal
  good_fibre_geometry : ∀ y : Fin (r - 2) → ℚ,
    eval y discriminant ≠ 0 →
    (rationalSliceIdeal I matrix y).IsPrime ∧
    GeometricallyPrimeMvPolynomialIdeal (rationalSliceIdeal I matrix y) ∧
    ∃ e : ℕ, e ≤ d ∧
      HasAffineDimensionDegree (rationalSliceIdeal I matrix y) 3 e

/-- The remaining lower-dimensional analytic/arithmetic endpoint: a single
uniform determinant estimate for the explicit good fibres of one fixed
slicing certificate.  It quantifies over the actual fibre ideal and actual
finite progression points, with the constant chosen before the target,
center, radius, modulus, residue and point set. -/
def GoodSurfaceFibreProgressionEstimate
    {n r d : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (cert : RationalSurfaceSlicingCertificate (r := r) (d := d) I) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (y : Fin (r - 2) → ℚ),
      eval y cert.discriminant ≠ 0 →
    ∀ (S : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
      (L : ℝ), 0 ≤ L →
    ∀ (m : ℕ), 0 < m → ∀ b : Fin n → ℤ,
      (∀ x ∈ S, ∀ i, |(x i : ℝ) - u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i - b i) →
      (∀ x ∈ S, (fun i ↦ (x i : ℚ)) ∈
        affineIdealZeroLocus (rationalSliceIdeal I cert.matrix y)) →
      (S.card : ℝ) ≤
        C * (2 + ‖u‖ + L + (m : ℝ)) ^ ε *
          (1 + L / (m : ℝ)) ^ 2

/-- The former high-dimensional cone estimate follows from the explicit
slicing certificate and the uniform good-surface-fibre estimate.  The proof
sums the actual fibres of the cleared rational matrix and counts all bad
points on the certificate's single fixed exceptional ideal. -/
theorem exists_source_bound_of_surfaceSlicing
    {n r d : ℕ} (hr : 2 ≤ r)
    (I : Ideal (MvPolynomial (Fin n) ℚ))
    (cert : RationalSurfaceSlicingCertificate (r := r) (d := d) I)
    (surface : GoodSurfaceFibreProgressionEstimate I cert)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (S : Finset (Fin n → ℤ)) (u : Fin n → ℝ)
      (L : ℝ), 0 ≤ L →
    ∀ (m : ℕ), 0 < m → ∀ b : Fin n → ℤ,
      (∀ x ∈ S, ∀ i, |(x i : ℝ) - u i| ≤ L) →
      (∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i - b i) →
      (∀ x ∈ S, (fun i ↦ (x i : ℚ)) ∈ affineIdealZeroLocus I) →
      (S.card : ℝ) ≤
        C * (2 + ‖u‖ + L + (m : ℝ)) ^ ε *
          (1 + L / (m : ℝ)) ^ r := by
  classical
  obtain ⟨Csurf, hCsurf, hsurface⟩ := surface ε hε
  obtain ⟨Cexc, hCexc, hexc⟩ :=
    HomogeneousProgressionBoxCount.exists_bound cert.exceptionalIdeal
      cert.exceptional_proper cert.exceptional_homogeneous r
      cert.exceptional_dimension
  let K : ℕ := max 1 (integerProjectionCoefficientBound cert.matrix.num)
  let Abase : ℝ := (7 * (K : ℝ)) ^ (r - 2)
  let C : ℝ := max 1 (Abase * Csurf + Cexc)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro S u L hL m hm b hbox hres hsource
  let slice : (Fin n → ℤ) → (Fin (r - 2) → ℤ) :=
    integralNumeratorLinearProjection cert.matrix
  let target : (Fin (r - 2) → ℤ) → (Fin (r - 2) → ℚ) :=
    rationalTargetOfIntegralNumerator cert.matrix.den
  let good : (Fin (r - 2) → ℤ) → Prop := fun z ↦
    eval (target z) cert.discriminant ≠ 0
  let H : ℝ := 1 + L / (m : ℝ)
  let W : ℝ := 2 + ‖u‖ + L + (m : ℝ)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hH : 1 ≤ H := by
    dsimp [H]
    have hquot : 0 ≤ L / (m : ℝ) := div_nonneg hL hmR.le
    linarith
  have hW : 1 ≤ W := by
    dsimp [W]
    have hunorm : 0 ≤ ‖u‖ := norm_nonneg u
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hbaseAll : ((S.image slice).card : ℝ) ≤ Abase * H ^ (r - 2) := by
    simpa only [slice, K, Abase, H] using
      rationalNumeratorSlice_image_card_cast_le
        cert.matrix S u L hL m hm b hbox hres
  have hbase : (((S.image slice).filter good).card : ℝ) ≤
      Abase * H ^ (r - 2) := by
    have hcardNat := Finset.card_filter_le (S.image slice) good
    have hcardReal : (((S.image slice).filter good).card : ℝ) ≤
        ((S.image slice).card : ℝ) := by
      exact_mod_cast hcardNat
    exact hcardReal.trans hbaseAll
  have hgood : ∀ z ∈ S.image slice, good z →
      ((sliceFiber slice S z).card : ℝ) ≤
        Csurf * W ^ ε * H ^ 2 := by
    intro z _hz hzgood
    apply hsurface (target z) hzgood (sliceFiber slice S z) u L hL m hm b
    · intro x hx i
      exact hbox x (mem_sliceFiber_iff slice S z x |>.mp hx).1 i
    · intro x hx i
      exact hres x (mem_sliceFiber_iff slice S z x |>.mp hx).1 i
    · intro x hx
      obtain ⟨hxS, hxslice⟩ := (mem_sliceFiber_iff slice S z x).mp hx
      apply (mem_affineZeroLocus_rationalSliceIdeal_iff I cert.matrix (target z) _).mpr
      refine ⟨hsource x hxS, ?_⟩
      exact rationalLinearProjection_eq_target_of_integralNumerator_eq
        cert.matrix x z hxslice
  have hexceptional :
      ((S.filter fun x ↦ ¬ good (slice x)).card : ℝ) ≤
        Cexc * H ^ ((r - 2) + 2) := by
    have hcount := hexc (S.filter fun x ↦ ¬ good (slice x))
      u L hL m hm b
      (fun x hx i ↦ hbox x (Finset.mem_filter.mp hx).1 i)
      (fun x hx i ↦ hres x (Finset.mem_filter.mp hx).1 i)
      (fun x hx ↦ by
        obtain ⟨hxS, hxbad⟩ := Finset.mem_filter.mp hx
        apply cert.bad_mem_exceptional (fun i ↦ (x i : ℚ)) (hsource x hxS)
        have hprojection := rationalLinearProjection_eq_target_of_integralNumerator_eq
          cert.matrix x (slice x) rfl
        have hzero : eval (target (slice x)) cert.discriminant = 0 :=
          Classical.byContradiction (fun hne ↦ hxbad hne)
        change eval (rationalLinearProjection cert.matrix (intVectorToRat x))
          cert.discriminant = 0
        rw [hprojection]
        exact hzero)
    have hexponent : (r - 2) + 2 = r := by omega
    simpa only [H, hexponent] using hcount
  have haggregate := card_cast_le_surfaceSlices_add_exceptional
    slice good S (r - 2) H W ε Abase Csurf Cexc
    hH hW hε.le (zero_le_one.trans hCsurf) (zero_le_one.trans hCexc)
    hbase hgood hexceptional
  have hexponent : (r - 2) + 2 = r := by omega
  rw [hexponent] at haggregate
  exact haggregate.trans (by
    gcongr
    exact le_max_right _ _)

end CubicTenVariables.FixedConeSurfaceSlicingReduction
