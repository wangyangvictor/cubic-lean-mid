import CubicTenVariables.FixedConeSurfaceSlicingReduction
import TranslatedDepthSeven.AffineChartProjectionBoundaryTopPart
import TranslatedDepthSeven.AffineIdealProjectiveClosureInternal
import TranslatedDepthSeven.AffineProjectiveClosureUniquenessInternal
import TranslatedDepthSeven.PrimeLinearCutFlagDegreeInternal

/-!
# Exact degree of rational surface slices from a Bertini prime flag

The existing surface-slicing certificate records only that a good affine
slice has some degree at most the degree of the source.  Degree equality is
not a formal consequence of final-fibre primality alone in the present
library: one must also control the scheme-theoretic linear intersections.

This file isolates a classical sufficient condition.  Homogenize the affine
equations in the internally constructed projective closure and require that
they form a proper prime flag.  The exact Hilbert-difference theorem then
preserves degree at every cut.  Dehomogenizing the last ideal recovers the
literal `rationalSliceIdeal`, so every good affine threefold has the original
degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

namespace CubicTenVariables.ExactDegreeRationalSurfaceSlicing

open MvPolynomial TranslatedDepthSeven Published
open FixedConeSurfaceSlicingReduction

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogenization of one affine slice equation in the new coordinate zero. -/
def homogeneousRationalSliceEquation {n s : ℕ}
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) (i : Fin s) :
    MvPolynomial (Fin (n + 1)) ℚ :=
  (∑ j, C (A i j) * X j.succ) - C (y i) * X 0

/-- The equation induced at infinity by one affine slice row. -/
def rationalSliceBoundaryEquation {n s : ℕ}
    (A : Matrix (Fin s) (Fin n) ℚ) (i : Fin s) :
    MvPolynomial (Fin n) ℚ :=
  ∑ j, C (A i j) * X j

theorem homogeneousRationalSliceEquation_isHomogeneous {n s : ℕ}
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) (i : Fin s) :
    (homogeneousRationalSliceEquation A y i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sub
  · apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
    intro j _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  · exact MvPolynomial.isHomogeneous_C_mul_X _ _

@[simp]
theorem rationalSpecialize_homogeneousRationalSliceEquation_zero
    {n s : ℕ} (A : Matrix (Fin s) (Fin n) ℚ)
    (y : Fin s → ℚ) (i : Fin s) :
    rationalSpecializeFirstCoordinate 0
        (homogeneousRationalSliceEquation A y i) =
      rationalSliceBoundaryEquation A i := by
  simp [homogeneousRationalSliceEquation, rationalSliceBoundaryEquation,
    rationalSpecializeFirstCoordinate]

/-- The ordered list of the homogenized equations. -/
def rationalProjectiveSliceCuts {n s : ℕ}
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) :
    List (MvPolynomial (Fin (n + 1)) ℚ) :=
  List.ofFn (homogeneousRationalSliceEquation A y)

@[simp]
theorem rationalProjectiveSliceCuts_length {n s : ℕ}
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) :
    (rationalProjectiveSliceCuts A y).length = s := by
  simp [rationalProjectiveSliceCuts]

theorem rationalProjectiveSliceCuts_isHomogeneous {n s : ℕ}
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) :
    ∀ f ∈ rationalProjectiveSliceCuts A y, f.IsHomogeneous 1 := by
  intro f hf
  rw [rationalProjectiveSliceCuts, List.mem_ofFn] at hf
  obtain ⟨i, rfl⟩ := hf
  exact homogeneousRationalSliceEquation_isHomogeneous A y i

/-- The literal projective closure cut by all homogenized affine equations. -/
def rationalProjectiveSliceIdeal {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ))
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) :
    Ideal (MvPolynomial (Fin (n + 1)) ℚ) :=
  affineIdealProjectiveClosure I ⊔
    Ideal.span (Set.range (homogeneousRationalSliceEquation A y))

/-- The boundary of the explicit projective slice is obtained by imposing
the homogeneous row equations.  In particular the affine target `y`
disappears completely. -/
theorem projectiveBoundaryIdeal_rationalProjectiveSliceIdeal
    {n s : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) :
    projectiveBoundaryIdeal (rationalProjectiveSliceIdeal I A y) =
      projectiveBoundaryIdeal (affineIdealProjectiveClosure I) ⊔
        Ideal.span (Set.range (rationalSliceBoundaryEquation A)) := by
  unfold projectiveBoundaryIdeal rationalProjectiveSliceIdeal
  rw [Ideal.map_sup, Ideal.map_span]
  congr 2
  rw [← Set.range_comp]
  congr 1
  funext i
  exact rationalSpecialize_homogeneousRationalSliceEquation_zero A y i

/-- All members of one rational affine slicing family have the same
scheme-theoretic boundary at infinity. -/
theorem projectiveBoundaryIdeal_rationalProjectiveSliceIdeal_independent
    {n s : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (A : Matrix (Fin s) (Fin n) ℚ) (y y' : Fin s → ℚ) :
    projectiveBoundaryIdeal (rationalProjectiveSliceIdeal I A y) =
      projectiveBoundaryIdeal (rationalProjectiveSliceIdeal I A y') := by
  rw [projectiveBoundaryIdeal_rationalProjectiveSliceIdeal,
    projectiveBoundaryIdeal_rationalProjectiveSliceIdeal]

theorem iteratedLinearCutIdeal_rationalProjectiveSliceCuts {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ))
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) :
    iteratedLinearCutIdeal (affineIdealProjectiveClosure I)
        (rationalProjectiveSliceCuts A y) =
      rationalProjectiveSliceIdeal I A y := by
  classical
  rw [iteratedLinearCutIdeal_eq_sup_span_toFinset]
  unfold rationalProjectiveSliceIdeal rationalProjectiveSliceCuts
  congr 2
  ext f
  rw [Finset.mem_coe, List.mem_toFinset, List.mem_ofFn]
  exact Set.mem_range.symm

theorem standardDehomogenizationHom_homogeneousRationalSliceEquation
    {n s : ℕ} (A : Matrix (Fin s) (Fin n) ℚ)
    (y : Fin s → ℚ) (i : Fin s) :
    standardDehomogenizationHom ℚ n
        (homogeneousRationalSliceEquation A y i) =
      rationalSliceEquation A y i := by
  simp [homogeneousRationalSliceEquation, rationalSliceEquation,
    standardDehomogenizationHom]

/-- The standard affine chart of the projective slice is exactly the
original literal affine slice ideal. -/
theorem map_rationalProjectiveSliceIdeal_standardDehomogenization
    {n s : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ) :
    (rationalProjectiveSliceIdeal I A y).map
        (standardDehomogenizationHom ℚ n) =
      rationalSliceIdeal I A y := by
  unfold rationalProjectiveSliceIdeal rationalSliceIdeal
  rw [Ideal.map_sup,
    map_affineIdealProjectiveClosure_standardDehomogenization,
    Ideal.map_span]
  congr 2
  rw [← Set.range_comp]
  congr 1
  funext i
  exact standardDehomogenizationHom_homogeneousRationalSliceEquation A y i

/-- Under the proper-prime flag hypothesis, the explicit homogeneous cut is
literally the kernel-defined projective closure of the affine slice.  This
is the saturation bridge needed by projective affine-chart constructions. -/
theorem rationalProjectiveSliceIdeal_eq_affineIdealProjectiveClosure_of_primeFlag
    {n s : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (hIprime : I.IsPrime)
    (A : Matrix (Fin s) (Fin n) ℚ) (y : Fin s → ℚ)
    (hJprime : (rationalSliceIdeal I A y).IsPrime)
    (hflag : IsProperPrimeLinearCutFlag (affineIdealProjectiveClosure I)
      (rationalProjectiveSliceCuts A y)) :
    rationalProjectiveSliceIdeal I A y =
      affineIdealProjectiveClosure (rationalSliceIdeal I A y) := by
  let cuts := rationalProjectiveSliceCuts A y
  let P := rationalProjectiveSliceIdeal I A y
  have hcutsHom : ∀ f ∈ cuts, f.IsHomogeneous 1 :=
    rationalProjectiveSliceCuts_isHomogeneous A y
  have hPprime : P.IsPrime := by
    have h := iteratedLinearCutIdeal_isPrime
      (affineIdealProjectiveClosure I)
      (affineIdealProjectiveClosure_isPrime I hIprime) cuts hflag
    simpa only [P, cuts,
      iteratedLinearCutIdeal_rationalProjectiveSliceCuts] using h
  have hPhom : P.IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) ℚ) := by
    have h := iteratedLinearCutIdeal_isHomogeneous
      (affineIdealProjectiveClosure I)
      (affineIdealProjectiveClosure_isHomogeneous I) cuts hcutsHom
    simpa only [P, cuts,
      iteratedLinearCutIdeal_rationalProjectiveSliceCuts] using h
  have hchart : P.map (standardDehomogenizationHom ℚ n) =
      rationalSliceIdeal I A y :=
    map_rationalProjectiveSliceIdeal_standardDehomogenization I A y
  have hX : X (0 : Fin (n + 1)) ∉ P := by
    intro hmem
    have hmap := Ideal.mem_map_of_mem
      (standardDehomogenizationHom ℚ n) hmem
    rw [hchart] at hmap
    have hone : (1 : MvPolynomial (Fin n) ℚ) ∈
        rationalSliceIdeal I A y := by
      simpa [standardDehomogenizationHom] using hmap
    exact hJprime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  exact eq_affineIdealProjectiveClosure_of_prime_homogeneous_chart
    (rationalSliceIdeal I A y) hJprime P hPprime hPhom hX hchart

/-- The precise extra Bertini datum needed for exact degree: on every good
fibre, the ordered homogenized equations cut the projective closure through
a proper prime flag. -/
def HasGoodFibreProjectivePrimeFlags
    {n r d : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ))
    (cert : RationalSurfaceSlicingCertificate (r := r) (d := d) I) : Prop :=
  ∀ (y : Fin (r - 2) → ℚ), eval y cert.discriminant ≠ 0 →
    IsProperPrimeLinearCutFlag (affineIdealProjectiveClosure I)
      (rationalProjectiveSliceCuts cert.matrix y)

/-- Certificate-free exact-degree theorem for one literal rational slice.

This is the algebraic core of the good-fibre result below.  It takes only
the chosen rational matrix and target, primality of the literal affine
slice, and the proper projective prime flag.  In particular it can be used
while constructing a `RationalSurfaceSlicingCertificate`, before that
certificate's `good_fibre_geometry` field exists. -/
theorem rationalSliceIdeal_hasAffineDimensionDegree_exact_of_primeFlag
    {N r d : ℕ} (hr : r = 4 ∨ r = 5)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I r d)
    (A : Matrix (Fin (r - 2)) (Fin (N + 1)) ℚ)
    (y : Fin (r - 2) → ℚ)
    (hJprime : (rationalSliceIdeal I A y).IsPrime)
    (hflag : IsProperPrimeLinearCutFlag
      (affineIdealProjectiveClosure I)
      (rationalProjectiveSliceCuts A y)) :
    HasAffineDimensionDegree (rationalSliceIdeal I A y) 3 d := by
  let cuts := rationalProjectiveSliceCuts A y
  let P := rationalProjectiveSliceIdeal I A y
  have hIaffine : HasAffineDimensionDegree I (r + 1) d :=
    hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
      I hIhom hIprime r d hIdegree
  have hclosureDegree : HasProjectiveDimensionDegree
      (affineIdealProjectiveClosure I) (r + 1) d :=
    affineIdealProjectiveClosure_hasProjectiveDimensionDegree I hIaffine
  have hcutsHom : ∀ f ∈ cuts, f.IsHomogeneous 1 := by
    exact rationalProjectiveSliceCuts_isHomogeneous A y
  have hdimension : 3 + cuts.length = r + 1 := by
    dsimp only [cuts]
    rw [rationalProjectiveSliceCuts_length]
    rcases hr with rfl | rfl <;> norm_num
  have hiteratedDegree : HasProjectiveDimensionDegree
      (iteratedLinearCutIdeal (affineIdealProjectiveClosure I) cuts) 3 d :=
    iteratedLinearCutIdeal_preserves_projective_degree
      (affineIdealProjectiveClosure I)
      (affineIdealProjectiveClosure_isPrime I hIprime)
      (affineIdealProjectiveClosure_isHomogeneous I)
      cuts hcutsHom (by simpa only [hdimension] using hclosureDegree) hflag
  have hPdegree : HasProjectiveDimensionDegree P 3 d := by
    simpa only [P, cuts,
      iteratedLinearCutIdeal_rationalProjectiveSliceCuts] using hiteratedDegree
  have hPprime : P.IsPrime := by
    have h := iteratedLinearCutIdeal_isPrime
      (affineIdealProjectiveClosure I)
      (affineIdealProjectiveClosure_isPrime I hIprime) cuts hflag
    simpa only [P, cuts,
      iteratedLinearCutIdeal_rationalProjectiveSliceCuts] using h
  have hPhom : P.IsHomogeneous
      (homogeneousSubmodule (Fin ((N + 1) + 1)) ℚ) := by
    have h := iteratedLinearCutIdeal_isHomogeneous
      (affineIdealProjectiveClosure I)
      (affineIdealProjectiveClosure_isHomogeneous I) cuts hcutsHom
    simpa only [P, cuts,
      iteratedLinearCutIdeal_rationalProjectiveSliceCuts] using h
  have hchart : P.map (standardDehomogenizationHom ℚ (N + 1)) =
      rationalSliceIdeal I A y := by
    exact map_rationalProjectiveSliceIdeal_standardDehomogenization
      I A y
  have hX : X (0 : Fin ((N + 1) + 1)) ∉ P := by
    intro hmem
    have hmap := Ideal.mem_map_of_mem
      (standardDehomogenizationHom ℚ (N + 1)) hmem
    rw [hchart] at hmap
    have hone : (1 : MvPolynomial (Fin (N + 1)) ℚ) ∈
        rationalSliceIdeal I A y := by
      simpa [standardDehomogenizationHom] using hmap
    exact hJprime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  have hPaffine : HasAffineDimensionDegree P 4 d := by
    simpa using
      hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
        P hPhom hPprime 3 d hPdegree
  obtain ⟨q, hq, hchartDegree⟩ :=
    exists_standardAffineChart_dimensionDegree P hPhom hX hPaffine
  have hq3 : q = 3 := by omega
  subst q
  rw [hchart] at hchartDegree
  exact hchartDegree

/-- A proper prime flag proves that the corresponding good affine slice has
the original degree, not merely a degree bounded above by it. -/
theorem good_fibre_hasAffineDimensionDegree_exact
    {N r d : ℕ} (hr : r = 4 ∨ r = 5)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I r d)
    (cert : RationalSurfaceSlicingCertificate (r := r) (d := d) I)
    (hflags : HasGoodFibreProjectivePrimeFlags I cert)
    (y : Fin (r - 2) → ℚ) (hy : eval y cert.discriminant ≠ 0) :
    HasAffineDimensionDegree (rationalSliceIdeal I cert.matrix y) 3 d := by
  exact rationalSliceIdeal_hasAffineDimensionDegree_exact_of_primeFlag
    hr I hIprime hIhom hIdegree cert.matrix y
      (cert.good_fibre_geometry y hy).1 (hflags y hy)

end CubicTenVariables.ExactDegreeRationalSurfaceSlicing
