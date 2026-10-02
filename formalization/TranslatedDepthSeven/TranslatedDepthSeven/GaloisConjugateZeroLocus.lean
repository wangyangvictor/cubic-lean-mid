import TranslatedDepthSeven.FiniteFamilyHomogenization
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Conjugation of literal finite polynomial zero loci

Let `K` be a field over `ℚ` and let `g : K ≃ₐ[ℚ] K`.  This file applies `g`
coefficientwise to a literal finite polynomial family and coordinatewise to
its points.  Evaluation commutes with these two operations.  Consequently a
point on a finite affine zero locus is carried to the conjugate zero locus.

For homogeneous equations the coordinatewise semilinear equivalence induces
an actual map of Mathlib projective spaces, and the analogous transport result
holds there.  Since a `ℚ`-algebra automorphism fixes every rational
coordinate, a rational point of either locus belongs to every conjugate
locus.  The final statements record this as membership in the intersection
with the conjugate; they do not need, and do not assert, that the conjugate is
distinct.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

open MvPolynomial Finset

universe u v

variable {K : Type u} {ι : Type v} [Field K] [Algebra ℚ K]

/-- Coefficientwise application of a `ℚ`-algebra automorphism to a
multivariable polynomial. -/
def conjugatePolynomial (g : K ≃ₐ[ℚ] K) :
    MvPolynomial ι K ≃+* MvPolynomial ι K :=
  MvPolynomial.mapEquiv ι g.toRingEquiv

@[simp]
theorem conjugatePolynomial_apply (g : K ≃ₐ[ℚ] K)
    (f : MvPolynomial ι K) :
    conjugatePolynomial g f = MvPolynomial.map g.toRingHom f :=
  rfl

/-- The literal finite family of coefficientwise conjugate equations. -/
def conjugateEquationFamily (g : K ≃ₐ[ℚ] K)
    (equations : Finset (MvPolynomial ι K)) :
    Finset (MvPolynomial ι K) := by
  classical
  exact equations.image (conjugatePolynomial g)

@[simp]
theorem mem_conjugateEquationFamily_iff (g : K ≃ₐ[ℚ] K)
    (equations : Finset (MvPolynomial ι K)) (f : MvPolynomial ι K) :
    f ∈ conjugateEquationFamily g equations ↔
      ∃ f₀ ∈ equations, conjugatePolynomial g f₀ = f := by
  classical
  simp [conjugateEquationFamily]

/-- Coordinatewise conjugation of an affine point. -/
def conjugatePoint (g : K ≃ₐ[ℚ] K) (x : ι → K) : ι → K :=
  fun i ↦ g (x i)

/-- Evaluation is compatible with simultaneous coefficientwise and
coordinatewise conjugation. -/
theorem eval_conjugatePolynomial (g : K ≃ₐ[ℚ] K)
    (x : ι → K) (f : MvPolynomial ι K) :
    MvPolynomial.eval (conjugatePoint g x) (conjugatePolynomial g f) =
      g (MvPolynomial.eval x f) := by
  simpa [conjugatePoint, conjugatePolynomial_apply, Function.comp_def] using
    (MvPolynomial.map_eval g.toRingHom x f).symm

/-- Coordinatewise conjugation carries the affine common zero locus to the
common zero locus of the conjugate finite equation family. -/
theorem conjugatePoint_mem_finiteAffineCommonZeroLocus
    (g : K ≃ₐ[ℚ] K) (equations : Finset (MvPolynomial ι K))
    {x : ι → K} (hx : x ∈ finiteAffineCommonZeroLocus equations) :
    conjugatePoint g x ∈
      finiteAffineCommonZeroLocus (conjugateEquationFamily g equations) := by
  classical
  intro f hf
  obtain ⟨f₀, hf₀, rfl⟩ :=
    (mem_conjugateEquationFamily_iff g equations f).mp hf
  rw [eval_conjugatePolynomial, hx f₀ hf₀, map_zero]

/-- A `ℚ`-algebra automorphism fixes a point obtained by extending rational
coordinates to `K`. -/
theorem conjugatePoint_algebraMap (g : K ≃ₐ[ℚ] K) (x : ι → ℚ) :
    conjugatePoint g (fun i ↦ algebraMap ℚ K (x i)) =
      (fun i ↦ algebraMap ℚ K (x i)) := by
  funext i
  exact g.commutes (x i)

/-- Hence an affine point with rational coordinates which lies on the
original finite zero locus also lies on every conjugate finite zero locus. -/
theorem rationalPoint_mem_conjugateFiniteAffineCommonZeroLocus
    (g : K ≃ₐ[ℚ] K) (equations : Finset (MvPolynomial ι K))
    (x : ι → ℚ)
    (hx : (fun i ↦ algebraMap ℚ K (x i)) ∈
      finiteAffineCommonZeroLocus equations) :
    (fun i ↦ algebraMap ℚ K (x i)) ∈
      finiteAffineCommonZeroLocus (conjugateEquationFamily g equations) := by
  have hconj := conjugatePoint_mem_finiteAffineCommonZeroLocus g equations hx
  rwa [conjugatePoint_algebraMap] at hconj

/-- Precise affine intersection consequence.  No distinctness hypothesis on
the conjugate is required; if distinctness is known separately, this says
that every rational point lies in the intersection of the two distinct
loci. -/
theorem rationalPoint_mem_finiteAffineCommonZeroLocus_inter_conjugate
    (g : K ≃ₐ[ℚ] K) (equations : Finset (MvPolynomial ι K))
    (x : ι → ℚ)
    (hx : (fun i ↦ algebraMap ℚ K (x i)) ∈
      finiteAffineCommonZeroLocus equations) :
    (fun i ↦ algebraMap ℚ K (x i)) ∈
      finiteAffineCommonZeroLocus equations ∩
        finiteAffineCommonZeroLocus (conjugateEquationFamily g equations) :=
  ⟨hx, rationalPoint_mem_conjugateFiniteAffineCommonZeroLocus
    g equations x hx⟩

/-! ## Actual projective conjugation -/

/-- Coordinatewise conjugation as a semilinear map over the underlying field
automorphism. -/
def conjugatePointSemilinearMap (g : K ≃ₐ[ℚ] K) :
    (ι → K) →ₛₗ[g.toRingHom] (ι → K) where
  toFun x := conjugatePoint g x
  map_add' x y := by
    funext i
    exact g.map_add (x i) (y i)
  map_smul' a x := by
    funext i
    exact g.map_mul a (x i)

theorem conjugatePointSemilinearMap_injective (g : K ≃ₐ[ℚ] K) :
    Function.Injective (conjugatePointSemilinearMap (ι := ι) g) := by
  intro x y hxy
  funext i
  apply g.injective
  exact congrFun hxy i

/-- The actual map on projective space induced by coordinatewise
conjugation. -/
def conjugateProjectivePoint (g : K ≃ₐ[ℚ] K) :
    Projectivization K (ι → K) → Projectivization K (ι → K) :=
  Projectivization.map (conjugatePointSemilinearMap (ι := ι) g)
    (conjugatePointSemilinearMap_injective g)

@[simp]
theorem conjugateProjectivePoint_mk (g : K ≃ₐ[ℚ] K)
    (x : ι → K) (hx : x ≠ 0) :
    conjugateProjectivePoint g (Projectivization.mk K x hx) =
      Projectivization.mk K (conjugatePoint g x)
        (by
          intro hzero
          apply hx
          funext i
          apply g.injective
          simpa [conjugatePoint] using congrFun hzero i) := by
  rfl

/-- Coefficientwise conjugation preserves the displayed homogeneous degree. -/
theorem conjugatePolynomial_isHomogeneous (g : K ≃ₐ[ℚ] K)
    {f : MvPolynomial ι K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (conjugatePolynomial g f).IsHomogeneous d := by
  exact hf.map g.toRingHom

/-- Projective conjugation carries a finite homogeneous common zero locus to
the projective common zero locus of the coefficientwise conjugate family. -/
theorem conjugateProjectivePoint_mem_finiteProjectiveCommonZeroLocus
    {σ : Type v} (g : K ≃ₐ[ℚ] K)
    (equations : Finset (MvPolynomial (Option σ) K))
    (degree : MvPolynomial (Option σ) K → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    {P : Projectivization K (Option σ → K)}
    (hP : P ∈ finiteProjectiveCommonZeroLocus equations) :
    conjugateProjectivePoint g P ∈
      finiteProjectiveCommonZeroLocus (conjugateEquationFamily g equations) := by
  classical
  induction P using Projectivization.ind with
  | h x hx =>
      rw [conjugateProjectivePoint_mk]
      intro f hf
      obtain ⟨f₀, hf₀, rfl⟩ :=
        (mem_conjugateEquationFamily_iff g equations f).mp hf
      rw [mk_mem_homogeneousProjectiveHypersurface_iff _ (degree f₀)
        (conjugatePolynomial_isHomogeneous g (hhom f₀ hf₀))]
      change MvPolynomial.eval (conjugatePoint g x)
        (conjugatePolynomial g f₀) = 0
      rw [eval_conjugatePolynomial]
      have hxzero : MvPolynomial.eval x f₀ = 0 := by
        exact (mk_mem_homogeneousProjectiveHypersurface_iff
          f₀ (degree f₀) (hhom f₀ hf₀) x hx).mp (hP f₀ hf₀)
      rw [hxzero, map_zero]

/-- An actual projective point represented by rational homogeneous
coordinates is fixed by every `ℚ`-algebra automorphism. -/
theorem conjugateProjectivePoint_mk_algebraMap
    (g : K ≃ₐ[ℚ] K) (x : ι → ℚ)
    (hx : (fun i ↦ algebraMap ℚ K (x i)) ≠ 0) :
    conjugateProjectivePoint g
        (Projectivization.mk K (fun i ↦ algebraMap ℚ K (x i)) hx) =
      Projectivization.mk K (fun i ↦ algebraMap ℚ K (x i)) hx := by
  rw [conjugateProjectivePoint_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simpa only [one_smul] using (conjugatePoint_algebraMap g x).symm

/-- A projective point with rational homogeneous coordinates which lies on
the original finite homogeneous locus lies on every conjugate locus. -/
theorem rationalProjectivePoint_mem_conjugateFiniteProjectiveCommonZeroLocus
    {σ : Type v} (g : K ≃ₐ[ℚ] K)
    (equations : Finset (MvPolynomial (Option σ) K))
    (degree : MvPolynomial (Option σ) K → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (x : Option σ → ℚ)
    (hx0 : (fun i ↦ algebraMap ℚ K (x i)) ≠ 0)
    (hx : Projectivization.mk K (fun i ↦ algebraMap ℚ K (x i)) hx0 ∈
      finiteProjectiveCommonZeroLocus equations) :
    Projectivization.mk K (fun i ↦ algebraMap ℚ K (x i)) hx0 ∈
      finiteProjectiveCommonZeroLocus (conjugateEquationFamily g equations) := by
  have hconj :=
    conjugateProjectivePoint_mem_finiteProjectiveCommonZeroLocus
      g equations degree hhom hx
  rwa [conjugateProjectivePoint_mk_algebraMap] at hconj

/-- Precise projective intersection consequence, again without assuming
that the conjugate locus is distinct from the original locus. -/
theorem rationalProjectivePoint_mem_finiteProjectiveCommonZeroLocus_inter_conjugate
    {σ : Type v} (g : K ≃ₐ[ℚ] K)
    (equations : Finset (MvPolynomial (Option σ) K))
    (degree : MvPolynomial (Option σ) K → ℕ)
    (hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (x : Option σ → ℚ)
    (hx0 : (fun i ↦ algebraMap ℚ K (x i)) ≠ 0)
    (hx : Projectivization.mk K (fun i ↦ algebraMap ℚ K (x i)) hx0 ∈
      finiteProjectiveCommonZeroLocus equations) :
    Projectivization.mk K (fun i ↦ algebraMap ℚ K (x i)) hx0 ∈
      finiteProjectiveCommonZeroLocus equations ∩
        finiteProjectiveCommonZeroLocus
          (conjugateEquationFamily g equations) :=
  ⟨hx, rationalProjectivePoint_mem_conjugateFiniteProjectiveCommonZeroLocus
    g equations degree hhom x hx0 hx⟩

end

end TranslatedDepthSeven
